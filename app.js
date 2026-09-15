(() => {
  "use strict";

  const $ = (s, root=document) => root.querySelector(s);
  const $$ = (s, root=document) => [...root.querySelectorAll(s)];


  const CONSTANTS = Object.freeze({
    NAME_LANG_BN:0x0445,
    NAME_LANG_EN:0x0409,
    HEAD_CHECKSUM_MAGIC:0xB1B0AFBA,
    GLYPHS_PER_PAGE:120,
    SEARCH_DEBOUNCE_MS:250,
    FONT_FAMILY:"UploadedFont"
  });

  const state = {
    file:null, buffer:null, font:null, format:"", sfnt:null,
    activeView:"overview", previewSize:54,
    metaOriginal:{}, fontURL:null, fontFace:null, axes:[],
    glyphPage:1, glyphItems:[],
    fontPreviewURL:null
  };

  const ids = {
    copyright:0, family:1, subfamily:2, fullName:4, version:5, postScript:6,
    trademark:7, manufacturer:8, designer:9, manufacturerURL:11,
    designerURL:12, license:13, licenseURL:14, sampleText:19
  };


  function toast(msg, type="ok"){
    const el=$("#toast"); el.textContent=msg; el.className="toast show "+type;
    clearTimeout(toast.t); toast.t=setTimeout(()=>el.className="toast",3500);
  }

  function esc(s){
    return String(s ?? "").replace(/[&<>"']/g, c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
  }

  const SFNTUtils = Object.freeze({
    u32:(d,o)=>d.getUint32(o,false),
    u16:(d,o)=>d.getUint16(o,false),
    tag:(d,o)=>String.fromCharCode(d.getUint8(o),d.getUint8(o+1),d.getUint8(o+2),d.getUint8(o+3)),
    align4:n=>(n+3)&~3,
    calcChecksum:bytes=>{
      const padded=bytes.byteLength%4 ? SFNTUtils.align4(bytes.byteLength) : bytes.byteLength;
      const tmp=padded===bytes.byteLength?bytes:new Uint8Array(padded);
      if(tmp!==bytes) tmp.set(bytes);
      const d=new DataView(tmp.buffer,tmp.byteOffset,tmp.byteLength);
      let sum=0;
      for(let i=0;i<tmp.byteLength;i+=4){
        sum=(sum + (d.getUint8(i)<<24>>>0) + (d.getUint8(i+1)<<16>>>0) + (d.getUint8(i+2)<<8>>>0) + d.getUint8(i+3))>>>0;
      }
      return sum>>>0;
    }
  });

  function parseSFNT(buffer){
    const d=new DataView(buffer);
    if(d.byteLength<12) throw new Error("File is too small to be a valid SFNT font.");
    const scaler=SFNTUtils.u32(d,0);
    const isSFNT=[0x00010000,0x4f54544f,0x74727565,0x74797031].includes(scaler);
    if(!isSFNT) return null;
    const n=SFNTUtils.u16(d,4), tables=[];
    if(12+n*16>d.byteLength) throw new Error("Invalid SFNT table directory.");
    for(let i=0;i<n;i++){
      const p=12+i*16, t=SFNTUtils.tag(d,p), checksum=SFNTUtils.u32(d,p+4), offset=SFNTUtils.u32(d,p+8), length=SFNTUtils.u32(d,p+12);
      if(offset+length>d.byteLength) throw new Error("Invalid table range: "+t);
      tables.push({tag:t,checksum,offset,length});
    }
    return {scaler,n,tables};
  }

  function decodeUTF16BE(bytes){
    let out="";
    for(let i=0;i+1<bytes.length;i+=2) out+=String.fromCharCode((bytes[i]<<8)|bytes[i+1]);
    return out.replace(/\u0000/g,"");
  }

  function readNameRecords(buffer, sfnt){
    const table=sfnt?.tables.find(t=>t.tag==="name");
    if(!table) return {};
    const d=new DataView(buffer,table.offset,table.length);
    const count=d.getUint16(2), stringOffset=d.getUint16(4), result={};
    const preference={};
    for(let i=0;i<count;i++){
      const p=6+i*12;
      const platform=d.getUint16(p), encoding=d.getUint16(p+2), language=d.getUint16(p+4), nameID=d.getUint16(p+6), length=d.getUint16(p+8), off=d.getUint16(p+10);
      if(platform!==3 || encoding!==1 || off+length>table.length-stringOffset) continue;
      const bytes=new Uint8Array(buffer,table.offset+stringOffset+off,length);
      const value=decodeUTF16BE(bytes);
      const score=(language===0x0445?3:language===0x0409?2:1);
      if(!preference[nameID] || score>preference[nameID].score) preference[nameID]={value,score};
    }
    Object.entries(ids).forEach(([key,id])=>result[key]=preference[id]?.value||"");
    return result;
  }

  function readVendor(buffer,sfnt){
    const t=sfnt?.tables.find(x=>x.tag==="OS/2");
    if(!t || t.length<62) return "";
    const bytes=new Uint8Array(buffer,t.offset+58,4);
    return String.fromCharCode(...bytes).replace(/[^\x20-\x7e]/g,"");
  }

  function parseFormat(buffer,file){
    const d=new DataView(buffer);
    const sig=d.byteLength>=4 ? String.fromCharCode(d.getUint8(0),d.getUint8(1),d.getUint8(2),d.getUint8(3)) : "";
    if(sig==="wOFF") return "WOFF";
    if(sig==="wOF2") return "WOFF2";
    if(sig==="OTTO") return "OTF";
    if(sig==="true" || sig==="typ1" || d.getUint32(0,false)===0x00010000) return file?.name?.toLowerCase().endsWith(".otf") ? "OTF" : "TTF";
    return file?.name?.split(".").pop()?.toUpperCase()||"UNKNOWN";
  }

  function makeParserSafeSFNT(buffer, sfnt){
    if(!sfnt) return buffer;
    // Some fonts contain layout-table variants that older opentype.js builds
    // cannot parse. The editor does not need those tables for preview/glyphs.
    const blocked=new Set(["GSUB","GPOS","GDEF","BASE","JSTF"]);
    const tables=sfnt.tables.filter(t=>!blocked.has(t.tag));
    const n=tables.length, dir=12+n*16;
    let cursor=SFNTUtils.align4(dir);
    const entries=[];
    for(const t of tables){ entries.push({tag:t.tag,bytes:new Uint8Array(buffer,t.offset,t.length),length:t.length,offset:cursor,checksum:t.checksum}); cursor+=SFNTUtils.align4(t.length); }
    const out=new Uint8Array(cursor);
    const d=new DataView(out.buffer);
    d.setUint32(0,sfnt.scaler,false); d.setUint16(4,n);
    let mp=1, es=0; while(mp*2<=n){mp*=2;es++;}
    d.setUint16(6,mp*16); d.setUint16(8,es); d.setUint16(10,n*16-mp*16);
    entries.sort((a,b)=>a.tag.localeCompare(b.tag));
    cursor=SFNTUtils.align4(dir);
    for(const e of entries){ e.offset=cursor; out.set(e.bytes,cursor); cursor+=SFNTUtils.align4(e.length); }
    entries.forEach((e,i)=>{
      const p=12+i*16; for(let k=0;k<4;k++) d.setUint8(p+k,e.tag.charCodeAt(k));
      d.setUint32(p+4,e.checksum>>>0); d.setUint32(p+8,e.offset>>>0); d.setUint32(p+12,e.length>>>0);
    });
    return out.buffer;
  }

  async function parseFont(buffer, file){
    try{ return opentype.parse(buffer); }
    catch(first){
      try{
        const safe=makeParserSafeSFNT(buffer,state.sfnt);
        return opentype.parse(safe);
      }catch(second){
        throw new Error("Could not parse font. The font may use an unsupported or malformed internal table.");
      }
    }
  }

  function showView(name){
    state.activeView=name;
    $$(".view").forEach(v=>v.classList.toggle("active",v.id===name));
    $$("#sideNav button,[data-view]").forEach(b=>b.classList.toggle("active",b.dataset.view===name));
    if(name==="overview") $("#welcome").style.display="none"; else $("#welcome").style.display="none";
    window.scrollTo({top:0,behavior:"smooth"});
  }

  function setEmpty(){
    $("#welcome").style.display="block";
    $$(".view").forEach(v=>v.classList.remove("active"));
  }

  function getOS2Info(buffer,sfnt){
    const t=sfnt?.tables?.find(x=>x.tag==="OS/2");
    if(!t || t.length<8) return {};
    const d=new DataView(buffer,t.offset,t.length);
    const out={version:SFNTUtils.u16(d,0)};
    if(t.length>=8) out.xAvgCharWidth=d.getInt16(2);
    if(t.length>=10) out.usWeightClass=SFNTUtils.u16(d,4);
    if(t.length>=12) out.usWidthClass=SFNTUtils.u16(d,6);
    if(t.length>=70) { out.fsType=SFNTUtils.u16(d,8); out.typoAscender=d.getInt16(68); }
    if(t.length>=72) out.typoDescender=d.getInt16(70);
    if(t.length>=74) out.typoLineGap=d.getInt16(72);
    if(t.length>=78) out.winAscent=SFNTUtils.u16(d,74);
    if(t.length>=80) out.winDescent=SFNTUtils.u16(d,76);
    return out;
  }

  function collectGlyphStats(f){
    let mapped=0, unencoded=0, unicodeCount=0;
    const cps=[];
    for(let i=0;i<(f?.glyphs?.length||0);i++){
      let g; try{g=f.glyphs.get(i)}catch(_){continue}
      const arr=Array.isArray(g?.unicodes)&&g.unicodes.length?g.unicodes:(g?.unicode!=null?[g.unicode]:[]);
      if(arr.length){mapped++; unicodeCount+=arr.length; for(const cp of arr) if(Number.isInteger(cp)) cps.push(cp)} else unencoded++;
    }
    cps.sort((a,b)=>a-b);
    const min=cps.length?cps[0]:null, max=cps.length?cps[cps.length-1]:null;
    return {mapped,unencoded,unicodeCount,min,max};
  }

  function renderOverview(){
    const f=state.font, meta=state.metaOriginal;
    if(!f) return;
    const os=getOS2Info(state.buffer,state.sfnt);
    const gs=collectGlyphStats(f);
    const family=meta.family || f.names?.fontFamily?.en || state.file.name;
    const style=meta.subfamily || f.names?.fontSubfamily?.en || "Regular";
    $("#fontTitle").textContent=family;
    $("#fontSub").textContent=style+" · "+state.file.name;
    $("#formatBadge").textContent=state.format;
    const glyphCount=f.glyphs?.length||0;
    $("#stats").innerHTML=[
      ["Glyphs",glyphCount],["Mapped glyphs",gs.mapped],["Unencoded glyphs",gs.unencoded],["File size",Math.ceil(state.buffer.byteLength/1024)+" KB"],
      ["Units / Em",f.unitsPerEm||"—"],["Ascender",f.ascender??"—"],["Descender",f.descender??"—"],["OS/2 weight",os.usWeightClass||"—"]
    ].map(x=>`<div class="card stat"><div class="label">${esc(x[0])}</div><div class="value">${esc(x[1])}</div></div>`).join("");
    const kv=[
      ["Family",family],["Style",style],["Full name",meta.fullName||f.names?.fullName?.en||"—"],["Version",meta.version||f.names?.version?.en||"—"],
      ["PostScript",meta.postScript||f.names?.postScriptName?.en||"—"],["Copyright",meta.copyright||f.names?.copyright?.en||"—"],["Vendor ID",readVendor(state.buffer,state.sfnt)||"—"]
    ];
    $("#identity").innerHTML=kv.map(([a,b])=>`<div class="kv"><b>${esc(a)}</b><div>${esc(b)}</div></div>`).join("");
    $("#layoutSummary").innerHTML=[
      ["Units per em",f.unitsPerEm||"—"],["Ascender",f.ascender??"—"],["Descender",f.descender??"—"],["Line gap",f.tables?.hhea?.lineGap??"—"],
      ["OS/2 weight class",os.usWeightClass||"—"],["OS/2 width class",os.usWidthClass||"—"],["Typo ascender",os.typoAscender??"—"],["Typo descender",os.typoDescender??"—"]
    ].map(([a,b])=>`<div class="kv"><b>${esc(a)}</b><div>${esc(b)}</div></div>`).join("");
    $("#coverageSummary").innerHTML=[
      ["Total glyphs",glyphCount],["Unicode-mapped glyphs",gs.mapped],["Unencoded glyphs",gs.unencoded],["Unicode records",gs.unicodeCount],
      ["Lowest mapped code point",gs.min?"U+"+gs.min.toString(16).toUpperCase():"—"],["Highest mapped code point",gs.max?"U+"+gs.max.toString(16).toUpperCase():"—"],
      ["Font file",state.file.name],["Format",state.format]
    ].map(([a,b])=>`<div class="kv"><b>${esc(a)}</b><div>${esc(b)}</div></div>`).join("");
    const sample=$("#overviewBanglaSample"); if(sample) sample.style.fontFamily='"UploadedFont",sans-serif';
  }

  const UNICODE_NAMES = {
    0x0980:"BENGALI ANJI",0x0981:"BENGALI SIGN CANDRABINDU",0x0982:"BENGALI SIGN ANUSVARA",0x0983:"BENGALI SIGN VISARGA",
    0x0985:"BENGALI LETTER A",0x0986:"BENGALI LETTER AA",0x0987:"BENGALI LETTER I",0x0988:"BENGALI LETTER II",0x0989:"BENGALI LETTER U",0x098A:"BENGALI LETTER UU",0x098B:"BENGALI LETTER VOCALIC R",0x098C:"BENGALI LETTER VOCALIC L",
    0x098F:"BENGALI LETTER E",0x0990:"BENGALI LETTER AI",0x0993:"BENGALI LETTER O",0x0994:"BENGALI LETTER AU",
    0x0995:"BENGALI LETTER KA",0x0996:"BENGALI LETTER KHA",0x0997:"BENGALI LETTER GA",0x0998:"BENGALI LETTER GHA",0x0999:"BENGALI LETTER NGA",
    0x099A:"BENGALI LETTER CA",0x099B:"BENGALI LETTER CHA",0x099C:"BENGALI LETTER JA",0x099D:"BENGALI LETTER JHA",0x099E:"BENGALI LETTER NYA",
    0x099F:"BENGALI LETTER TTA",0x09A0:"BENGALI LETTER TTHA",0x09A1:"BENGALI LETTER DDA",0x09A2:"BENGALI LETTER DDHA",0x09A3:"BENGALI LETTER NNA",
    0x09A4:"BENGALI LETTER TA",0x09A5:"BENGALI LETTER THA",0x09A6:"BENGALI LETTER DA",0x09A7:"BENGALI LETTER DHA",0x09A8:"BENGALI LETTER NA",
    0x09AA:"BENGALI LETTER PA",0x09AB:"BENGALI LETTER PHA",0x09AC:"BENGALI LETTER BA",0x09AD:"BENGALI LETTER BHA",0x09AE:"BENGALI LETTER MA",
    0x09AF:"BENGALI LETTER YA",0x09B0:"BENGALI LETTER RA",0x09B2:"BENGALI LETTER LA",0x09B6:"BENGALI LETTER SHA",0x09B7:"BENGALI LETTER SSA",0x09B8:"BENGALI LETTER SA",0x09B9:"BENGALI LETTER HA",
    0x09BC:"BENGALI SIGN NUKTA",0x09BE:"BENGALI VOWEL SIGN AA",0x09BF:"BENGALI VOWEL SIGN I",0x09C0:"BENGALI VOWEL SIGN II",0x09C1:"BENGALI VOWEL SIGN U",0x09C2:"BENGALI VOWEL SIGN UU",0x09C3:"BENGALI VOWEL SIGN VOCALIC R",0x09C4:"BENGALI VOWEL SIGN VOCALIC RR",
    0x09C7:"BENGALI VOWEL SIGN E",0x09C8:"BENGALI VOWEL SIGN AI",0x09CB:"BENGALI VOWEL SIGN O",0x09CC:"BENGALI VOWEL SIGN AU",0x09CD:"BENGALI SIGN VIRAMA",
    0x09CE:"BENGALI LETTER KHANDA TA",0x09D7:"BENGALI AU LENGTH MARK",0x09DC:"BENGALI LETTER RRA",0x09DD:"BENGALI LETTER RHA",0x09DF:"BENGALI LETTER YYA",
    0x09E0:"BENGALI LETTER VOCALIC RR",0x09E1:"BENGALI LETTER VOCALIC LL",0x09E2:"BENGALI VOWEL SIGN VOCALIC L",0x09E3:"BENGALI VOWEL SIGN VOCALIC LL",
    0x09E6:"BENGALI DIGIT ZERO",0x09E7:"BENGALI DIGIT ONE",0x09E8:"BENGALI DIGIT TWO",0x09E9:"BENGALI DIGIT THREE",0x09EA:"BENGALI DIGIT FOUR",0x09EB:"BENGALI DIGIT FIVE",0x09EC:"BENGALI DIGIT SIX",0x09ED:"BENGALI DIGIT SEVEN",0x09EE:"BENGALI DIGIT EIGHT",0x09EF:"BENGALI DIGIT NINE",
    0x09F0:"BENGALI LETTER RA WITH MIDDLE DIAGONAL",0x09F1:"BENGALI LETTER RA WITH LOWER DIAGONAL",0x09F2:"BENGALI RUPEE MARK",0x09F3:"BENGALI RUPEE SIGN",0x09F4:"BENGALI CURRENCY NUMERATOR ONE",0x09F5:"BENGALI CURRENCY NUMERATOR TWO",0x09F6:"BENGALI CURRENCY NUMERATOR THREE",0x09F7:"BENGALI CURRENCY NUMERATOR FOUR",0x09F8:"BENGALI CURRENCY NUMERATOR ONE LESS THAN THE DENOMINATOR",0x09F9:"BENGALI CURRENCY DENOMINATOR SIXTEEN",0x09FA:"BENGALI ISSHAR",0x09FB:"BENGALI GANDA MARK"
  };

  function unicodeName(cp){
    if(cp==null) return "UNENCODED GLYPH";
    if(UNICODE_NAMES[cp]) return UNICODE_NAMES[cp];
    if(cp>=0x41&&cp<=0x5A) return "LATIN CAPITAL LETTER "+String.fromCharCode(cp);
    if(cp>=0x61&&cp<=0x7A) return "LATIN SMALL LETTER "+String.fromCharCode(cp);
    if(cp>=0x30&&cp<=0x39) return "DIGIT "+String.fromCharCode(cp);
    const common={32:"SPACE",33:"EXCLAMATION MARK",34:"QUOTATION MARK",35:"NUMBER SIGN",36:"DOLLAR SIGN",37:"PERCENT SIGN",38:"AMPERSAND",39:"APOSTROPHE",40:"LEFT PARENTHESIS",41:"RIGHT PARENTHESIS",42:"ASTERISK",43:"PLUS SIGN",44:"COMMA",45:"HYPHEN-MINUS",46:"FULL STOP",47:"SOLIDUS",58:"COLON",59:"SEMICOLON",60:"LESS-THAN SIGN",61:"EQUALS SIGN",62:"GREATER-THAN SIGN",63:"QUESTION MARK",64:"COMMERCIAL AT",91:"LEFT SQUARE BRACKET",92:"REVERSE SOLIDUS",93:"RIGHT SQUARE BRACKET",95:"LOW LINE",123:"LEFT CURLY BRACKET",124:"VERTICAL LINE",125:"RIGHT CURLY BRACKET"};
    return common[cp] || "UNICODE CHARACTER";
  }

  function glyphSvg(g, size=62){
    try{
      const em=state.font?.unitsPerEm||1000;
      const path=g.getPath ? g.getPath(0,0,em) : null;
      const data=path?.toPathData ? path.toPathData(2) : "";
      if(!data) return `<div style="width:${size}px;height:${size}px;display:grid;place-items:center;color:#71809a;font-size:20px">·</div>`;
      let bb=null;
      try{ bb=path.getBoundingBox ? path.getBoundingBox() : null; }catch(_){ }
      if(!bb || !isFinite(bb.x1) || !isFinite(bb.x2) || !isFinite(bb.y1) || !isFinite(bb.y2)) bb={x1:0,y1:-em*.8,x2:em*.8,y2:em*.2};
      const pad=Math.max((bb.x2-bb.x1),(bb.y2-bb.y1),1)*.12;
      const x=bb.x1-pad, y=bb.y1-pad, w=Math.max(bb.x2-bb.x1+pad*2,1), h=Math.max(bb.y2-bb.y1+pad*2,1);
      return `<svg class="glyph-svg" viewBox="${x} ${y} ${w} ${h}" preserveAspectRatio="xMidYMid meet" aria-hidden="true"><path class="glyph-outline" d="${data}"/></svg>`;
    }catch(_){ return `<div style="width:${size}px;height:${size}px;display:grid;place-items:center;color:#71809a;font-size:20px">·</div>`; }
  }

  function buildGlyphItems(){
    const f=state.font;
    if(!f?.glyphs) return [];
    const q=(($(' #glyphSearch')?.value)||'').trim().toLowerCase();
    const items=[];
    for(let i=0;i<f.glyphs.length;i++){
      let g; try{g=f.glyphs.get(i)}catch(_){continue}
      if(!g) continue;
      const cps=Array.isArray(g.unicodes)&&g.unicodes.length?g.unicodes:(g.unicode!=null?[g.unicode]:[]);
      if(cps.length){
        for(const cp of cps){
          if(!Number.isInteger(cp)||cp<0||cp>0x10ffff) continue;
          let ch='·'; try{ch=String.fromCodePoint(cp)}catch(_){continue}
          const code='U+'+cp.toString(16).toUpperCase().padStart(4,'0');
          const uname=unicodeName(cp);
          const hay=(i+' '+ch+' '+code+' '+uname+' '+(g.name||'')).toLowerCase();
          if(q&&!hay.includes(q)) continue;
          items.push({i,g,cp,ch,code,uname});
        }
      }else{
        const uname=unicodeName(null), hay=(i+' '+(g.name||'')+' '+uname).toLowerCase();
        if(q&&!hay.includes(q)) continue;
        items.push({i,g,cp:null,ch:'◆',code:'—',uname});
      }
    }
    items.sort((a,b)=>a.cp==null?1:b.cp==null?-1:(a.cp-b.cp||a.i-b.i));
    return items;
  }

  function renderGlyphPage(){
    const grid=$('#glyphGrid'), empty=$('#glyphEmpty'), pager=$('#glyphPagination');
    if(!grid) return;
    const items=state.glyphItems;
    const totalPages=Math.max(1,Math.ceil(items.length/CONSTANTS.GLYPHS_PER_PAGE));
    state.glyphPage=Math.min(Math.max(1,state.glyphPage),totalPages);
    const start=(state.glyphPage-1)*CONSTANTS.GLYPHS_PER_PAGE;
    const pageItems=items.slice(start,start+CONSTANTS.GLYPHS_PER_PAGE);
    grid.innerHTML=pageItems.map(x=>`<button type="button" class="glyph ${x.cp==null?'unencoded':''}" data-gid="${x.i}" data-cp="${x.cp??''}" title="${esc(x.uname)} · GID ${x.i}" aria-label="${esc(x.cp!=null?x.ch:'Unencoded glyph')}, ${esc(x.uname)}, GID ${x.i}, ${esc(x.code)}">${glyphSvg(x.g)}<span class="char-label">${x.cp!=null?esc(x.ch):'◆'}</span><span class="glyph-name">${esc(x.uname)}</span><span class="glyph-code">GID ${x.i} · ${esc(x.code)}</span></button>`).join('');
    if(empty) empty.style.display=items.length?'none':'block';
    if(pager){
      pager.innerHTML=items.length>CONSTANTS.GLYPHS_PER_PAGE ? `<button type="button" class="btn small" data-page="prev" ${state.glyphPage===1?'disabled':''} aria-label="Previous glyph page">‹</button><span class="page-info">Page ${state.glyphPage} / ${totalPages} · ${items.length.toLocaleString()} glyph records</span><button type="button" class="btn small" data-page="next" ${state.glyphPage===totalPages?'disabled':''} aria-label="Next glyph page">›</button>` : '';
      pager.querySelector('[data-page="prev"]')?.addEventListener('click',()=>{state.glyphPage--;renderGlyphPage();window.scrollTo({top:0,behavior:'smooth'})});
      pager.querySelector('[data-page="next"]')?.addEventListener('click',()=>{state.glyphPage++;renderGlyphPage();window.scrollTo({top:0,behavior:'smooth'})});
    }
    $$('.glyph',grid).forEach(b=>b.addEventListener('click',()=>{const gid=+b.dataset.gid;const cp=b.dataset.cp===''?null:+b.dataset.cp;glyphDetail(gid,cp)}));
  }

  function renderGlyphs(){
    const grid=$('#glyphGrid');
    if(!grid) return;
    if(!state.font?.glyphs){
      grid.innerHTML='<div class="empty"><strong>No font loaded</strong>Load a font first.</div>';
      const pager=$('#glyphPagination'); if(pager) pager.innerHTML='';
      const empty=$('#glyphEmpty'); if(empty) empty.style.display='none';
      return;
    }
    state.glyphItems=buildGlyphItems();
    state.glyphPage=1;
    renderGlyphPage();
  }

  function glyphDetail(gid,cp){
    const g=state.font.glyphs.get(gid);
    const bb=g.getBoundingBox ? g.getBoundingBox() : {};
    const adv=g.advanceWidth ?? "—";
    const modal=document.createElement("div");
    const char=cp!=null?String.fromCodePoint(cp):"Unencoded glyph";
    modal.style.cssText="position:fixed;inset:0;background:rgba(0,0,0,.72);z-index:100;display:grid;place-items:center;padding:18px";
    modal.innerHTML=`<div class="card" style="width:min(620px,100%);max-height:90vh;overflow:auto">
      <div class="card-head"><h3>Glyph ${gid}</h3><button class="btn small" id="closeGlyph">Close</button></div>
      <div class="card-body">
        <div style="display:grid;place-items:center;min-height:220px;padding:20px;background:#0b111d;border-radius:14px">${glyphSvg(g,180)}</div>
        <div class="kv"><b>Character</b><div>${esc(char)}</div></div>
        <div class="kv"><b>Unicode name</b><div>${esc(unicodeName(cp))}</div></div>
        <div class="kv"><b>Code point</b><div class="mono">${cp!=null?"U+"+cp.toString(16).toUpperCase():"No Unicode mapping"}</div></div>
        <div class="kv"><b>Glyph name</b><div>${esc(g.name||"—")}</div></div>
        <div class="kv"><b>Advance width</b><div>${esc(adv)}</div></div>
        <div class="kv"><b>Bounding box</b><div>${esc(JSON.stringify(bb))}</div></div>
      </div></div>`;
    document.body.appendChild(modal); $("#closeGlyph",modal).onclick=()=>modal.remove(); modal.onclick=e=>{if(e.target===modal)modal.remove()};
  }

  function renderMetadata(){
    const m=state.metaOriginal||{};
    $$('[data-meta]').forEach(i=>{ if(i) i.value=m[i.dataset.meta]||""; });
    const vendorInput=$("#vendorId"), notice=$("#editNotice");
    if(vendorInput) vendorInput.value=readVendor(state.buffer,state.sfnt)||"";
    if(notice){
      const editable=state.format==="TTF"||state.format==="OTF";
      notice.textContent=editable ? "TTF/OTF metadata editing is enabled. Other font data is preserved." : "This font is read-only for metadata export. Use TTF/OTF for editing.";
      notice.className="notice "+(editable?"ok":"warn");
    }
  }

  function applyPreviewStyle(){
    const el=$("#previewText");
    if(!el) return;
    const range=$("#sizeRange");
    const label=$("#sizeLabel");
    const weight=$("#weightSelect");
    const size=range ? (+range.value || state.previewSize || 54) : (state.previewSize || 54);
    const wt=weight ? (weight.value || "400") : "400";
    el.style.fontSize=size+"px";
    el.style.fontWeight=wt;
    el.style.fontFamily='UploadedFont, sans-serif';
    if(label) label.textContent=size+"px";
  }

  function renderAxes(){
    const box=$("#axisBox");
    if(!box) return;
    const axes=state.font?.tables?.fvar?.axes || [];
    state.axes=axes;
    if(!axes.length){box.innerHTML=`<div class="empty"><strong>No fvar axes detected</strong>This is normal for a static font. Variable fonts expose axes such as wght, wdth or opsz here.</div>`;return}
    box.innerHTML=axes.map((a,i)=>`<div class="axis"><b class="mono">${esc(a.tag)}</b><input type="range" min="${a.minValue}" max="${a.maxValue}" step="${(a.maxValue-a.minValue)/100||1}" value="${a.defaultValue}" data-axis="${i}"><output>${a.defaultValue}</output></div>`).join("");
    $$(".axis input",box).forEach(inp=>inp.addEventListener("input",()=>{
      const a=axes[+inp.dataset.axis]; inp.nextElementSibling.value=inp.value;
      $("#previewText").style.fontVariationSettings=`"${a.tag}" ${inp.value}`;
    }));
  }

  

  function renderAll(){
    try{renderOverview()}catch(e){console.warn("Overview render:",e)}
    try{renderGlyphs()}catch(e){console.warn("Glyph render:",e)}
    try{renderMetadata()}catch(e){console.warn("Metadata render:",e)}
    try{renderAxes()}catch(e){console.warn("Axes render:",e)}
    try{applyPreviewStyle()}catch(e){console.warn("Preview render:",e)}
  }

  // Build a metadata-safe name table by starting from the ORIGINAL name
  // records.  Only the Windows Unicode records for the selected language and
  // the Name IDs exposed by the editor are changed.  Every other name record
  // (including Name IDs 3 and 10) is preserved.
  function readRawNameRecords(buffer, sfnt){
    const table=sfnt?.tables?.find(t=>t.tag==="name");
    if(!table || table.length<6) return null;
    const d=new DataView(buffer,table.offset,table.length);
    const format=d.getUint16(0), count=d.getUint16(2), storageOffset=d.getUint16(4);
    if(storageOffset>table.length || 6+count*12>table.length) return null;

    const records=[];
    for(let i=0;i<count;i++){
      const p=6+i*12;
      const platformID=d.getUint16(p), encodingID=d.getUint16(p+2), languageID=d.getUint16(p+4);
      const nameID=d.getUint16(p+6), length=d.getUint16(p+8), offset=d.getUint16(p+10);
      const start=storageOffset+offset, end=start+length;
      if(end>table.length) continue;
      records.push({platformID,encodingID,languageID,nameID,bytes:new Uint8Array(buffer,table.offset+start,length).slice()});
    }
    return {format,records};
  }

  function encodeUTF16BE(value){
    const str=String(value??"");
    const units=[];
    for(let i=0;i<str.length;i++){
      const c=str.charCodeAt(i);
      units.push((c>>8)&255,c&255);
    }
    return new Uint8Array(units);
  }

  function makeNameTable(meta, lang, original){
    const parsed=original || {format:0,records:[]};
    const languageID=lang==="en" ? CONSTANTS.NAME_LANG_EN : CONSTANTS.NAME_LANG_BN;
    const editedById=new Map();
    Object.entries(ids).forEach(([key,id])=>{
      let value=String(meta[key]??"");
      if(id===6) value=value.replace(/[^A-Za-z0-9_.-]/g,"-").slice(0,63);
      editedById.set(id,value);
    });

    const records=parsed.records.map(r=>({
      platformID:r.platformID, encodingID:r.encodingID, languageID:r.languageID,
      nameID:r.nameID, bytes:r.bytes.slice(), _edited:false
    }));

    // Update only the editor's metadata IDs in Windows Unicode records for
    // the selected language. Other platforms/languages remain untouched.
    for(const [nameID,value] of editedById){
      const matches=records.filter(r=>
        r.platformID===3 && (r.encodingID===1 || r.encodingID===10) &&
        r.languageID===languageID && r.nameID===nameID
      );
      if(matches.length){
        if(value){
          const bytes=encodeUTF16BE(value);
          matches.forEach(r=>{r.bytes=bytes.slice();r._edited=true});
        }else{
          for(let i=records.length-1;i>=0;i--){
            const r=records[i];
            if(r.platformID===3 && (r.encodingID===1 || r.encodingID===10) && r.languageID===languageID && r.nameID===nameID) records.splice(i,1);
          }
        }
      }else if(value){
        // The selected language may not exist in the original font. Add one
        // Windows Unicode record without disturbing existing records.
        records.push({platformID:3,encodingID:1,languageID,nameID,bytes:encodeUTF16BE(value),_edited:true});
      }
    }

    // Keep name-table version 0/1 where possible. For v1 we preserve the
    // existing header's language-tag records by rebuilding only the name
    // records/storage area; uncommon malformed v1 tables safely fall back to v0.
    const format=(parsed.format===0 || parsed.format===1) ? parsed.format : 0;
    const recordBytes=records.map(r=>r.bytes);
    const recordCount=records.length;

    if(format===1){
      // Read and preserve v1 language-tag records and their storage bytes.
      const table=state.sfnt?.tables?.find(t=>t.tag==="name");
      const d=new DataView(state.buffer,table.offset,table.length);
      const base=6+recordCount*12;
      const oldCount=d.getUint16(6);
      const oldTagBytes=oldCount*4;
      const oldTagStart=10;
      const oldStorageOffset=d.getUint16(4);
      if(oldTagStart+oldTagBytes<=oldStorageOffset && oldStorageOffset<=table.length){
        const tagRecords=new Uint8Array(state.buffer,table.offset+oldTagStart,oldTagBytes).slice();
        const oldStorage=new Uint8Array(state.buffer,table.offset+oldStorageOffset,table.length-oldStorageOffset).slice();
        const header=10+oldTagBytes;
        let storageSize=0; for(const b of recordBytes) storageSize+=b.length;
        const total=header+storageSize+oldStorage.length;
        if(total<=0xFFFF){
          const out=new Uint8Array(total), od=new DataView(out.buffer);
          od.setUint16(0,1); od.setUint16(2,recordCount); od.setUint16(4,header+storageSize); od.setUint16(6,oldCount);
          out.set(tagRecords,10);
          let pos=header+storageSize; out.set(oldStorage,pos);
          let strOff=0;
          records.forEach((r,i)=>{
            const p=10+oldTagBytes+i*12;
            od.setUint16(p,r.platformID); od.setUint16(p+2,r.encodingID); od.setUint16(p+4,r.languageID);
            od.setUint16(p+6,r.nameID); od.setUint16(p+8,r.bytes.length); od.setUint16(p+10,strOff); strOff+=r.bytes.length;
          });
          pos=header; for(const b of recordBytes){out.set(b,pos);pos+=b.length;}
          return out;
        }
      }
    }

    let storageSize=0; for(const b of recordBytes) storageSize+=b.length;
    const header=6+recordCount*12;
    if(header+storageSize>0xFFFF) throw new Error("Font metadata is too large for the OpenType name table.");
    const out=new Uint8Array(header+storageSize), d=new DataView(out.buffer);
    d.setUint16(0,0); d.setUint16(2,recordCount); d.setUint16(4,header);
    let strOff=0, pos=header;
    records.forEach((r,i)=>{
      const p=6+i*12;
      d.setUint16(p,r.platformID); d.setUint16(p+2,r.encodingID); d.setUint16(p+4,r.languageID);
      d.setUint16(p+6,r.nameID); d.setUint16(p+8,r.bytes.length); d.setUint16(p+10,strOff);
      out.set(r.bytes,pos); pos+=r.bytes.length; strOff+=r.bytes.length;
    });
    return out;
  }

  function buildEditedSFNT(){
    if(!state.sfnt || !["TTF","OTF"].includes(state.format)) throw new Error("Metadata export supports TTF and OTF only.");
    const d=new DataView(state.buffer);
    const meta={}; $$('[data-meta]').forEach(i=>meta[i.dataset.meta]=i.value.trim());
    const vendor=( $("#vendorId")?.value || "" ).trim();
    if(vendor && !/^[\x20-\x7E]{4}$/.test(vendor)) throw new Error("Vendor ID must be exactly 4 printable ASCII characters.");
    const lang=$("#metaLang")?.value||"bn";

    const originalName=readRawNameRecords(state.buffer,state.sfnt);
    if(!originalName) throw new Error("The font does not contain a readable name table.");
    const nameBytes=makeNameTable(meta,lang,originalName);

    // Preserve every source table byte-for-byte except the tables that the
    // user explicitly edits. A signed DSIG cannot remain valid after any
    // metadata change, so remove it rather than leaving a stale signature.
    const tables=[];
    for(const t of state.sfnt.tables){
      if(t.tag==="DSIG") continue;
      if(t.tag==="name") tables.push({tag:t.tag,bytes:nameBytes});
      else tables.push({tag:t.tag,bytes:new Uint8Array(state.buffer,t.offset,t.length).slice()});
    }

    if(vendor){
      const os=tables.find(t=>t.tag==="OS/2");
      if(os && os.bytes.length>=62) os.bytes.set(new TextEncoder().encode(vendor),58);
    }

    // Repack the SFNT directory without touching the contents of GSUB/GPOS/
    // GDEF/glyf/cmap/etc. Offsets may move, but table bytes remain identical.
    const n=tables.length, dirSize=12+n*16;
    let cursor=SFNTUtils.align4(dirSize);
    const entries=[];
    for(const t of tables){
      entries.push({tag:t.tag,bytes:t.bytes,offset:cursor,length:t.bytes.length,checksum:0});
      cursor+=SFNTUtils.align4(t.bytes.length);
    }

    const out=new Uint8Array(cursor), od=new DataView(out.buffer);
    const scaler=d.getUint32(0,false);
    od.setUint32(0,scaler,false); od.setUint16(4,n);
    let maxPower=1,entrySelector=0; while(maxPower*2<=n){maxPower*=2;entrySelector++;}
    od.setUint16(6,maxPower*16); od.setUint16(8,entrySelector); od.setUint16(10,n*16-maxPower*16);

    entries.sort((a,b)=>a.tag.localeCompare(b.tag));
    cursor=SFNTUtils.align4(dirSize);
    for(const e of entries){e.offset=cursor;out.set(e.bytes,cursor);cursor+=SFNTUtils.align4(e.length);}

    entries.forEach((e,i)=>{
      const padded=SFNTUtils.align4(e.length);
      const tmp=new Uint8Array(padded); tmp.set(e.bytes);
      if(e.tag==="head" && e.length>=12) new DataView(tmp.buffer).setUint32(8,0,false);
      e.checksum=SFNTUtils.calcChecksum(tmp);
      const p=12+i*16;
      for(let k=0;k<4;k++) od.setUint8(p+k,e.tag.charCodeAt(k));
      od.setUint32(p+4,e.checksum>>>0); od.setUint32(p+8,e.offset>>>0); od.setUint32(p+12,e.length>>>0);
    });

    const head=entries.find(e=>e.tag==="head");
    if(head && head.length>=12){
      const hd=new DataView(out.buffer,head.offset,head.length);
      hd.setUint32(8,0,false);
      const sum=SFNTUtils.calcChecksum(out);
      hd.setUint32(8,(CONSTANTS.HEAD_CHECKSUM_MAGIC-sum)>>>0,false);
    }
    return out.buffer;
  }

  async function downloadBuffer(buffer, filename){
    const blob=new Blob([buffer],{type:"font/ttf"});
    if("showSaveFilePicker" in window){
      try{
        const h=await window.showSaveFilePicker({suggestedName:filename,types:[{description:"Font",accept:{"font/ttf":[".ttf",".otf"]}}]});
        const w=await h.createWritable(); await w.write(blob); await w.close(); toast("Font saved successfully.","ok"); return;
      }catch(e){ if(e.name==="AbortError") return; }
    }
    const url=URL.createObjectURL(blob), a=document.createElement("a"); a.href=url;a.download=filename;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
    toast("Download started.","ok");
  }

  async function saveFont(){
    try{
      if(!state.file){toast("Load a font first.","error");return}
      const out=buildEditedSFNT();
      const base=state.file.name.replace(/\.(ttf|otf|woff2?|TTF|OTF|WOFF2?)$/i,"");
      const ext=state.format==="OTF"?"otf":"ttf";
      await downloadBuffer(out,base+"_edited."+ext);
    }catch(e){toast(e.message||"Could not save font.","error")}
  }

  function cleanupFontResources(){
    if(state.fontFace){ try{document.fonts.delete(state.fontFace)}catch(_){ } state.fontFace=null; }
    if(state.fontURL){ try{URL.revokeObjectURL(state.fontURL)}catch(_){ } state.fontURL=null; }
    if(state.fontPreviewURL){ try{URL.revokeObjectURL(state.fontPreviewURL)}catch(_){ } state.fontPreviewURL=null; }
  }

  async function load(file){
    if(!file)return;
    try{
      const buffer=await file.arrayBuffer();
      state.file=file; state.buffer=buffer; state.format=parseFormat(buffer,file); state.sfnt=parseSFNT(buffer);
      state.font=await parseFont(buffer,file);
      state.metaOriginal=readNameRecords(buffer,state.sfnt);
      cleanupFontResources();
      try{
        state.fontURL=URL.createObjectURL(new Blob([buffer],{type:file.type||'font/ttf'}));
        state.fontFace=new FontFace(CONSTANTS.FONT_FAMILY,`url(${state.fontURL})`);
        await state.fontFace.load();
        document.fonts.add(state.fontFace);
      }catch(e){
        cleanupFontResources();
        console.warn('FontFace load:',e);
      }
      $("#welcome").style.display="none";
      showView("overview");
      renderAll();
      toast(file.name+" loaded successfully.","ok");
    }catch(e){
      console.error(e); toast(e.message||"Could not read font.","error");
      setEmpty();
    }
  }

  function reset(){
    state.file=null;state.buffer=null;state.font=null;state.sfnt=null;state.format="";state.metaOriginal={};
    cleanupFontResources();
    state.glyphItems=[]; state.glyphPage=1;
    $("#fontTitle").textContent="No font loaded";$("#fontSub").textContent="Load a font to begin.";
    setEmpty(); toast("Inspector reset.","ok");
  }


  function debounce(fn, delay=CONSTANTS.SEARCH_DEBOUNCE_MS){
    let timer=0;
    return (...args)=>{
      clearTimeout(timer);
      timer=setTimeout(()=>fn(...args),delay);
    };
  }
  // Navigation
  $$("#sideNav button,[data-view]").forEach(b=>b.addEventListener("click",()=>{
    const v=b.dataset.view; if(!v)return;
    showView(v);
  }));
  const mobile=$("#mobileNav");
  const navButtons=$$("#sideNav button[data-view]");
  if(mobile){
    mobile.innerHTML=navButtons.map(b=>`<button type="button" data-view="${b.dataset.view}" aria-label="Open ${esc(b.textContent.trim())} section">${esc(b.textContent.trim())}</button>`).join("");
    $$("#mobileNav button").forEach(b=>b.addEventListener("click",()=>showView(b.dataset.view)));
  }

  const chooseBtn=$("#chooseBtn"), fileInput=$("#fileInput");
  if(chooseBtn && fileInput) chooseBtn.onclick=()=>fileInput.click();
  if(fileInput) fileInput.onchange=e=>load(e.target.files?.[0]);
  const dz=$("#dropzone");
  ["dragenter","dragover"].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.add("drag")}));
  ["dragleave","drop"].forEach(ev=>dz.addEventListener(ev,e=>{e.preventDefault();dz.classList.remove("drag")}));
  dz.addEventListener("drop",e=>load(e.dataTransfer.files[0]));

  const saveBtn=$("#saveBtn"), saveMetaBtn=$("#saveMetaBtn"), resetBtn=$("#resetBtn"), reloadMetaBtn=$("#reloadMetaBtn");
  if(saveBtn) saveBtn.onclick=saveFont;
  if(saveMetaBtn) saveMetaBtn.onclick=saveFont;
  if(resetBtn) resetBtn.onclick=reset;
  if(reloadMetaBtn) reloadMetaBtn.onclick=()=>{if(state.file){renderMetadata();toast("Original metadata restored in the form.","ok")}};
  const sizeRange=$("#sizeRange"), sizeLabel=$("#sizeLabel"), sizeDown=$("#sizeDown"), sizeUp=$("#sizeUp"), weightSelect=$("#weightSelect"), glyphSearch=$("#glyphSearch");
  if(sizeRange) sizeRange.oninput=e=>{state.previewSize=+e.target.value; if(sizeLabel) sizeLabel.textContent=state.previewSize+"px"; applyPreviewStyle()};
  if(sizeDown && sizeRange) sizeDown.onclick=()=>{sizeRange.value=Math.max(12,state.previewSize-4);sizeRange.dispatchEvent(new Event("input"))};
  if(sizeUp && sizeRange) sizeUp.onclick=()=>{sizeRange.value=Math.min(180,state.previewSize+4);sizeRange.dispatchEvent(new Event("input"))};
  if(weightSelect) weightSelect.onchange=applyPreviewStyle;
  if(glyphSearch) glyphSearch.oninput=debounce(renderGlyphs,CONSTANTS.SEARCH_DEBOUNCE_MS);

  setEmpty();
})();
