import { test, before, after } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer, type ViewerServer } from "./viewer-server.ts";

let browser: CdpBrowser;
let server: ViewerServer;
before(async () => {
  server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  browser = await CdpBrowser.launch();
});
after(async () => {
  await browser?.close();
  await server?.stop();
});

test("small PDF references remain focusable overlays at their original positions", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=Hyperfinite.measurableSet`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 45000 });
  await tab.waitFor("document.querySelector('#pdf-viewer .pdf-page > a.pdf-link-box')", { timeout: 30000 });
  const result = await tab.evaluate<{ count: number; positioned: boolean; text: string; menus: number }>(`(() => {
    const page = [...document.querySelectorAll('#pdf-viewer .pdf-page')].find(p => p.querySelector('a.pdf-link-box'));
    page.id='overlay-test-page';
    const rect = page.getBoundingClientRect();
    const links = [...page.querySelectorAll(':scope > a.pdf-link-box')];
    links[0].id='keyboard-overlay-link';
    return {count:links.length, text:page.querySelector('.pdf-text-layer').textContent,
      menus:document.querySelectorAll('.pdf-extra-links').length,
      positioned:links.every(a=>{
        const r=a.getBoundingClientRect();
        return getComputedStyle(a).position==='absolute' && r.width>=24 && r.height>=24 &&
          Math.abs(r.left+12-rect.left-rect.width*parseFloat(a.style.left)/100)<1 &&
          Math.abs(r.top+12-rect.top-rect.height*parseFloat(a.style.top)/100)<1;
      })};
  })()`);
  assert.ok(result.count > 0);
  assert.ok(result.text.length > 100, "the selectable PDF text layer is preserved");
  assert.equal(result.positioned, true, "links must overlay their printed references");
  assert.equal(result.menus, 0, "small references must not move into a separate page menu");
  await tab.evaluate("document.querySelector('#keyboard-overlay-link').focus({preventScroll:true})");
  assert.equal(await tab.evaluate("document.activeElement.id"), "keyboard-overlay-link");
  const before = await tab.evaluate<number>(
    "document.querySelector('#overlay-test-page').getBoundingClientRect().height",
  );
  await tab.setViewport(390, 844, 2);
  await tab.evaluate("import('./build/pdf.js').then(pdf=>pdf.schedulePdfRepaint())");
  await tab.waitFor(`(async () => {
    const {state}=await import('./build/state.js');
    return !state.pdf.repaintTimer && [...state.pdf.pageStates.values()].every(page=>!page.rendering);
  })()`);
  const after = await tab.evaluate<number>(
    "document.querySelector('#overlay-test-page').getBoundingClientRect().height",
  );
  assert.ok(Math.abs(after - before) < 0.1, "device-pixel rounding must not shift page geometry during repaint");
  assert.equal(
    await tab.evaluate("document.querySelector('#keyboard-overlay-link')?.parentElement.id"),
    "overlay-test-page",
  );
});

test("overlay geometry scales with the page and selecting text prevents navigation", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  const result = await tab.evaluate<{
    scales: boolean[];
    selected: boolean;
    follows: number;
    external: string;
  }>(`(async () => {
    const stylesheet=document.createElement('link');stylesheet.rel='stylesheet';stylesheet.href='./styles.css';
    const loaded=new Promise((resolve,reject)=>{stylesheet.onload=resolve;stylesheet.onerror=reject;});
    document.head.append(stylesheet);await loaded;
    const {appendPageLinks}=await import('./build/pdf-document.js');
    const page=document.createElement('div');
    page.className='pdf-page';page.style.cssText='position:fixed;left:0;top:100px;width:400px;height:200px';
    const text=document.createTextNode('Selectable text');page.append(text);document.body.append(page);
    let follows=0;
    appendPageLinks(page,[
      {subtype:'Link',rect:[20,20,40,40],dest:'section.1'},
      {subtype:'Link',rect:[60,20,80,40],url:'https://example.com/'},
      {subtype:'Link',rect:[0,0,10,10],url:'javascript:void(0)'},
    ],{width:100,height:100,convertToViewportPoint:(x,y)=>[x,100-y]},null,async()=>{follows++;});
    const links=[...page.querySelectorAll('a')];
    const a=links[0];
    const scales=[400,600].map(width=>{
      page.style.width=width+'px';page.style.height=width/2+'px';
      const p=page.getBoundingClientRect(),r=a.getBoundingClientRect();
      return Math.abs(r.left+12-p.left-width*.2)<1 && Math.abs(r.top+12-p.top-width/2*.6)<1 &&
        Math.abs(r.width-24-width*.2)<1 && Math.abs(r.height-24-width/2*.2)<1;
    });
    const selection=getSelection(),range=document.createRange();range.selectNodeContents(text);
    selection.removeAllRanges();selection.addRange(range);a.click();
    const selected=selection.toString()==='Selectable text' && follows===0;
    selection.removeAllRanges();a.click();
    return {scales,selected,follows,external:links.length===2 ? links[1].href : 'invalid annotations accepted'};
  })()`);
  assert.deepEqual(result.scales, [true, true]);
  assert.equal(result.selected, true);
  assert.equal(result.follows, 1);
  assert.equal(result.external, "https://example.com/");
});

test("CSS touch extensions preserve printed-link priority and use native clicks", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(`(async () => {
    const stylesheet=document.createElement('link');stylesheet.rel='stylesheet';stylesheet.href='./styles.css';
    const loaded=new Promise((resolve,reject)=>{stylesheet.onload=resolve;stylesheet.onerror=reject;});
    document.head.append(stylesheet);await loaded;
    const {setProject}=await import('./build/state.js');setProject(await fetch('./manifest.json').then(r=>r.json()));
    const {appendPageLinks}=await import('./build/pdf-document.js');
    document.body.replaceChildren();
    const page=document.createElement('div');page.className='pdf-page';
    page.style.cssText='position:fixed;left:100px;top:200px;width:100px;height:100px;z-index:100';
    page.innerHTML='<div class="pdf-text-host"><div class="pdf-text-layer" style="width:100%;height:100%"><span style="inset:0;font-size:12px;transform:none">Selectable text</span></div></div>';
    for (const [name,x] of [['first',12],['first-core',21],['second',34],['term',56],['far',90]]) {
      const probe=document.createElement('span');probe.id='near-'+name;
      probe.style.cssText='position:absolute;pointer-events:none;left:'+x+'px;top:78px;width:1px;height:1px';
      page.append(probe);
    }
    document.body.append(page);window.overlayFollows=[];window.nativeOverlayClicks=[];
    page.addEventListener('click',e=>{if(e.target.closest('a.pdf-link-box')) window.nativeOverlayClicks.push(e.isTrusted);},true);
    appendPageLinks(page,[
      {subtype:'Link',rect:[20,20,24,24],dest:'overlay-first-test'},
      {subtype:'Link',rect:[26,20,30,24],dest:'overlay-second-test'},
      {subtype:'Link',rect:[60,20,64,24],dest:'term-index-indicator-function'},
    ],{width:100,height:100,convertToViewportPoint:(x,y)=>[x,100-y]},null,
      async dest=>{window.overlayFollows.push(dest);},
      {current:()=>true,document:async()=>({getDestination:async()=>[0]})});
  })()`);
  await tab.tap("#near-first");
  await tab.waitFor("window.overlayFollows[0]==='overlay-first-test'");
  const sizes = await tab.evaluate<{
    width: number;
    height: number;
    core: number;
    nearbyHit: string;
    printedHit: string;
  }>(`(() => {
    const a=document.querySelector('a.pdf-link-box');const hit=getComputedStyle(a,'::before');
    return {width:parseFloat(hit.width),height:parseFloat(hit.height),core:parseFloat(getComputedStyle(a,'::after').width),
      nearbyHit:document.elementFromPoint(112.5,278.5)?.closest('a')?.dataset.definition,
      printedHit:document.elementFromPoint(121.5,278.5)?.closest('a')?.dataset.definition};
  })()`);
  assert.ok(sizes.width >= 24 && sizes.height >= 24);
  assert.equal(sizes.core, 4, "the visual overlay must remain aligned with the original PDF annotation");
  assert.equal(
    sizes.nearbyHit,
    "overlay-first-test",
    "CSS hit testing must include the expanded area above the text layer",
  );
  assert.equal(sizes.printedHit, "overlay-first-test", "another link extension must not obscure the printed core");
  await tab.tap("#near-first-core");
  await tab.waitFor("window.overlayFollows[1]==='overlay-first-test'");
  await tab.tap("#near-second");
  await tab.waitFor("window.overlayFollows[2]==='overlay-second-test'");
  await tab.tap("#near-far");
  assert.equal(await tab.evaluate("window.overlayFollows.length"), 3);
  await tab.tap("#near-term");
  await tab.waitFor("document.querySelector('.term-definition-preview[role=dialog] .term-preview-source')");
  assert.equal(await tab.evaluate("window.overlayFollows.length"), 3, "term taps must preview rather than navigate");
  assert.equal(
    await tab.evaluate("window.nativeOverlayClicks.every(Boolean)"),
    true,
    "no synthetic click forwarding is needed",
  );
  await tab.pressKey("Escape");
  await tab.waitFor("!document.querySelector('#term-link-popup')");
});
