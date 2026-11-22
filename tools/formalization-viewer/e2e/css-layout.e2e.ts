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

const LOAD_CSS = `(() => {
  const link=document.createElement('link');link.rel='stylesheet';link.href='./styles.css';
  const loaded=new Promise((resolve,reject)=>{link.onload=resolve;link.onerror=reject;});
  document.head.append(link);return loaded;
})()`;

test("CSS pickers fit the viewport and follow their fields without JavaScript geometry measurements", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(LOAD_CSS);
  await tab.evaluate(`(async () => {
    const {enhanceSelect}=await import('./build/select-dropdown.js');
    const host=document.createElement('div');host.style.cssText='position:fixed;right:10px;bottom:10px;width:120px';
    const select=document.createElement('select');select.setAttribute('aria-label','CSS picker');
    select.innerHTML=Array.from({length:40},(_,i)=>'<option>Document '+i+'</option>').join('');
    host.append(select);document.body.append(host);enhanceSelect(select);
    window.cssField=host.querySelector('button');window.cssPopover=host.querySelector('[popover]');
    for(const element of [window.cssField,window.cssPopover]) element.getBoundingClientRect=()=>{throw new Error('JavaScript must not measure picker geometry');};
    window.cssField.click();
  })()`);
  const bounds = () =>
    tab.evaluate<{
      left: number;
      top: number;
      right: number;
      bottom: number;
      above: boolean;
      inline: boolean;
    }>(`(() => {
    const rect=Element.prototype.getBoundingClientRect;
    const p=rect.call(window.cssPopover),f=rect.call(window.cssField);
    return {left:p.left,top:p.top,right:p.right,bottom:p.bottom,above:p.bottom<=f.top,
      inline:!!(window.cssPopover.style.left || window.cssPopover.style.top || window.cssPopover.style.width)};
  })()`);
  await tab.waitFor("window.cssPopover.matches(':popover-open')");
  for (const [width, height] of [
    [390, 844],
    [280, 640],
  ]) {
    await tab.setViewport(width, height);
    await tab.evaluate("new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))");
    const rect = await bounds();
    assert.ok(rect.left >= 0 && rect.top >= 0 && rect.right <= width && rect.bottom <= height, JSON.stringify(rect));
    assert.equal(rect.above, true, "a picker near the bottom must flip above its field");
    assert.equal(rect.inline, false, "position and size must be determined by CSS");
  }
});

test("CSS context menus fit both pointer and keyboard invocations", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(LOAD_CSS);
  await tab.evaluate(`(async () => {
    const {setProject}=await import('./build/state.js');setProject(await fetch('./manifest.json').then(r=>r.json()));
    const {attachTermLink}=await import('./build/term-preview.js');
    const a=document.createElement('a');a.href='#';a.textContent='indicator function';
    a.style.cssText='position:fixed;right:10px;bottom:10px;width:120px;height:24px';document.body.append(a);
    a.getBoundingClientRect=()=>{throw new Error('JavaScript must not measure the term anchor');};
    attachTermLink(a,'term-index-indicator-function',{current:()=>true,document:async()=>({getDestination:async()=>[0]})},async()=>{});
    window.cssTermAnchor=a;
    a.dispatchEvent(new MouseEvent('contextmenu',{bubbles:true,cancelable:true,clientX:385,clientY:839}));
  })()`);
  for (const kind of ["pointer", "keyboard"]) {
    if (kind === "keyboard")
      await tab.evaluate(
        "window.cssTermAnchor.dispatchEvent(new KeyboardEvent('keydown',{key:'F10',shiftKey:true,bubbles:true,cancelable:true}))",
      );
    await tab.waitFor("document.querySelector('.term-context-menu:popover-open')");
    const fits = await tab.evaluate<boolean>(`(() => {
      const menu=document.querySelector('.term-context-menu'),r=menu.getBoundingClientRect();
      return r.left>=0 && r.top>=0 && r.right<=innerWidth && r.bottom<=innerHeight && !menu.style.left && !menu.style.top;
    })()`);
    assert.equal(fits, true, kind);
    await tab.pressKey("Escape");
  }
});

test("bibliography, external URLs and PDF passages have hover previews", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(
    "window.ttViolations=[];document.addEventListener('securitypolicyviolation',e=>window.ttViolations.push(e.violatedDirective));",
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  await tab.evaluate(`(async()=>{
    const {attachTermLink}=await import('./build/term-preview.js');
    window.previewCalls=0;
    const reference={key:'Example',title:'Example title',source:'Plain-text fallback',html:'Author. <em>Example title</em>. 2026. <math><mi>x</mi></math><img src=x onerror=alert(1)>'};
    const context={current:()=>true,references:()=>({entries:{Example:reference},urls:{'https://doi.org/10.1/example':'Example'}}),document:async()=>{window.previewCalls++;return {getDestinations:async()=>({}),getDestination:async()=>[0,{name:'XYZ'},0,200],getPage:async()=>({getTextContent:async()=>({items:[{str:'Linked passage excerpt',transform:[1,0,0,1,0,180]}]})})};}};
    for(const [id,dest] of [['citation','cite.0@ref-Example'],['doi','https://doi.org/10.1/example'],['external','https://example.com/article'],['email','mailto:author@example.com'],['passage','page.3']]){
      const a=document.createElement('a');a.id=id;a.href='#';a.textContent=id;document.body.append(a);
      attachTermLink(a,dest,context,async()=>{throw new Error('Hover must not navigate');});
    }
  })()`);
  for (const [id, expected] of [
    ["citation", "Author. Example title. 2026."],
    ["doi", "Author. Example title. 2026."],
    ["external", "https://example.com/article"],
    ["email", "mailto:author@example.com"],
    ["passage", "Linked passage excerpt"],
  ]) {
    await tab.evaluate(`document.getElementById(${JSON.stringify(id)}).dispatchEvent(new MouseEvent('mouseenter'))`);
    await tab.waitFor(
      `document.querySelector('.term-preview-body')?.textContent.includes(${JSON.stringify(expected)})`,
    );
    if (id === "citation" || id === "doi") {
      assert.equal(await tab.evaluate("document.querySelector('.term-preview-body em')?.textContent"), "Example title");
      assert.equal(await tab.evaluate("document.querySelector('.term-preview-body math mi')?.textContent"), "x");
      assert.equal(await tab.evaluate("!!document.querySelector('.term-preview-body [onerror]')"), false);
    }
    if (id !== "passage") assert.equal(await tab.evaluate("window.previewCalls"), 0);
  }
  assert.equal(await tab.evaluate("window.previewCalls"), 1);
  assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
});
