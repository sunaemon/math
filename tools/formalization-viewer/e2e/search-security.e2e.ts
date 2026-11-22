import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("Trusted Types blocks raw HTML and policies sanitize HTML, SVG and MathML", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.onNewDocument(
    "window.ttViolations=[];document.addEventListener('securitypolicyviolation',e=>window.ttViolations.push({directive:e.violatedDirective,sample:e.sample,source:e.sourceFile,line:e.lineNumber}));",
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
  assert.equal(await tab.evaluate("!!document.querySelector('#search-scope option[value=pdf-peer]')"), false);
  assert.equal(await tab.evaluate("!!document.querySelector('[data-pane=pdf-peer] .pane-search')"), false);
  const result = await tab.evaluate<{ blocked: boolean; unsafe: boolean; math: boolean; svg: boolean }>(`(async()=>{
 const {setHTML}=await import('./build/safe-html.js');const el=document.createElement('div');document.body.append(el);
 let blocked=false;try{el.innerHTML='<b>raw</b>'}catch(e){blocked=e instanceof TypeError;}
 setHTML(el,'<math><mi>x</mi></math><svg viewBox="0 0 10 10"><path d="M0 0L10 10"/></svg><img src=x onerror="window.unsafe=true"><a href="javascript:window.unsafe=true">bad</a><script>window.unsafe=true<\\/script>');
 return {blocked,unsafe:!!el.querySelector('script,[onerror],[href^="javascript:"]'),math:!!el.querySelector('math mi'),svg:!!el.querySelector('svg path')};})()`);
  assert.deepEqual(result, { blocked: true, unsafe: false, math: true, svg: true });
  await tab.evaluate(`(() => {
    document.getElementById('book-search-toggle').click();
    const input = document.getElementById('book-search-input');
    input.value = 'space';
    input.dispatchEvent(new Event('input'));
  })()`);
  await tab.waitFor("!document.getElementById('book-search-more').hidden", { timeout: 45000 });
  assert.equal(await tab.evaluate("document.querySelectorAll('#book-search-results li').length"), 30);
  const first = await tab.evaluate("document.querySelector('#book-search-results a').href");
  await tab.evaluate("document.getElementById('book-search-more').scrollIntoView({block:'center'})");
  await tab.click("#book-search-more");
  await tab.waitFor("document.querySelectorAll('#book-search-results li').length > 30");
  assert.equal(await tab.evaluate("document.querySelector('#book-search-results a').href"), first);
});

test(
  "Japanese WASM full-text search finds unspaced prose and navigates to its source line",
  { timeout: 60000 },
  async (t) => {
    const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space-ja");
    t.after(() => server.stop());
    const browser = await CdpBrowser.launch();
    t.after(() => browser.close());
    const tab = await browser.newPage();
    await tab.onNewDocument(
      "window.ttViolations=[];document.addEventListener('securitypolicyviolation',e=>window.ttViolations.push({directive:e.violatedDirective,sample:e.sample,source:e.sourceFile,line:e.lineNumber}));",
    );
    await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&layout=md`);
    await tab.waitFor("document.body.dataset.viewerReady==='1'");
    assert.equal(
      tab.requests().some((url) => url.includes("/pagefind/")),
      false,
      "Search must be lazy",
    );
    assert.equal(await tab.evaluate("!!document.querySelector('[data-pane=pdf-peer] .pane-search')"), true);
    await tab.evaluate("document.getElementById('book-search-toggle').click()");
    await tab.evaluate(
      "(()=>{const input=document.getElementById('book-search-input');input.value='可算稠密';input.dispatchEvent(new Event('input'));})()",
    );
    await tab.waitFor("document.querySelector('#book-search-results a')", { timeout: 45000 });
    assert.equal(
      await tab.evaluate("document.querySelector('#book-search-results li').getBoundingClientRect().height<48"),
      true,
    );
    const destination = await tab.evaluate<string>("document.querySelector('#book-search-results a').href");
    assert.ok(new URL(destination).searchParams.get("searchSource")?.startsWith("polish-space-ja/"));
    await tab.click("#book-search-results a");
    await tab.waitFor("document.querySelector('.line.search-hit')");
    assert.equal(await tab.evaluate("document.getElementById('book-search').open"), false);
    assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
    assert.ok(tab.requests().some((url) => url.includes("pagefind.js")));
    const deep = new URL(destination);
    deep.searchParams.set("layout", "md");
    await tab.navigate(deep.href);
    await tab.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 30000 });
    assert.equal(
      await tab.evaluate("document.querySelector('.line.search-hit')?.dataset.line"),
      new URL(destination).searchParams.get("searchLine"),
    );
  },
);

test("Cmd/Ctrl+F searches each pane and retains independent queries", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(`(async()=>{
  const parsed=new DOMParser().parseFromString(await(await fetch('./index.html')).text(),'text/html');parsed.querySelectorAll('script').forEach(script=>script.remove());document.body.replaceChildren(...parsed.body.childNodes);
  for(const name of ['md','lean','tex','pdf']){const section=document.querySelector('[data-pane="'+name+'"]');let pre=section.querySelector('pre');if(!pre){pre=document.createElement('pre');section.append(pre);}pre.innerHTML='<div class="line" data-line="1">needle one</div><div class="line" data-line="2">needle two</div>'; }
  const meta=document.createElement('meta');meta.httpEquiv='Content-Security-Policy';meta.content="require-trusted-types-for 'script'; trusted-types viewer-html dompurify viewer-script-url";document.head.append(meta);
  const {state,setProject}=await import('./build/state.js');setProject({dir:'polish-space'});state.paneSections={};state.panes={};state.sources={md:'needle one\\nneedle two',lean:'theorem needle',tex:'needle tex'};
  for(const name of ['md','lean','tex','pdf']){state.paneSections[name]=document.querySelector('[data-pane="'+name+'"]');state.panes[name]=state.paneSections[name].querySelector('pre');}
  state.pdf.document={numPages:1,getPage:async()=>({view:[0,0,100,100],getTextContent:async()=>({items:[{str:'needle PDF',transform:[1,0,0,1,0,80]}]})})};
  const {initSearch}=await import('./build/search.js');initSearch(async()=>{});
 })()`);
  for (const [index, name] of ["md", "lean", "tex", "pdf"].entries()) {
    const prevented = await tab.evaluate<boolean>(
      `(()=>{document.querySelector('[data-pane="${name}"] pre').dispatchEvent(new Event('pointerdown',{bubbles:true}));const event=new KeyboardEvent('keydown',{key:'f',${index % 2 ? "metaKey" : "ctrlKey"}:true,bubbles:true,cancelable:true});document.dispatchEvent(event);return event.defaultPrevented;})()`,
    );
    assert.equal(prevented, true);
    assert.equal(await tab.evaluate("document.getElementById('pane-search').dataset.searchScope"), name);
    assert.equal(await tab.evaluate("document.getElementById('book-search').open"), false);
    await tab.evaluate(
      "(()=>{const input=document.getElementById('book-search-input');input.value='needle';input.dispatchEvent(new Event('input'));})()",
    );
    await tab.waitFor("document.querySelector('#pane-search [role=status]').textContent.startsWith('1 / ')");
    if (name !== "pdf")
      assert.ok(await tab.evaluate(`!!document.querySelector('[data-pane="${name}"] .line.search-hit')`));
    await tab.pressKey("Escape");
    assert.equal(await tab.evaluate("document.getElementById('pane-search').hidden"), true);
  }
  await tab.click('[data-pane="md"] .pane-search');
  assert.equal(await tab.evaluate("document.getElementById('book-search-input').value"), "needle");
});

test("PDF search loads a deferred document automatically under Trusted Types", { timeout: 90000 }, async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.onNewDocument(
    "window.ttViolations=[];document.addEventListener('securitypolicyviolation',e=>window.ttViolations.push(e.violatedDirective));",
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  assert.equal(
    await tab.evaluate("(async()=>{const {state}=await import('./build/state.js');return !!state.pdf.document;})()"),
    false,
  );
  await tab.evaluate(
    "(()=>{const check=document.querySelector('.pane-check[value=pdf]');check.checked=true;check.dispatchEvent(new Event('change'));document.querySelector('[data-pane=pdf] .pane-search').click();const input=document.getElementById('book-search-input');input.value='Polish';input.dispatchEvent(new Event('input'));})()",
  );
  await tab.waitFor("document.querySelector('#pane-search [role=status]').textContent.startsWith('1 / ')", {
    timeout: 75000,
  });
  assert.ok(tab.requests().some((url) => url.includes(".pdf")));
  assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
  await tab.waitFor("document.querySelector('.pdf-search-hit')");
});
