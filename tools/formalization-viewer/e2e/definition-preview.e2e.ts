import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("cross-chapter source definition renders with KaTeX without requesting a PDF", async (t) => {
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
  await tab.evaluate(`(async () => {
    const { setProject } = await import('./build/state.js');
    const { attachTermLink } = await import('./build/term-preview.js');
    const manifest = await fetch('./manifest.json').then(r => r.json());
    setProject(manifest);
    const anchor = document.createElement('a');
    anchor.textContent = 'indicator function';
    anchor.href = '#';
    document.body.replaceChildren(anchor);
    attachTermLink(anchor, 'term-index-indicator-function', {
      document: () => { throw new Error('Definition hover must not load a PDF'); },
      current: () => true,
    }, async () => {});
    anchor.dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor("document.querySelector('.term-preview-source math[display=block]')", { timeout: 20000 });
  const result = await tab.evaluate<{ text: string; errors: number; canvases: number }>(`({
    text: document.querySelector('.term-preview-body').textContent,
    errors: document.querySelectorAll('.term-preview-source .katex-error').length,
    canvases: document.querySelectorAll('.term-preview-body canvas').length,
  })`);
  assert.match(result.text, /indicator function/);
  assert.equal(result.errors, 0);
  assert.equal(result.canvases, 0);
  assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  await tab.evaluate(`(async () => {
    const { setProject } = await import('./build/state.js');
    const { attachTermLink } = await import('./build/term-preview.js');
    setProject(await fetch('./manifest.json').then(r => r.json()));
    const anchor = document.createElement('a');
    anchor.textContent = 'Q';
    anchor.href = '#';
    document.body.replaceChildren(anchor);
    attachTermLink(anchor, 'notation-index-QQ', {
      document: () => { throw new Error('Notation hover must not load a PDF'); },
      current: () => true,
    }, async () => {});
    anchor.dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor("document.querySelector('.term-preview-source li strong .katex')", { timeout: 20000 });
  const japanese = await tab.evaluate<{ text: string; errors: number }>(`({
    text: document.querySelector('.term-preview-source').textContent,
    errors: document.querySelectorAll('.term-preview-source .katex-error').length,
  })`);
  assert.match(japanese.text, /数の集合/);
  assert.doesNotMatch(japanese.text, /\\define|RestrictedSet|mathmeta|\*\*/);
  assert.equal(japanese.errors, 0);
  await tab.evaluate(`(async () => {
    const { attachTermLink, dismissTermPopup } = await import('./build/term-preview.js');
    dismissTermPopup();
    const anchor=document.createElement('a');
    anchor.href='#';
    document.body.replaceChildren(anchor);
    attachTermLink(anchor,'notation-index-InternalDisjointUnion',{
      current:()=>true,document:()=>{throw new Error('No PDF');},
    },async()=>{});
    anchor.dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor("document.querySelector('.term-preview-source')?.textContent.includes('内的非交和')", {
    timeout: 20000,
  });
  assert.doesNotMatch(
    await tab.evaluate<string>("document.querySelector('.term-preview-source').textContent"),
    /displaylimits|katex-error/,
  );
  await tab.evaluate(`(async () => {
    const { appendPageLinks } = await import('./build/pdf-document.js');
    const { dismissTermPopup } = await import('./build/term-preview.js');
    dismissTermPopup();
    const container = document.createElement('div');
    document.body.replaceChildren(container);
    appendPageLinks(container, [{subtype:'Link',rect:[0,0,120,20],dest:'notation-index-BaireSpace'}],
      {width:500,height:600,convertToViewportPoint:(x,y)=>[x,600-y]},null,
      async dest=>{window.definitionJump = dest;},
      {document:()=>{throw new Error('Preview cannot request a PDF');},current:()=>true});
    container.querySelector('a').id='baire-registry-test';
    container.querySelector('a').dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor("document.querySelector('.term-preview-source')?.textContent.includes('Baire空間')", {
    timeout: 20000,
  });
  const baire = await tab.evaluate<string>("document.querySelector('.term-preview-source').textContent");
  assert.doesNotMatch(baire, /零次元|\\\\BookSectionLink|zero-dimensional/);
  await tab.evaluate("document.querySelector('#baire-registry-test').click()");
  await tab.waitFor("window.definitionJump === 'term-def-baire-space'", { timeout: 5000 });
  await tab.evaluate(
    "document.querySelector('#baire-registry-test').dispatchEvent(new MouseEvent('contextmenu',{bubbles:true}))",
  );
  await tab.waitFor("document.querySelector('.term-context-menu button')?.disabled === false", { timeout: 5000 });
  const targetChapter = await tab.evaluate<string>(`(async()=> {
    const { chapterPdfForDestination } = await import('./build/pdf.js');
    return await chapterPdfForDestination('notation-index-BaireSpace');
  })()`);
  assert.match(targetChapter, /polish-space-book-ja-preview-polish-spaces\.pdf$/);
  // An English peer pane must not reuse the active Japanese book's records.
  await tab.evaluate(`(async () => {
    const { attachTermLink, dismissTermPopup } = await import('./build/term-preview.js');
    dismissTermPopup();
    const english = await fetch('/polish-space/manifest.json').then(response=>response.json());
    const anchor = document.createElement('a');
    anchor.href='#';
    document.body.replaceChildren(anchor);
    attachTermLink(anchor,'notation-index-BaireSpace',{
      current:()=>true,
      document:()=>{throw new Error('No PDF');},
      definitions:()=>english.definitionRegistry,
      macros:()=>english.katexMacros,
      chapterTitles:()=>english.chapterTitles,
    },async()=>{});
    anchor.dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor("document.querySelector('.term-preview-source')?.textContent.includes('Baire space')", {
    timeout: 20000,
  });
  assert.doesNotMatch(
    await tab.evaluate<string>("document.querySelector('.term-preview-source').textContent"),
    /Baire空間|零次元/,
  );
  await tab.evaluate(`(async () => {
    const { project } = await import('./build/state.js');
    const { attachTermLink, dismissTermPopup } = await import('./build/term-preview.js');
    dismissTermPopup();
    const dest = Object.keys(project.definitionRegistry.aliases).find(key => /^chapter\\./.test(key)) ?? 'sec:baire-class-functions';
    const anchor = document.createElement('a');
    anchor.href = '#';
    anchor.textContent = 'Section reference';
    document.body.replaceChildren(anchor);
    attachTermLink(anchor, dest, {
      document: () => { throw new Error('Section hover must not load a PDF'); },
      current: () => true,
    }, async () => {});
    anchor.dispatchEvent(new MouseEvent('mouseenter'));
  })()`);
  await tab.waitFor(
    "document.querySelector('.term-definition-preview[aria-label=\"Section excerpt\"] .term-preview-source strong')",
    { timeout: 20000 },
  );
  assert.equal(
    await tab.evaluate("document.querySelector('.term-definition-preview > strong').textContent"),
    "Section",
  );
  assert.equal(await tab.evaluate("document.querySelector('.pdf-section-link').hasAttribute('aria-haspopup')"), false);
  assert.deepEqual(await tab.evaluate("window.ttViolations"), []);
});
