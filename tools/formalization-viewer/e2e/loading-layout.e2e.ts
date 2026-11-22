import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("loading status leaves source and PDF pane geometry unchanged", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(`(async()=>{
    const link=document.createElement('link');link.rel='stylesheet';link.href='./styles.css';
    const loaded=new Promise(resolve=>link.onload=resolve);document.head.append(link);await loaded;
    document.body.innerHTML='<section class="pane" style="width:600px;height:400px"><header class="pane-header">Source</header><pre class="source document-scroller">Source content</pre></section>';
  })()`);
  for (const kind of ["source", "pdf-viewer"]) {
    await tab.evaluate(`document.querySelector('pre').className=${JSON.stringify(kind + " document-scroller")}`);
    const bounds = () => tab.evaluate("JSON.stringify(document.querySelector('pre').getBoundingClientRect().toJSON())");
    const before = await bounds();
    for (const text of ["Loading…", "Loading PDF · 123.4 MB / 999.9 MB", null]) {
      await tab.evaluate(
        `import('./build/loading-progress.js').then(({paneLoadStatus})=>paneLoadStatus(document.querySelector('pre'),${JSON.stringify(text)}))`,
      );
      assert.equal(await bounds(), before, `${kind}: ${text}`);
    }
  }
});

test("repeated PDF geometry refreshes reuse resolved destinations", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=pdf&pdfMode=full&marker=preface_rational_complexity`);
  await tab.waitFor("document.body.dataset.viewerReady === '1'", { timeout: 30000 });
  const result = await tab.evaluate<{ calls: number; reused: boolean; targets: number }>(`(async()=>{
    const {state}=await import('./build/state.js');
    await state.pdf.targetPromise;
    const targets=state.pdf.targets;
    const doc=state.pdf.document;
    const original=doc.getDestination;
    let calls=0;
    doc.getDestination=function(...args){calls++;return original.apply(this,args)};
    try {
      const {refreshPdfLayoutGeometry}=await import('./build/pdf.js');
      for(let i=0;i<20;i++) refreshPdfLayoutGeometry();
      await new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
      return {calls,reused:targets===state.pdf.targets,targets:targets.size};
    } finally {doc.getDestination=original;}
  })()`);
  assert.ok(result.targets > 0);
  assert.equal(result.calls, 0);
  assert.equal(result.reused, true);
});
