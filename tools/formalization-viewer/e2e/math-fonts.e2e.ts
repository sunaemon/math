import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("fixed formulas render native MathML without loading KaTeX", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady === '1'", { timeout: 30000 });
  const result = await tab.evaluate<{ count: number; width: number; height: number; requests: string[] }>(`(async()=>{
    const {project}=await import('./build/state.js');
    const html=Object.values(project.fixedMath).find(value=>value.includes('<math'));
    const {setHTML}=await import('./build/safe-html.js');const example=document.createElement('div');setHTML(example,html);document.body.append(example);
    const math=example.querySelector('math');const rect=math.getBoundingClientRect();
    return {count:Object.keys(project.fixedMath).length,width:rect.width,height:rect.height,
      requests:performance.getEntriesByType('resource').map(e=>e.name).filter(name=>name.includes('/vendor/katex/'))};
  })()`);
  assert.ok(result.count > 0);
  assert.ok(result.width > 0 && result.height > 0);
  assert.deepEqual(result.requests, []);
});
