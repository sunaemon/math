import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("large marker menus render only visible rows plus one screen of overscan", async (t) => {
  const previous = process.env.BOOKLINK_AUTOBUILD;
  process.env.BOOKLINK_AUTOBUILD = "0";
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  if (previous === undefined) delete process.env.BOOKLINK_AUTOBUILD;
  else process.env.BOOKLINK_AUTOBUILD = previous;
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&pdfMode=chapter&marker=preface_rational_complexity`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 30000 });
  await tab.evaluate(`(async()=>{
    const {state}=await import('./build/state.js');
    window.virtualState=state;
    window.mathCalls=0;
    state.katex={renderToString:()=>{window.mathCalls++;throw new Error('Fixed math must be precomputed')}};
    document.querySelector('#marker-field').click();
  })()`);
  const initial = await tab.evaluate<{ rows: number; total: number; calls: number; height: number }>(
    `({rows:document.querySelectorAll('#marker-list .marker-row').length,total:window.virtualState.entries.length,calls:window.mathCalls,height:document.querySelector('#marker-list').clientHeight})`,
  );
  t.diagnostic(`${initial.total} markers: ${initial.rows} mounted rows, ${initial.calls} KaTeX calls on open`);
  assert.ok(initial.total > 1000);
  assert.ok(initial.rows <= 3 * Math.ceil(initial.height / 52) + 2, JSON.stringify(initial));
  assert.equal(initial.calls, 0, JSON.stringify(initial));
  await tab.evaluate("document.querySelector('#marker-list').scrollTop=200000");
  await tab.waitFor("Number(document.querySelector('#marker-list .marker-row').dataset.position)>1000");
  assert.ok((await tab.evaluate<number>("document.querySelectorAll('#marker-list .marker-row').length")) < 40);
  await tab.evaluate(
    "const search=document.querySelector('#marker-search');search.value='greedyApprox_prefix';search.dispatchEvent(new Event('input',{bubbles:true}))",
  );
  await tab.waitFor("document.querySelectorAll('#marker-list .marker-row').length===1");
  assert.equal(
    await tab.evaluate("document.querySelector('#marker-list .marker-row').getAttribute('aria-setsize')"),
    "1",
  );
  await tab.evaluate(
    "document.querySelector('#marker-search').dispatchEvent(new KeyboardEvent('keydown',{key:'Enter',bubbles:true,cancelable:true}))",
  );
  await tab.waitFor("document.querySelector('#marker-popover').hidden");
});
