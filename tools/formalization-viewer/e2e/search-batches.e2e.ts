import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("next match extends the search by 200 at each 100-remaining threshold without moving the selected hit", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady==='1'");
  await tab.evaluate(`(async()=>{
    const {state}=await import('./build/state.js'), {setHTML}=await import('./build/safe-html.js');
    state.sources.md=Array.from({length:650},(_,i)=>'needle '+(i+1)).join('\\n');
    setHTML(state.panes.md,Array.from({length:650},(_,i)=>'<div class="line" data-line="'+(i+1)+'">needle '+(i+1)+'</div>').join(''));
    document.querySelector('[data-pane=md] .pane-search').click();
    const input=document.getElementById('book-search-input');input.value='needle';input.dispatchEvent(new Event('input'));
  })()`);
  const counter = "document.querySelector('#pane-search [role=status]').textContent";
  await tab.waitFor(`${counter}==='1 / 200+'`);
  const advance = async (count: number) =>
    tab.evaluate(
      `(()=>{const next=document.querySelector('#pane-search .search-navigation button:last-child');for(let i=0;i<${count};i++)next.click();})()`,
    );
  await advance(98);
  assert.equal(await tab.evaluate(counter), "99 / 200+");
  await advance(1);
  await tab.waitFor(`${counter}==='100 / 400+'`);
  assert.equal(await tab.evaluate("document.querySelector('.line.search-hit').dataset.line"), "100");
  await advance(199);
  assert.equal(await tab.evaluate(counter), "299 / 400+");
  await advance(1);
  await tab.waitFor(`${counter}==='300 / 600+'`);
  await advance(200);
  await tab.waitFor(`${counter}==='500 / 650'`);
  assert.equal(await tab.evaluate("document.querySelector('.line.search-hit').dataset.line"), "500");
});
