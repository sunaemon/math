import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("source markers are tab stops with Enter and Space activation, disabled when hidden", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor(
    "document.body.dataset.viewerReady==='1' && !!document.querySelector('#md-source [data-mark-control]')",
  );
  const entry = await tab.evaluate<string>(`(()=>{
    const mark=document.querySelector('#md-source [data-mark-control]');
    const start=document.createElement('button');start.textContent='Tab start';mark.before(start);start.focus();
    return mark.dataset.entry;
  })()`);
  await tab.pressKey("Tab");
  assert.equal(await tab.evaluate("document.activeElement.dataset.entry"), entry);
  assert.equal(await tab.evaluate("document.activeElement.getAttribute('role')"), "button");
  for (const key of ["Enter", " "]) {
    await tab.pressKey(key);
    await tab.waitFor(
      `document.querySelector('#md-source [data-mark-control][data-entry="${entry}"]').classList.contains('active')`,
    );
  }
  assert.equal(
    await tab.evaluate(`(()=>{
    const ids=[...document.querySelectorAll('#md-source [data-mark-control]')].map(node=>node.dataset.entry);
    return new Set(ids).size===ids.length;
  })()`),
    true,
  );
  await tab.evaluate("document.querySelector('#highlights-seg [data-value=off]').click()");
  assert.equal(
    await tab.evaluate("[...document.querySelectorAll('[data-mark-control]')].every(node=>node.tabIndex===-1)"),
    true,
  );
});
