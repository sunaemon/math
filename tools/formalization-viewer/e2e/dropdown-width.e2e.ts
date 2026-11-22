import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("marker and document dropdowns match their field widths across viewport sizes", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor("document.body.dataset.viewerReady === '1'");
  for (const width of [390, 1024, 2048]) {
    await tab.setViewport(width, 900);
    await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
    for (const [field, menu, search] of [
      ["#marker-field", "#marker-popover", "#marker-search"],
      [
        "#md-document-control .cselect-field",
        "#md-document-control .cselect-popover",
        "#md-document-control .cselect-search",
      ],
    ]) {
      await tab.evaluate(`document.querySelector(${JSON.stringify(field)}).click()`);
      const box = await tab.evaluate<{ field: number; menu: number; left: number; right: number }>(`(() => {
        const a=document.querySelector(${JSON.stringify(field)}).getBoundingClientRect();
        const b=document.querySelector(${JSON.stringify(menu)}).getBoundingClientRect();
        return {field:a.width,menu:b.width,left:Math.abs(a.left-b.left),right:b.right};
      })()`);
      assert.ok(Math.abs(box.field - box.menu) < 1, JSON.stringify({ width, ...box }));
      assert.ok(box.left < 1, JSON.stringify({ width, ...box }));
      assert.ok(box.right <= width);
      await tab.evaluate(
        `document.querySelector(${JSON.stringify(search)}).dispatchEvent(new KeyboardEvent('keydown',{key:'Escape',bubbles:true}))`,
      );
    }
  }
});
