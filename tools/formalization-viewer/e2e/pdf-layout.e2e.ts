import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("PDF layout menu changes rendered paths and restores choices from the URL", async () => {
  const saved = process.env.BOOKLINK_AUTOBUILD;
  process.env.BOOKLINK_AUTOBUILD = "0";
  const root = path.resolve(import.meta.dirname, "..", "..", "..");
  const server = await startViewerServer(root, "polish-space");
  let browser: CdpBrowser | undefined;
  try {
    browser = await CdpBrowser.launch();
    const tab = await browser.newPage();
    await tab.setViewport(390, 844);
    // A hidden PDF pane exercises selection without starting a book build.
    await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md&pdfMode=full&paper=b6&fontSize=12`);
    await tab.waitFor("document.body.dataset.viewerReady === '1'", { timeout: 30000 });
    assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('#settings-menu')).display"), "none");
    await tab.evaluate("document.querySelector('#settings-toggle').click()");
    assert.equal(await tab.evaluate("document.querySelector('#settings-menu').hidden"), false);
    assert.ok(
      await tab.evaluate<boolean>(`(() => {
      const r = document.querySelector('#settings-menu').getBoundingClientRect();
      return r.left >= 0 && r.right <= innerWidth;
    })()`),
    );
    assert.equal(await tab.evaluate("document.querySelector('#pdf-paper').value"), "b6");
    assert.equal(await tab.evaluate("document.querySelector('#pdf-font-size').value"), "12");
    assert.match(await tab.evaluate<string>("document.querySelector('#pdf-link').href"), /-layout-b6-12pt-debug\.pdf$/);
    await tab.evaluate(`for (const [id,value] of [['pdf-paper','a4'],['pdf-font-size','11']]) {
      const control = document.getElementById(id); control.value = value; control.dispatchEvent(new Event('change'));
    }`);
    const url = await tab.evaluate<string>("location.href");
    assert.equal(new URL(url).searchParams.get("paper"), "a4");
    assert.equal(new URL(url).searchParams.get("fontSize"), "11");
    assert.match(await tab.evaluate<string>("document.querySelector('#pdf-link').href"), /-layout-a4-11pt-debug\.pdf$/);
    await tab.navigate(url);
    await tab.waitFor("document.body.dataset.viewerReady === '1'", { timeout: 30000 });
    assert.equal(await tab.evaluate("document.querySelector('#pdf-paper').value"), "a4");
    assert.equal(await tab.evaluate("document.querySelector('#pdf-font-size').value"), "11");
  } finally {
    await browser?.close();
    await server.stop();
    if (saved === undefined) delete process.env.BOOKLINK_AUTOBUILD;
    else process.env.BOOKLINK_AUTOBUILD = saved;
  }
});
