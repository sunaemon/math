import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("Tab previews PDF links immediately and survives the page scroll caused by focus", async (t) => {
  const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(`${server.baseUrl}/polish-space/styles.css`);
  await tab.evaluate(`(async()=>{
    document.body.innerHTML='<button id="start">Start</button><div class="pdf-viewer" style="width:350px;height:180px;overflow:auto"><div style="height:400px"><a id="first" class="pdf-link-box" href="https://example.com/first">First link</a></div><div style="height:400px"><a id="second" class="pdf-link-box" href="https://example.com/second">Second link</a></div></div>';
    const {attachTermLink}=await import('./build/term-preview.js');
    for(const anchor of document.querySelectorAll('a')) attachTermLink(anchor,anchor.href,{document:async()=>({}),current:()=>true},async()=>{});
    document.getElementById('start').focus();
  })()`);
  await tab.pressKey("Tab");
  assert.equal(await tab.evaluate("document.activeElement.id"), "first");
  assert.equal(
    await tab.evaluate("document.querySelector('.term-preview-body')?.textContent"),
    "https://example.com/first",
    "keyboard focus must not wait for the mouse hover timer",
  );
  await tab.pressKey("Tab");
  assert.equal(await tab.evaluate("document.activeElement.id"), "second");
  assert.equal(
    await tab.evaluate("document.querySelector('.term-preview-body')?.textContent"),
    "https://example.com/second",
  );
  await tab.evaluate("new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))");
  assert.ok((await tab.evaluate<number>("document.querySelector('.pdf-viewer').scrollTop")) > 0);
  assert.equal(
    await tab.evaluate(
      "document.getElementById('second').getAttribute('aria-describedby')===document.querySelector('.term-definition-preview')?.id",
    ),
    true,
  );
  await tab.evaluate("document.querySelector('.pdf-viewer').scrollTop=0");
  await tab.waitFor("!document.querySelector('.term-definition-preview')");
  await tab.evaluate(
    "document.activeElement.blur();document.getElementById('first').dispatchEvent(new MouseEvent('mouseenter'))",
  );
  assert.equal(
    await tab.evaluate("!!document.querySelector('.term-definition-preview')"),
    false,
    "pointer hover retains its delay",
  );
  await tab.waitFor("document.querySelector('.term-preview-body')?.textContent==='https://example.com/first'");
});
