import { test } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("browser language, focused search mode, fixed counter and menu grouping", { timeout: 60000 }, async (t) => {
  for (const [language, book, bookLanguage, settings, placeholder, close, chat] of [
    ["ja-JP", "polish-space", "en", "表示設定", "検索語を入力", "閉じる", "チャットを開く"],
    ["en-GB", "polish-space-ja", "ja", "View options", "Enter search terms", "Close", "Open chat"],
  ]) {
    const server = await startViewerServer(path.resolve(import.meta.dirname, "../../.."), book);
    t.after(() => server.stop());
    const browser = await CdpBrowser.launch();
    t.after(() => browser.close());
    const tab = await browser.newPage();
    await tab.onNewDocument(`Object.defineProperty(navigator,'languages',{get:()=>[${JSON.stringify(language)}]});`);
    await tab.navigate(`${server.baseUrl}/${book}/?v=1&layout=md&focus=md`);
    await tab.waitFor("document.body.dataset.viewerReady==='1'");
    assert.equal(await tab.evaluate("document.documentElement.lang"), language.slice(0, 2));
    assert.equal(await tab.evaluate("document.getElementById('md-source').lang"), bookLanguage);
    assert.equal(await tab.evaluate("document.getElementById('settings-toggle').title"), settings);
    assert.equal(await tab.evaluate("document.getElementById('chat-toggle').title"), chat);
    assert.equal(await tab.evaluate("!!document.querySelector('#settings-menu #book-search-toggle')"), true);
    assert.equal(
      await tab.evaluate(
        "document.querySelector('.pane-check').closest('.vo-section')===document.querySelector('#layout-seg').closest('.vo-section')",
      ),
      true,
    );
    await tab.click("#pane-search-focused");
    assert.equal(await tab.evaluate("document.getElementById('book-search').open"), false);
    assert.equal(await tab.evaluate("getComputedStyle(document.getElementById('pane-tools')).display"), "none");
    assert.equal(await tab.evaluate("document.querySelector('#pane-search [role=status]').textContent"), "- / -");
    assert.equal(await tab.evaluate("document.getElementById('book-search-input').placeholder"), placeholder);
    for (const width of [1000, 390, 280]) {
      await tab.setViewport(width, 800);
      const sizes = await tab.evaluate<number[]>(`(()=>{
        const input=document.getElementById('book-search-input'), count=document.querySelector('#pane-search [role=status]');
        return ['- / -','1 / 2','200 / 200+'].map(value=>{count.textContent=value;return input.getBoundingClientRect().width});
      })()`);
      assert.ok(sizes[0] > 80, `input uses available width at ${width}px`);
      assert.ok(
        sizes.every((size) => Math.abs(size - sizes[0]) < 1),
        "counter never changes input width",
      );
    }
    assert.equal(
      await tab.evaluate("document.querySelector('#pane-search button[aria-label]').getAttribute('aria-label')"),
      language.startsWith("ja") ? "前の一致" : "Previous match",
    );
    await tab.pressKey("Escape");
    assert.equal(await tab.evaluate("document.getElementById('pane-search').hidden"), true);
    assert.notEqual(await tab.evaluate("getComputedStyle(document.getElementById('pane-tools')).display"), "none");
    await tab.click("#pane-search-focused");
    await tab.evaluate(`document.querySelector('#pane-search button[aria-label=${JSON.stringify(close)}]').click()`);
    assert.equal(await tab.evaluate("document.getElementById('pane-search').hidden"), true);
    await tab.click("#pane-restore");
    await tab.evaluate(
      "document.querySelector('[data-pane=md]').style.width='120px';document.querySelector('[data-pane=md] .pane-search').click()",
    );
    assert.equal(
      await tab.evaluate(`(()=>{
      const bar=document.getElementById('pane-search').getBoundingClientRect();
      return [...document.querySelectorAll('#pane-search input, #pane-search [role=status], #pane-search button')].every(node=>{const r=node.getBoundingClientRect();return r.left>=bar.left && r.right<=bar.right;});
    })()`),
      true,
      "search controls fit even a narrow split pane",
    );
    assert.equal(
      await tab.evaluate(`(()=>{
      const pane=document.querySelector('[data-pane=md]'), header=pane.querySelector('.pane-header').getBoundingClientRect(), bar=document.getElementById('pane-search').getBoundingClientRect();
      return bar.top-header.bottom>=0 && bar.top-header.bottom<=6 && pane.getBoundingClientRect().right-bar.right<=6;
    })()`),
      true,
      "search stays directly below the header at the right edge",
    );
    await tab.evaluate("document.querySelector('[data-pane=md] .pane-search').click()");
    assert.equal(
      await tab.evaluate("document.getElementById('pane-search').hidden"),
      true,
      "the active pane search button exits search mode",
    );
    assert.equal(
      await tab.evaluate("document.querySelector('[data-pane=md] .pane-search').getAttribute('aria-expanded')"),
      "false",
    );
    await tab.evaluate("document.querySelector('[data-pane=md] .pane-search').click()");
    assert.equal(
      await tab.evaluate("document.getElementById('pane-search').hidden"),
      false,
      "the same button opens search again",
    );
    assert.equal(
      await tab.evaluate("document.querySelector('[data-pane=md] .pane-search').getAttribute('aria-expanded')"),
      "true",
    );
    await tab.pressKey("Escape");
    await tab.evaluate("document.getElementById('about-open').click()");
    assert.equal(await tab.evaluate("document.getElementById('about-overlay').open"), true);
    const licenses = await tab.evaluate<string>("document.getElementById('about-license-list').textContent");
    assert.match(licenses, /DOMPurify/);
    assert.match(licenses, /Pagefind/);
    assert.doesNotMatch(
      licenses,
      /tree-sitter|Manthe|Ackerman|AFK|Included in the static export|Build and verification only/,
    );
    if (language === "en-GB") {
      await tab.evaluate(
        "(()=>{const select=document.getElementById('ui-language');select.value='ja';select.dispatchEvent(new Event('change'));})()",
      );
      await tab.waitFor("document.body.dataset.viewerReady==='1' && document.documentElement.lang==='ja'");
      assert.equal(await tab.evaluate("document.getElementById('ui-language').value"), "ja");
      await tab.evaluate(
        "(()=>{const select=document.getElementById('ui-language');select.value='auto';select.dispatchEvent(new Event('change'));})()",
      );
      await tab.waitFor("document.body.dataset.viewerReady==='1' && document.documentElement.lang==='en'");
    }
    await tab.close();
  }
});
