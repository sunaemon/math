import assert from "node:assert/strict";
import test from "node:test";
import path from "node:path";
import { CdpBrowser } from "./cdp.ts";
import { startViewerServer } from "./viewer-server.ts";

test("formula overlays coexist with lemma marks in Markdown and the tagged PDF", async (t) => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const server = await startViewerServer(root, "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const page = await browser.newPage();
  await page.navigate(`${server.baseUrl}/polish-space/?v=1&layout=row(pdf,md)&pdfMode=full&marker=real_polish`);
  await page.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 60000 });
  await page.waitFor(
    "document.querySelectorAll('#md-source .formula-overlay').length>0 && document.querySelectorAll('.pdf-formula').length>0",
    { timeout: 90000 },
  );
  const original = await page.evaluate<any>(
    `({text:document.getElementById('md-source').textContent,marks:document.querySelectorAll('#md-source .mark').length})`,
  );
  assert.ok(original.marks > 0);
  await page.evaluate("document.getElementById('formula-overlays-toggle').click()");
  assert.equal(await page.evaluate("document.querySelectorAll('.formula-overlay,.pdf-formula').length"), 0);
  assert.deepEqual(
    await page.evaluate(
      `({text:document.getElementById('md-source').textContent,marks:document.querySelectorAll('#md-source .mark').length})`,
    ),
    original,
  );
  await page.evaluate("document.getElementById('formula-overlays-toggle').click()");
  await page.waitFor("document.querySelectorAll('.pdf-formula').length>0");
  assert.deepEqual(
    await page.evaluate(
      `({text:document.getElementById('md-source').textContent,marks:document.querySelectorAll('#md-source .mark').length})`,
    ),
    original,
  );
  const selected = await page.evaluate<any>(
    `(()=>{const n=document.querySelector('.pdf-formula');n.click();return {tag:n.dataset.formulaTag,index:n.dataset.formula};})()`,
  );
  assert.equal(await page.evaluate("document.getElementById('formula-popup').hidden"), false);
  assert.equal(await page.evaluate("document.getElementById('correspondence-dialog').open"), false);
  assert.ok(
    await page.evaluate(
      `Array.from(document.querySelectorAll('#md-source .formula-overlay')).some(n=>n.dataset.formulaTag===${JSON.stringify(selected.tag)} && n.classList.contains('formula-selected'))`,
    ),
  );
  await page.evaluate("document.querySelector('#formula-popup button').click()");
  await page.waitFor(
    `document.getElementById('correspondence-dialog').open && document.getElementById('correspondence-formula').value==='${selected.index}'`,
    { timeout: 30000 },
  );
});

test("viewer exposes the actual semantic AST and source-to-Lean operator evidence", async (t) => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const server = await startViewerServer(root, "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const page = await browser.newPage();
  await page.navigate(
    `${server.baseUrl}/polish-space/?v=1&layout=md&searchSource=src/polish-space-book/polish-spaces.md&searchLine=48`,
  );
  await page.waitFor("document.body.dataset.viewerReady === '1'", { timeout: 30000 });
  await page.evaluate("document.getElementById('correspondence-open').click()");
  await page.waitFor("document.querySelectorAll('#correspondence-formula option').length===434", { timeout: 90000 });
  assert.equal(await page.evaluate("document.querySelector('#correspondence-dialog').open"), true);
  const data = await page.evaluate<any>(
    `fetch('./correspondence.json?source=polish-space/src/polish-space-book/polish-spaces.md').then(r=>r.json())`,
  );
  assert.equal(data.status, "current");
  assert.equal(data._cacheInputs, undefined);
  const cached = await fetch(
    `${server.baseUrl}/polish-space/correspondence.json?source=polish-space/src/polish-space-book/polish-spaces.md`,
  );
  assert.ok(cached.headers.get("etag"));
  assert.equal((await fetch(cached.url, { headers: { "If-None-Match": cached.headers.get("etag")! } })).status, 304);
  const index = data.formulas.findIndex((row: any) => row.operators.length > 0);
  assert.ok(index >= 0);
  assert.ok(data.formulas[index].semanticExpressions[0].ast.node);
  await page.evaluate(
    `(()=>{const s=document.getElementById('correspondence-formula');s.value='${index}';s.dispatchEvent(new Event('change',{bubbles:true}));})()`,
  );
  assert.ok(await page.evaluate("document.querySelectorAll('.correspondence-operator tbody tr').length>0"));
  await page.evaluate("document.querySelector('.correspondence-operator button').click()");
  assert.ok(await page.evaluate("document.querySelector('#correspondence-source mark').textContent.length>0"));
  assert.ok(
    await page.evaluate(
      "[...document.querySelectorAll('#correspondence-body summary')].some(x=>/Semantic AST|意味AST/.test(x.textContent))",
    ),
  );
  await page.evaluate("document.getElementById('correspondence-close').click()");
  assert.equal(await page.evaluate("document.querySelector('#correspondence-dialog').open"), false);
  await page.evaluate("document.getElementById('correspondence-open').click()");
  assert.ok(await page.evaluate("document.querySelectorAll('.correspondence-operator tbody tr').length>0"));
  assert.equal(await page.evaluate("document.getElementById('correspondence-formula').value"), String(index));
  await page.evaluate("document.getElementById('correspondence-close').click()");
  assert.equal((await fetch(`${server.baseUrl}/polish-space/correspondence.json?source=../private.md`)).status, 404);
  const unavailable = await fetch(
    `${server.baseUrl}/polish-space/correspondence.json?source=polish-space/src/polish-space-book/preface.md`,
  );
  assert.equal(((await unavailable.json()) as any).status, "unavailable");
});

test("formula selection highlights exact original Lean occurrences without changing code or lemma marks", async (t) => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const server = await startViewerServer(root, "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const page = await browser.newPage();
  await page.navigate(`${server.baseUrl}/polish-space/?v=1&layout=row(md,lean)&marker=real_polish`);
  await page.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 60000 });
  await page.waitFor("document.querySelector('#md-source .formula-overlay[data-formula=\"37\"]')", { timeout: 90000 });
  const original = await page.evaluate<any>(
    `({text:document.getElementById('lean-source').textContent,marks:document.querySelectorAll('#lean-source .mark').length})`,
  );
  await page.evaluate(`document.querySelector('#md-source .formula-overlay[data-formula="37"]').click()`);
  await page.waitFor("document.querySelectorAll('#lean-source .lean-formula-overlay').length>0", { timeout: 300000 });
  assert.deepEqual(
    await page.evaluate(
      `({text:document.getElementById('lean-source').textContent,marks:document.querySelectorAll('#lean-source .mark').length})`,
    ),
    original,
  );
  assert.match(
    await page.evaluate<string>(
      `Array.from(document.querySelectorAll('.lean-formula-overlay')).map(n=>n.textContent).join('')`,
    ),
    /dist/,
  );
  await page.evaluate(`document.querySelector('#md-source .formula-overlay[data-formula="0"]').click()`);
  await page.waitFor(
    "document.querySelectorAll('.lean-formula-overlay').length===0 && /No exact|確定できません/.test(document.querySelector('.formula-lean-status').textContent)",
  );
});

test("hover links PDF, Markdown and original Lean in every direction without navigating the marker", async (t) => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const server = await startViewerServer(root, "polish-space");
  t.after(() => server.stop());
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const page = await browser.newPage();
  await page.setViewport(1800, 1000);
  await page.navigate(
    `${server.baseUrl}/polish-space/?v=1&layout=row(pdf,md,lean)&pdfMode=full&marker=complete_compatible_metric_bounded_by_one`,
  );
  await page.waitFor("document.body.dataset.viewerReady==='1'", { timeout: 60000 });
  await page.waitFor(
    "document.querySelector('#md-source .formula-overlay[data-formula=\"37\"]') && document.querySelectorAll('.lean-formula-anchor').length>0",
    { timeout: 120000 },
  );
  const md = '#md-source .formula-overlay[data-formula="37"]';
  await page.evaluate(`document.querySelector(${JSON.stringify(md)}).scrollIntoView({block:'nearest'})`);
  await new Promise((resolve) => setTimeout(resolve, 500));
  const original = await page.evaluate<any>(
    `({url:location.href,md:document.getElementById('md-source').textContent,lean:document.getElementById('lean-source').textContent,marks:document.querySelectorAll('.mark').length})`,
  );
  await page.hover(md);
  await page.waitFor(
    "document.querySelector('#md-source .formula-hovered') && document.querySelector('.pdf-formula.formula-hovered') && document.querySelector('#lean-source .lean-formula-overlay') && document.getElementById('formula-popup').dataset.mode==='hover'",
    { timeout: 30000 },
  );
  await page.waitFor("document.querySelector('.formula-lean-status').dataset.coverage==='partial'");
  assert.equal(
    await page.evaluate(
      "document.querySelectorAll('#lean-source .formula-hovered,#lean-source .formula-selected').length",
    ),
    0,
  );
  assert.ok(await page.evaluate("document.querySelectorAll('#lean-source .formula-partial-active').length>0"));
  assert.equal(
    await page.evaluate(
      "getComputedStyle(document.querySelector('#lean-source .formula-partial-active')).backgroundColor",
    ),
    "rgba(0, 0, 0, 0)",
  );
  assert.match(
    await page.evaluate<string>("document.querySelector('.formula-lean-status').textContent"),
    /subexpression matches: 5|部分式のみ5箇所/,
  );
  const tag = await page.evaluate<string>(`document.querySelector(${JSON.stringify(md)}).dataset.formulaTag`);
  await page.evaluate(
    `Array.from(document.querySelectorAll('.lean-formula-anchor')).find(n=>JSON.parse(n.dataset.formulaTags).includes(${JSON.stringify(tag)})).dataset.hoverTest='lean'`,
  );
  await page.hover('[data-hover-test="lean"]');
  await page.waitFor(
    "document.querySelector('#lean-source .lean-formula-overlay') && document.querySelector('#md-source .formula-hovered') && document.querySelector('.pdf-formula.formula-hovered')",
  );
  await page.hover('.pdf-formula[data-formula="37"]');
  await page.waitFor(
    "document.querySelector('#md-source .formula-hovered[data-formula=\"37\"]') && document.querySelector('#lean-source .lean-formula-overlay') && document.querySelector('.pdf-formula.formula-hovered[data-formula=\"37\"]')",
  );
  assert.deepEqual(
    await page.evaluate(
      `({url:location.href,md:document.getElementById('md-source').textContent,lean:document.getElementById('lean-source').textContent,marks:document.querySelectorAll('.mark').length})`,
    ),
    original,
  );
  await page.hover("#formula-overlays-toggle");
  await page.waitFor(
    "document.querySelectorAll('.formula-hovered').length===0 && document.getElementById('formula-popup').hidden",
  );
  await page.evaluate(`document.querySelector(${JSON.stringify(md)}).click()`);
  await page.waitFor(
    "document.getElementById('formula-popup').dataset.mode==='pinned' && document.querySelector('.lean-formula-overlay.formula-partial-active')",
  );
  await page.hover('[data-hover-test="lean"]');
  await page.waitFor("document.getElementById('formula-popup').dataset.mode==='hover'");
  await page.hover("#formula-overlays-toggle");
  await page.waitFor(
    "document.getElementById('formula-popup').dataset.mode==='pinned' && document.querySelectorAll('.formula-hovered').length===0",
  );
  await page.evaluate(`document.querySelector('#md-source .formula-overlay[data-formula="64"]').click()`);
  await page.waitFor(
    "document.querySelector('.formula-lean-status').dataset.coverage==='whole' && document.querySelector('#lean-source .formula-selected')",
  );
  await page.evaluate("document.getElementById('formula-overlays-toggle').click()");
  assert.equal(
    await page.evaluate(
      "document.querySelectorAll('.formula-overlay,.pdf-formula,.lean-formula-anchor,.formula-selected,.formula-hovered,.formula-partial-active').length",
    ),
    0,
  );
});
