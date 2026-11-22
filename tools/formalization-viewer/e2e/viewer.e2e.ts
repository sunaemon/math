// Browser-driven end-to-end tests for the formalization viewer. Run with
// `make test-e2e` (needs a Chrome/Chromium binary; not part of `make test`).
//
// These cover what the unit tests deliberately cannot: the DOM/async glue and
// the live server connection. They launch the real serve.ts (HTTP + SSE bridge)
// and a headless Chrome driven over CDP, then drive the actual SPA — the source
// pane rendering into the DOM, the live /events + /lsp connections, the custom
// dropdown widget wiring, and cross-pane marker activation.

import { test, before, after } from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { computeHighlightData } from "../server/highlight-core.ts";
import { CdpBrowser, type CdpPage } from "./cdp.ts";
import { startViewerServer, type ViewerServer } from "./viewer-server.ts";

const REPO_ROOT = path.resolve(import.meta.dirname, "..", "..", "..");
// init() sets this once the stored/linked reading position has been restored;
// the first mark renders before that, still on the pre-restore first entry.
const READY = "document.body.dataset.viewerReady === '1'";
const MD_CONTROL = "#md-document-control";

async function openDocumentMenu(tab: CdpPage = page): Promise<void> {
  await tab.evaluate(
    "if (!document.querySelector('#settings-menu').matches(':popover-open')) document.querySelector('#settings-toggle').click()",
  );
}

let server: ViewerServer;
let browser: CdpBrowser;
let page: CdpPage;

before(async () => {
  server = await startViewerServer(REPO_ROOT, "polish-space");
  browser = await CdpBrowser.launch();
  page = await browser.newPage();
  await page.navigate(`${server.baseUrl}/?v=1&pdfMode=full&marker=preface_rational_complexity`);
  // The SPA fetches sources + the sourcemap, then renders the panes.
  await page.waitFor("document.querySelectorAll('#md-source .line').length > 0", { timeout: 30000 });
});

after(async () => {
  await browser?.close();
  await server?.stop();
});

test("boots: every pane mounts and the source pane renders with booklink marks", async () => {
  const dom = await page.evaluate<{ panes: string[]; mdLines: number; mdMarks: number; leanLines: number }>(`(() => ({
    panes: [...document.querySelectorAll('.pane')].map((p) => p.dataset.pane).sort(),
    mdLines: document.querySelectorAll('#md-source .line').length,
    mdMarks: document.querySelectorAll('#md-source .mark').length,
    leanLines: document.querySelectorAll('#lean-source .line').length,
  }))()`);
  assert.deepEqual(dom.panes, ["infoview", "lean", "md", "pdf", "pdf-peer", "tex"]);
  assert.ok(dom.mdLines > 50, `expected the md pane to render many lines, got ${dom.mdLines}`);
  assert.ok(dom.mdMarks > 0, "renderSource should emit booklink .mark spans against the live sourcemap");
  assert.ok(dom.leanLines > 0, `expected the lean pane to render, got ${dom.leanLines} lines`);
});

test("Japanese Part I excerpt is selectable and renders its own PDF and mapped sources", async (t) => {
  assert.equal(
    await page.evaluate("document.querySelector('#book-select option[value=\"/polish-space-part1-ja\"]')?.textContent"),
    "日本語 · 第I部",
  );
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/polish-space-part1-ja/?v=1&pdfMode=full`);
  await tab.waitFor(READY, { timeout: 60000 });
  await tab.waitFor("document.querySelector('#pdf-viewer canvas')?.width > 0", { timeout: 30000 });
  assert.ok(await tab.evaluate("document.querySelectorAll('#md-source .mark').length > 0"));
  assert.ok(await tab.evaluate("document.querySelectorAll('#lean-source .line').length > 0"));
  const map = await tab.evaluate<any>("fetch('./build/polish-space-part1-ja-sourcemap.json').then(r=>r.json())");
  assert.ok(map.entries.length > 0);
  assert.equal(new Set(map.entries.map((entry: any) => entry.match.source)).size, 8);
  assert.ok(map.entries.every((entry: any) => entry.match.source.includes("/polish-space-part1-ja/build/source/")));
  assert.ok(map.entries.every((entry: any) => entry.texMatch.status === "matched"));
  const manifest = await tab.evaluate<any>("fetch('./manifest.json').then(r=>r.json())");
  assert.equal(Object.keys(manifest.chapterTitles).length, 8);
});

test("hides the peer-PDF pane option for a project with no parallel PDF", async () => {
  // polish-space has no parallelPdf, so the option must stay hidden: the pane it
  // toggles would never load anything. The `hidden` attribute alone is not
  // enough — `.vo-panels label { display: flex }` outranks the UA rule.
  const display = await page.evaluate<string>(
    `getComputedStyle(document.getElementById('pdf-peer-pane-option')).display`,
  );
  assert.equal(display, "none", "the English PDF option should be invisible without a parallel PDF");
});

test("connects the live SSE event stream and the LSP bridge to the server", async () => {
  // The static dist cannot reach these; only the live serve.ts serves /events.
  const events = await page.waitForRequest("/events?session=", 15000);
  assert.match(events, /\/events\?session=[0-9a-f-]+/i, "the page should open one multiplexed EventSource");
  const lspInfo = await page.waitForRequest("/lsp/info", 15000);
  assert.ok(lspInfo.includes("project=polish-space"), "the LSP handshake should target the served project");
});

test("the PDF pane renders pages to canvas via pdf.js", async () => {
  await page.waitFor(
    "document.querySelector('#pdf-viewer canvas') && document.querySelector('#pdf-viewer canvas').width > 0",
    { timeout: 30000 },
  );
  const canvas = await page.evaluate<{ width: number; height: number }>(`(() => {
    const c = document.querySelector('#pdf-viewer canvas');
    return { width: c.width, height: c.height };
  })()`);
  assert.ok(canvas.width > 0 && canvas.height > 0, `expected a rendered PDF canvas, got ${JSON.stringify(canvas)}`);
});

test("clicking a Lean line drives the live LSP bridge and renders a goal", async () => {
  // The text of all rendered goal panes, joined — empty when the infoview shows
  // the "No goals." / placeholder state (which has no `.infoview-goal` element).
  const goalText = `[...document.querySelectorAll('.infoview-goal')].map((g) => g.textContent).join('\\n--\\n')`;
  // Click a Lean line at real coordinates (positionFromPoint needs them) and
  // return the goal text shown immediately BEFORE the click — which is also what
  // queryGoalAt re-renders synchronously on click (it keeps the prior goal in
  // state until the async plainGoal returns, app.ts:1474-1486). The click also
  // bumps the goal token, so any earlier in-flight query is dropped (app.ts:1485);
  // the next change away from this returned value can therefore only be this
  // click's own response.
  //
  // A rendered-but-scrolled-off line still has positive height, but its viewport
  // coordinates fall outside the pane, where leanPositionFromPoint's
  // document.elementFromPoint misses it — so the click would issue no query and
  // not bump the token. Scroll the line to the pane centre first and click only
  // once its centre point is genuinely on-screen. Returns null if the line is
  // missing, folded away, or could not be brought on-screen.
  const clickLeanLine = (index: number) =>
    page.evaluate<string | null>(`(() => {
      const line = document.querySelectorAll('#lean-source .line')[${index}];
      if (!line) return null;
      line.scrollIntoView({ block: "center" });
      const r = line.getBoundingClientRect();
      const x = Math.floor(r.left + 8);
      const y = Math.floor(r.top + r.height / 2);
      if (r.height <= 0 || x < 0 || y < 0 || x >= innerWidth || y >= innerHeight) return null;
      // The point must actually resolve to this line (not a header/overlay), or
      // inspectLeanClick maps it elsewhere and no query for this line is issued.
      if (!line.contains(document.elementFromPoint(x, y))) return null;
      const before = ${goalText};
      line.dispatchEvent(new MouseEvent('click', { bubbles: true, clientX: x, clientY: y }));
      return before;
    })()`);

  // Wake the cold bridge: click the first visible line so the server spawns,
  // opens the document, and elaborates it, then wait for the handshake to settle.
  const firstVisible = await page.evaluate<number>(`(() => {
    const lines = document.querySelectorAll('#lean-source .line');
    for (let i = 0; i < lines.length; i++) if (lines[i].getBoundingClientRect().height > 0) return i;
    return -1;
  })()`);
  assert.ok(firstVisible >= 0, "expected a visible Lean line");
  await clickLeanLine(firstVisible);
  await page.waitFor("document.querySelector('#infoview-status').dataset.status === 'ready'", { timeout: 150000 });

  // Candidate positions, most-likely-to-have-an-open-goal first: the line right
  // after a `by` (the full goal is open at the first tactic), then other tactic
  // lines as a fallback. Document order keeps the cheap, early-in-file positions
  // first (less incremental elaboration to reach them).
  const candidates = await page.evaluate<number[]>(`(() => {
    const lines = [...document.querySelectorAll('#lean-source .line')];
    const visible = (el) => el && el.getBoundingClientRect().height > 0;
    const byStarts = [];
    const tactics = [];
    lines.forEach((line, i) => {
      if (!visible(line)) return;
      const text = line.textContent || "";
      if (/\\bby\\s*$/.test(text) && visible(lines[i + 1])) byStarts.push(i + 1);
      else if (/\\b(simp|exact|intro|intros|rw|refine|apply|constructor|obtain|rcases|cases|have|calc|show)\\b/.test(text)) tactics.push(i);
    });
    return [...new Set([...byStarts, ...tactics])];
  })()`);
  assert.ok(candidates.length > 0, "expected tactic lines in the Lean source");

  // For each candidate, capture the pre-click goal, then wait for the goal to
  // change to a non-empty value. Because the click dropped any in-flight query,
  // that change can only be this click's own plainGoal response — so a non-empty
  // goal different from `before` is the live round trip for the clicked position,
  // never the synchronous placeholder or a stale/earlier query's late arrival.
  let goal = "";
  const deadline = Date.now() + 90000;
  for (const index of candidates) {
    if (Date.now() > deadline) break;
    const before = await clickLeanLine(index);
    if (before === null) continue;
    try {
      await page.waitFor(
        `(() => { const g = ${goalText}; return g.length > 0 && g !== ${JSON.stringify(before)}; })()`,
        {
          timeout: 10000,
          interval: 250,
        },
      );
      goal = await page.evaluate<string>(goalText);
      break;
    } catch {
      // No fresh goal at this position; try the next one.
    }
  }
  assert.ok(goal.length > 0, "a live Lean goal should render in response to clicking a tactic position");
});

test("marker navigation activates an entry across the panes (cross-pane sync)", async () => {
  await page.evaluate(`document.querySelector('#next-entry').click()`);
  await page.waitFor("document.querySelector('.mark.active')", { timeout: 15000 });
  const first = await page.evaluate<string>(`document.querySelector('.mark.active').dataset.entry`);

  await page.evaluate(`document.querySelector('#next-entry').click()`);
  await page.waitFor(
    `document.querySelector('.mark.active') && document.querySelector('.mark.active').dataset.entry !== ${JSON.stringify(first)}`,
    {
      timeout: 15000,
    },
  );
  const second = await page.evaluate<string>(`document.querySelector('.mark.active').dataset.entry`);

  assert.notEqual(second, first, "advancing to the next marker should activate a different entry");
  const label = await page.evaluate<string>(`document.querySelector('#marker-field-label').textContent`);
  assert.notEqual(label.trim(), "—", "the marker field should show the active marker's title");
});

test("the custom dropdown filters its options by query", async () => {
  await page.evaluate(`document.querySelector('${MD_CONTROL} .cselect-field').click()`);
  await page.waitFor(`!document.querySelector('${MD_CONTROL} .cselect-popover').hidden`);
  const total = await page.evaluate<number>(`document.querySelectorAll('${MD_CONTROL} .cselect-option').length`);
  assert.ok(total > 3, `expected several chapter options, got ${total}`);

  await page.evaluate(`(() => {
    const search = document.querySelector('${MD_CONTROL} .cselect-search');
    search.value = 'borel';
    search.dispatchEvent(new Event('input', { bubbles: true }));
  })()`);
  await page.waitFor(`document.querySelectorAll('${MD_CONTROL} .cselect-option').length < ${total}`);

  const filtered = await page.evaluate<string[]>(
    `[...document.querySelectorAll('${MD_CONTROL} .cselect-option')].map((o) => o.textContent.toLowerCase())`,
  );
  assert.ok(filtered.length >= 1 && filtered.length < total, "the query should narrow the option list");
  assert.ok(
    filtered.every((label) => label.includes("borel")),
    `every filtered option should match the query, got ${JSON.stringify(filtered)}`,
  );
  await page.evaluate(
    `document.querySelector('${MD_CONTROL} .cselect-search').dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }))`,
  );
});

test("select carets stay at the right edge and vertically centered with short and long labels", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/`);
  await tab.waitFor(READY, { timeout: 30000 });
  const samples = await tab.evaluate<
    Array<{ width: number; label: string; verticalError: number; rightError: number; named: boolean }>
  >(`(async () => {
    const { enhanceSelect } = await import('./build/select-dropdown.js');
    const host = document.createElement('div');
    host.style.cssText = 'position:fixed;left:20px;top:20px;z-index:100';
    const select = document.createElement('select');
    select.setAttribute('aria-label', 'Document');
    const {setHTML}=await import('./build/safe-html.js');
    setHTML(select, '<option value="short">Chapter</option><option value="long">A very long chapter title that must be truncated inside a narrow PDF selector</option>');
    host.append(select);
    document.body.append(host);
    enhanceSelect(select);
    const samples = [];
    for (const width of [64, 160, 500]) {
      host.style.width = width + 'px';
      for (const value of ['short', 'long']) {
        select.value = value;
        const field = host.querySelector('.select-field');
        const rect = field.getBoundingClientRect();
        const caret = field.querySelector('.select-caret').getBoundingClientRect();
        const style = getComputedStyle(field);
        samples.push({ width, label: value,
          named: field.getAttribute('aria-label') === 'Document: ' + select.selectedOptions[0].textContent,
          verticalError: Math.abs(caret.top + caret.height / 2 - rect.top - rect.height / 2),
          rightError: Math.abs(caret.right - (rect.right - parseFloat(style.paddingRight) - parseFloat(style.borderRightWidth))),
        });
      }
    }
    host.remove();
    return samples;
  })()`);
  for (const sample of samples) {
    assert.ok(sample.named, JSON.stringify(sample));
    assert.ok(sample.verticalError < 1, JSON.stringify(sample));
    assert.ok(sample.rightError < 1, JSON.stringify(sample));
  }
  assert.equal(await tab.evaluate("document.querySelector('#pdf-mode-seg').getAttribute('role') === 'group' "), true);
});

test("Markdown HTML comments override TeX colors without treating code examples as comments", async () => {
  const comments = [
    "<!-- \\termuse{example} $x$ **bold** --> outside",
    "<!-- first line\n\\begin{proof} $x$\n--> outside",
    "日本語 😀 before <!-- inline $x$ --> after",
    "<!-- still open\n\\termuse{example} $x$",
  ];
  const literals = [
    "`<!-- inline code -->`",
    "```html\n<!-- fenced code -->\n```",
    "    <!-- indented code -->",
    "\\<!-- escaped opener -->",
    '<div title="<!-- attribute value -->">text</div>',
  ];
  const result = { comments: [] as boolean[], literals: [] as boolean[] };
  for (const text of comments) {
    const start = text.indexOf("<!--");
    const close = text.indexOf("-->", start);
    const end = close < 0 ? text.length : close + 3;
    const { spans } = await computeHighlightData(text, "markdown");
    result.comments.push(
      [...Array(end - start)].every((_, i) =>
        spans.some((s) => s.cls === "tok-comment" && s.startOffset <= start + i && s.endOffset > start + i),
      ) && spans.every((s) => s.cls !== "tok-comment" || s.endOffset <= end),
    );
  }
  for (const text of literals) {
    const { spans } = await computeHighlightData(text, "markdown");
    result.literals.push(!spans.some((s) => s.cls === "tok-comment"));
  }
  assert.ok(result.comments.every(Boolean), JSON.stringify(result));
  assert.ok(result.literals.every(Boolean), JSON.stringify(result));
});

test("choosing a different file in the dropdown switches the rendered source", async () => {
  await page.evaluate(`document.querySelector('${MD_CONTROL} .cselect-field').click()`);
  await page.waitFor(`!document.querySelector('${MD_CONTROL} .cselect-popover').hidden`);

  // Click the first option whose native value differs from the current file.
  const chosen = await page.evaluate<string | null>(`(() => {
    const pane = document.querySelector('${MD_CONTROL}');
    const select = pane.querySelector('select');
    const current = select.value;
    for (const option of pane.querySelectorAll('.cselect-option')) {
      const value = select.options[Number(option.dataset.i)].value;
      if (value !== current) {
        option.click();
        return value;
      }
    }
    return null;
  })()`);
  assert.ok(chosen, "expected a different file to choose");

  await page.waitFor(`document.querySelector('#md-select').value === ${JSON.stringify(chosen)}`, { timeout: 15000 });
  await page.waitFor("document.querySelectorAll('#md-source .line').length > 0", { timeout: 15000 });
  const value = await page.evaluate<string>(`document.querySelector('#md-select').value`);
  assert.equal(value, chosen, "selecting an option should drive the native select and re-render the source");
});

// Runs last and on its own pages: it opens fresh tabs, which must not disturb
// the shared page the tests above navigate.
test("the reading position round-trips through the URL and the stored session", async (t) => {
  const before = await page.evaluate<number>("import('./build/state.js').then(({state})=>state.activeIndex)");
  const next = before + 1;
  const expectedMarker = await page.evaluate<string>(`(async () => {
    const appUrl = document.querySelector('script[type="module"]').src;
    const [{ markerId }, { state }] = await Promise.all([
      import(new URL('permalink.js', appUrl).href),
      import(new URL('state.js', appUrl).href),
    ]);
    return markerId(state.entries, ${next});
  })()`);
  await page.evaluate(`document.querySelector('#next-entry').click()`);
  await page.waitFor(`document.querySelector('.mark.active')?.dataset.entry === ${JSON.stringify(String(next))}`, {
    timeout: 15000,
  });
  // A prior navigation may still publish its trailing URL update after this
  // click. Wait for this marker, rather than merely any change from the old URL.
  await page.waitFor(`new URLSearchParams(location.search).get("marker") === ${JSON.stringify(expectedMarker)}`, {
    timeout: 15000,
  });
  const shared = await page.evaluate<{ url: string; entry: string }>(`(() => ({
    url: location.href,
    entry: document.querySelector('.mark.active').dataset.entry,
  }))()`);
  // The id is the Lean declaration name, not the entry index that shifts on
  // every rebuild.
  const marker = new URL(shared.url).searchParams.get("marker") ?? "";
  assert.equal(marker, expectedMarker);
  assert.match(marker, /^[A-Za-z_@][\w.'!?~]*$/, `expected a declaration-derived id, got ${JSON.stringify(marker)}`);

  // A copied link reopens the same marker in a fresh tab.
  const linked = await browser.newPage();
  t.after(() => linked.close());
  await linked.navigate(shared.url);
  await linked.waitFor(READY, { timeout: 30000 });
  const linkedEntry = await linked.evaluate<string>(`document.querySelector('.mark.active').dataset.entry`);
  assert.equal(linkedEntry, shared.entry, "?marker= should reopen the marker the link was copied from");

  // With no marker in the URL, the stored session restores the same place.
  const resumed = await browser.newPage();
  t.after(() => resumed.close());
  await resumed.navigate(`${server.baseUrl}/`);
  await resumed.waitFor(READY, { timeout: 30000 });
  const resumedEntry = await resumed.evaluate<string>(`document.querySelector('.mark.active').dataset.entry`);
  assert.equal(resumedEntry, shared.entry, "a plain reload should resume at the stored marker");
  // The restore navigates like any other, so the address bar catches up with it
  // on the same trailing timer.
  await resumed.waitFor("new URLSearchParams(location.search).get('marker')", { timeout: 15000 });
  const resumedMarker = await resumed.evaluate<string | null>(`new URLSearchParams(location.search).get('marker')`);
  assert.equal(resumedMarker, marker, "the restored position should be written back to the address bar");
});

test("splitters resize with the keyboard and report the new boundary", async () => {
  const result = await page.evaluate<{ before: number; after: number; role: string }>(`(() => {
    const splitter = document.querySelector('.splitter');
    const before = Number(splitter.getAttribute('aria-valuenow'));
    splitter.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowRight', bubbles: true }));
    return { before, after: Number(splitter.getAttribute('aria-valuenow')), role: splitter.getAttribute('role') };
  })()`);
  assert.equal(result.role, "separator");
  assert.ok(result.after > result.before);
});

test("pointer-opened selectors browse without text input while keyboard opening enters search", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=md`);
  await tab.waitFor(READY, { timeout: 30000 });
  for (const [field, list, search, pop] of [
    ["#marker-field", "#marker-list", "#marker-search", "#marker-popover"],
    [
      "#md-document-control .cselect-field",
      "#md-document-control .cselect-list",
      "#md-document-control .cselect-search",
      "#md-document-control .cselect-popover",
    ],
  ]) {
    const active = (selector: string) =>
      tab.evaluate(`document.activeElement===document.querySelector(${JSON.stringify(selector)})`);
    await tab.click(field);
    assert.equal(await active(list), true, "pointer opening focuses a non-editable list");
    assert.ok(
      (await tab.evaluate<number>(
        `parseFloat(getComputedStyle(document.querySelector(${JSON.stringify(search)})).fontSize)`,
      )) >= 16,
    );
    await tab.click(search);
    assert.equal(await active(search), true, "an explicit search-field click starts input");
    await tab.pressKey("Escape");
    await tab.pressKey("Enter");
    assert.equal(await active(search), true, "keyboard opening starts in search");
    await tab.pressKey("Escape");
    await tab.click(field);
    await tab.pressKey("b");
    assert.equal(await active(search), true);
    assert.equal(
      await tab.evaluate(`document.querySelector(${JSON.stringify(search)}).value`),
      "b",
      "the first typed character is retained once",
    );
    await tab.pressKey("Escape");
    await tab.click(field);
    const first = await tab.evaluate(
      `document.querySelector(${JSON.stringify(list)}).getAttribute('aria-activedescendant')`,
    );
    await tab.pressKey("ArrowDown");
    assert.equal(await active(list), true, "arrows browse without entering text input");
    assert.notEqual(
      await tab.evaluate(`document.querySelector(${JSON.stringify(list)}).getAttribute('aria-activedescendant')`),
      first,
    );
    await tab.pressKey("Enter");
    assert.equal(await tab.evaluate(`document.querySelector(${JSON.stringify(pop)}).hidden`), true);
    assert.equal(await active(field), true);
  }
});

test("marker and select search identify the active option to assistive technology", async () => {
  const result = await page.evaluate<boolean>(`(() => {
    document.querySelector('#marker-field').click();
    const search = document.querySelector('#marker-search');
    const id = search.getAttribute('aria-activedescendant');
    const valid = !!id && document.getElementById(id)?.getAttribute('role') === 'option';
    search.dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }));
    document.querySelector('${MD_CONTROL} .cselect-field').click();
    const selectSearch = document.querySelector('${MD_CONTROL} .cselect-search');
    selectSearch.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowDown', bubbles: true }));
    const selectedId = selectSearch.getAttribute('aria-activedescendant');
    const selected = !!selectedId && document.getElementById(selectedId)?.classList.contains('is-highlight');
    selectSearch.dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }));
    return valid && selected;
  })()`);
  assert.equal(result, true);
});

test("selection, scroll synchronization and URL use one location even when navigation finishes out of order", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/`);
  await tab.waitFor(READY, { timeout: 30000 });
  const expected = await tab.evaluate<string>(`(async () => {
    const { state } = await import('./build/state.js');
    const { setActive, setActivateHook } = await import('./build/sync.js');
    const { markerId } = await import('./build/permalink.js');
    state.sync = false;
    let release;
    const blocked = new Promise(resolve => release = resolve);
    window.completedNavigations = [];
    setActivateHook(async (index, origin, mode, current) => {
      if (index === 0) await blocked;
      if (current()) window.completedNavigations.push(index);
    });
    const slow = setActive(0);
    await setActive(1);
    release();
    await slow;
    window.navigationState = state;
    return markerId(state.entries, 1);
  })()`);
  await tab.waitFor(`new URLSearchParams(location.search).get('marker') === ${JSON.stringify(expected)}`);
  const result = await tab.evaluate<{ index: number; location: unknown; completed: number[] }>(`({
    index: window.navigationState.activeIndex,
    location: window.navigationState.location,
    completed: window.completedNavigations,
  })`);
  assert.deepEqual(result, { index: 1, location: { kind: "entry", index: 1 }, completed: [1] });
  const skipped = await tab.evaluate<string | null>(`(async () => {
    const { state } = await import('./build/state.js');
    const { setSkipActive } = await import('./build/sync.js');
    const key = state.skips[0]?.key;
    if (!key) return null;
    await setSkipActive({ key, progress: 0.4 });
    return key;
  })()`);
  if (skipped) {
    await tab.waitFor(`new URLSearchParams(location.search).get('skip') === ${JSON.stringify(skipped)}`);
    assert.equal(await tab.evaluate("window.navigationState.activeIndex"), -1);
    assert.equal(await tab.evaluate("document.querySelector('.mark.active') !== null"), false);
  }
});

test("rebuild notifications and browser reload retain the URL-relative reading position", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/?v=1&pdfMode=full&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(`(async () => {
    const { state, els } = await import('./build/state.js');
    const { setActive } = await import('./build/sync.js');
    await state.pdf.targetPromise;
    state.sync = false;
    localStorage.setItem('formalization-viewer-scroll-sync', 'off');
    const index = [...state.pdf.targets.keys()].find(i => state.pdf.targets.get(i).pageNumber > 5);
    if (index === undefined) throw new Error('No mapped PDF passage');
    await setActive(index, null, true);
    window.expectedReadingMarker = (await import('./build/permalink.js')).markerId(state.entries, index);
    els.pdfViewer.scrollTop += 37;
    els.mdSource.scrollTop += 23;
    window.readingState = state;
    window.readingEls = els;
    window.oldPdfToken = state.pdf.renderToken;
    window.oldMdLine = els.mdSource.firstChild;
  })()`);
  await tab.waitFor("new URLSearchParams(location.search).get('marker') === window.expectedReadingMarker");
  const snapshot = () =>
    tab.evaluate<{ url: string; page: number; fraction: number; md: number }>(`(async () => {
    const { state, els } = await import('./build/state.js');
    const { capturePdfScrollAnchor } = await import('./build/pdf.js');
    const anchor = capturePdfScrollAnchor();
    return { url: location.href, page: anchor.pageNumber, fraction: anchor.fraction, md: els.mdSource.scrollTop };
  })()`);
  const before = await snapshot();
  await tab.evaluate(`(async () => {
    const { eventStream } = await import('./build/event-stream.js');
    for (const path of [
      'polish-space/build/polish-space-book-debug.tex',
      'polish-space/build/polish-space-book-sourcemap.json',
      'polish-space/build/polish-space-book-debug.pdf',
    ]) eventStream.source.dispatchEvent(new MessageEvent('watch', { data: JSON.stringify({ path }) }));
  })()`);
  await tab.waitFor(
    `window.readingState.pdf.renderToken > window.oldPdfToken &&
    window.readingState.pdf.document && window.readingState.pdf.targetPromise &&
    window.readingEls.mdSource.firstChild !== window.oldMdLine`,
    { timeout: 30000 },
  );
  await tab.evaluate("window.readingState.pdf.targetPromise");
  const rebuilt = await snapshot();
  assert.equal(rebuilt.url, before.url);
  assert.equal(rebuilt.page, before.page);
  assert.ok(Math.abs(rebuilt.fraction - before.fraction) < 0.02);
  assert.ok(Math.abs(rebuilt.md - before.md) < 4);
  await tab.evaluate("window.beforeReadingReload = true; setTimeout(() => location.reload(), 0)");
  await tab.waitFor("!window.beforeReadingReload && document.body.dataset.viewerReady === '1'", { timeout: 30000 });
  const reloaded = await snapshot();
  assert.equal(reloaded.url, before.url);
  assert.equal(reloaded.page, before.page);
  assert.ok(Math.abs(reloaded.fraction - before.fraction) < 0.02);
  assert.ok(Math.abs(reloaded.md - before.md) < 4);
});

test("definition previews identify the term and PDF jumps briefly highlight the destination", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/?v=1&pdfMode=full&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.waitFor("document.querySelector('#pdf-viewer .pdf-term-link[data-definition^=\"term-def-\"]')", {
    timeout: 20000,
  });
  await tab.evaluate(`(async () => {
    const { state } = await import('./build/state.js');
    await state.pdf.targetPromise;
    state.sync=false;
    document.body.classList.add('marks-off');
  })()`);
  // Hiding the marker rail changes the PDF width; select a fresh text link
  // after that repaint, rather than an anchor from the discarded text layer.
  await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
  await tab.waitFor(`(async () => {
    const { state } = await import('./build/state.js');
    return !state.pdf.repaintTimer && [...state.pdf.pageStates.values()].every(page => !page.rendering);
  })()`);
  await tab.evaluate(`(async () => {
    const { state } = await import('./build/state.js');
    await state.pdf.targetPromise;
    state.sync = false;
    document.body.classList.add('marks-off');
    document.body.classList.remove('links-on');
    for (const anchor of document.querySelectorAll('#pdf-viewer .pdf-term-link[data-definition^="term-def-"]')) {
      if (!await state.pdf.document.getDestination(anchor.dataset.definition)) continue;
      anchor.id = 'definition-cue-test';
      anchor.scrollIntoView({ block: 'center' });
      return;
    }
    throw new Error('No linked definition');
  })()`);
  // Let scroll events from bringing the link into view finish before hovering.
  await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
  await tab.evaluate("document.querySelector('#definition-cue-test').dispatchEvent(new MouseEvent('mouseenter'))");
  await tab.waitFor("document.querySelector('.term-preview-source')", { timeout: 20000 });
  assert.ok(await tab.evaluate("document.querySelector('.term-preview-source').textContent.trim().length > 0"));
  assert.equal(await tab.evaluate("document.querySelector('.term-preview-body canvas')"), null);
  await tab.evaluate("document.querySelector('#definition-cue-test').click()");
  await tab.waitFor("document.querySelector('#pdf-viewer .pdf-destination-highlight.is-transient')", {
    timeout: 20000,
  });
  const visible = await tab.evaluate<boolean>(`(() => {
    const mark = document.querySelector('#pdf-viewer .pdf-destination-highlight').getBoundingClientRect();
    const pane = document.querySelector('#pdf-viewer').getBoundingClientRect();
    return mark.bottom > pane.top && mark.top < pane.bottom && mark.right > pane.left && mark.left < pane.right;
  })()`);
  assert.equal(visible, true, "the destination cue should be in the visible part of the PDF");
  await tab.waitFor("!document.querySelector('#pdf-viewer .pdf-destination-highlight')", { timeout: 4000 });
});

test("touch term links preview before navigating and dismiss without changing the reading position", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/?v=1&layout=pdf&pdfMode=full&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.waitFor("document.querySelector('#pdf-viewer .pdf-term-link')", { timeout: 20000 });
  await tab.evaluate(`(async () => {
    const { state } = await import('./build/state.js');
    await state.pdf.targetPromise;
    state.sync=false;
    document.body.classList.add('marks-off');
  })()`);
  // Hiding the marker rail changes the PDF width; select a fresh text link
  // after that repaint, rather than an anchor from the discarded text layer.
  await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
  await tab.waitFor(`(async () => {
    const { state } = await import('./build/state.js');
    return !state.pdf.repaintTimer && [...state.pdf.pageStates.values()].every(page => !page.rendering);
  })()`);
  await tab.evaluate(`(async () => {
    const { state } = await import('./build/state.js');
    await state.pdf.targetPromise;
    state.sync = false;
    document.body.classList.add('marks-off');
    for (const anchor of document.querySelectorAll('#pdf-viewer .pdf-term-link')) {
      if (!await state.pdf.document.getDestination(anchor.dataset.definition)) continue;
      anchor.id = 'touch-term-test';
      anchor.scrollIntoView({ block: 'center' });
      return;
    }
    throw new Error('No linked definition');
  })()`);
  await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
  const position = () => tab.evaluate("document.querySelector('#pdf-viewer').scrollTop");
  const before = await position();
  await tab.tap("#touch-term-test");
  await tab.waitFor("document.querySelector('.term-definition-preview[role=dialog] .term-preview-source')", {
    timeout: 20000,
  });
  assert.equal(await position(), before, "a tap must not follow the PDF link");
  assert.ok(
    await tab.evaluate(`(() => {
    const r = document.querySelector('.term-definition-preview').getBoundingClientRect();
    return r.left >= 0 && r.right <= innerWidth && r.top >= 0 && r.bottom <= innerHeight;
  })()`),
    "the preview and actions fit on a phone",
  );
  // Compatibility mouse events and focus changes must not close a touch preview.
  await tab.evaluate(`document.querySelector('#touch-term-test').dispatchEvent(new MouseEvent('mouseleave'));
    document.querySelector('#touch-term-test').dispatchEvent(new FocusEvent('blur'));`);
  await tab.evaluate("new Promise(resolve => setTimeout(resolve, 350))");
  assert.ok(await tab.evaluate("!!document.querySelector('.term-definition-preview')"));
  await tab.tap(".term-preview-actions button:last-child");
  assert.equal(await tab.evaluate("!!document.querySelector('#term-link-popup')"), false);
  assert.equal(await position(), before);
  await tab.evaluate(`(() => {
    const anchor = document.querySelector('#touch-term-test');
    anchor.dispatchEvent(new PointerEvent('pointerdown', { pointerType: 'touch', bubbles: true }));
    anchor.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true, detail: 1 }));
  })()`);
  assert.ok(await tab.evaluate("!!document.querySelector('.term-definition-preview[role=dialog]')"));
  assert.equal(await position(), before, "Safari's compatibility click must also preview without navigating");
  await tab.tap("#settings-toggle");
  await tab.waitFor("!document.querySelector('#term-link-popup')");
  await tab.tap("#settings-toggle");
  await tab.tap("#touch-term-test");
  await tab.waitFor("document.querySelector('.term-preview-actions button:first-child:not(:disabled)')");
  await tab.tap(".term-preview-actions button:first-child");
  await tab.waitFor("document.querySelector('#pdf-viewer .pdf-destination-highlight.is-transient')", {
    timeout: 20000,
  });
  assert.equal(await tab.evaluate("!!document.querySelector('#term-link-popup')"), false);
});

test("narrow toolbars hide arrows, shorten the marker, and wrap only as a last resort", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(1000, 700);
  await tab.navigate(`${server.baseUrl}/`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(`(() => {
    document.querySelector('#marker-field-label').textContent = 'Parameterized lambda recursion';
  })()`);
  const samples: Array<{
    width: number;
    arrows: boolean;
    wrapped: boolean;
    marker: number;
    height: number;
  }> = [];
  for (const width of [1000, 430, 390, 280, 200]) {
    await tab.setViewport(width, 700);
    await tab.evaluate("new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)))");
    samples.push(
      await tab.evaluate(`(() => {
      const toolbar = document.querySelector('.toolbar');
      return { width: innerWidth, arrows: getComputedStyle(document.querySelector('#prev-entry')).display !== 'none',
        wrapped: document.querySelector('#marker-combo').getBoundingClientRect().top >= document.querySelector('#settings-toggle').getBoundingClientRect().bottom, height: toolbar.getBoundingClientRect().height,
        marker: document.querySelector('#marker-combo').getBoundingClientRect().width };
    })()`),
    );
  }
  assert.equal(samples[0].arrows, true, JSON.stringify(samples));
  assert.equal(samples[1].arrows, false, JSON.stringify(samples));
  assert.ok(samples[2].marker < samples[1].marker, JSON.stringify(samples));
  assert.ok(samples[3].marker < samples[2].marker, JSON.stringify(samples));
  assert.ok(
    samples.slice(0, 4).every((s) => !s.wrapped && s.height < 60),
    JSON.stringify(samples),
  );
  assert.equal(samples[4].wrapped, true, JSON.stringify(samples));
});

test("readable v1 layout URLs retain nested ratios and focus across reload and marker navigation", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument("localStorage.setItem('formalization-viewer-scroll-sync','off')");
  await tab.navigate(
    `${server.baseUrl}/polish-space/?v=1&layout=row(pdf:3,col(md,lean):2)&focus=md&marker=closed_subspace_polish`,
  );
  await tab.waitFor(READY, { timeout: 30000 });
  const snapshot = () =>
    tab.evaluate(`(async()=>{
    const {state}=await import('./build/state.js');
    return {tree:state.layout.tree,focus:state.layout.maximized,url:location.search,
      visible:[...document.querySelectorAll('.pane')].filter(p=>!p.hidden).map(p=>p.dataset.pane)};
  })()`);
  const initial = (await snapshot()) as { tree: unknown; focus: string; url: string; visible: string[] };
  assert.deepEqual(initial.tree, {
    dir: "row",
    children: [{ pane: "pdf" }, { dir: "col", children: [{ pane: "md" }, { pane: "lean" }], ratios: [1, 1] }],
    ratios: [3, 2],
  });
  assert.equal(initial.focus, "md");
  assert.deepEqual(initial.visible, ["md"]);
  assert.ok(initial.url.includes("layout=row(pdf:3,col(md,lean):2)"), initial.url);
  await tab.evaluate("window.compactReload=true;setTimeout(()=>location.reload(),0)");
  await tab.waitFor("!window.compactReload && document.body.dataset.viewerReady==='1'", { timeout: 30000 });
  assert.deepEqual(await snapshot(), initial);
  await tab.evaluate("document.querySelector('#next-entry').click()");
  await tab.waitFor("new URLSearchParams(location.search).get('marker')!=='closed_subspace_polish'");
  assert.equal(await tab.evaluate("location.search.includes('layout=row(pdf:3,col(md,lean):2)')"), true);
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  await tab.waitFor("!new URLSearchParams(location.search).has('focus')");
  assert.equal(await tab.evaluate("location.search.includes('layout=row(pdf:3,col(md,lean):2)')"), true);
});

test("layout URLs override storage while local appearance applies before asynchronous startup", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    localStorage.setItem('formalization-viewer-appearance-mode', 'dark');
    localStorage.setItem('formalization-viewer-code-font', 'monaco');
    localStorage.setItem('formalization-viewer-layout-v2', JSON.stringify({tree:{pane:'lean'}}));
    const fetchOriginal = window.fetch.bind(window);
    window.fetch = (input, options) => String(input) === 'manifest.json'
      ? new Promise(resolve => window.releaseViewerManifest = () => resolve(fetchOriginal(input, options)))
      : fetchOriginal(input, options);
  `);
  const layout = { tree: { dir: "row", children: [{ pane: "md" }, { pane: "tex" }], ratios: [3, 1] } };
  const params = new URLSearchParams({ v: "1", layout: JSON.stringify(layout) });
  await tab.navigate(`${server.baseUrl}/?${params}`);
  await tab.waitFor("typeof window.releaseViewerManifest === 'function'");
  const early = await tab.evaluate<{ theme: string; visibility: string; font: string; ready: string | undefined }>(`({
    theme: document.documentElement.dataset.theme,
    visibility: getComputedStyle(document.querySelector('.workspace')).visibility,
    font: getComputedStyle(document.documentElement).getPropertyValue('--code-font'),
    ready: document.body.dataset.viewerReady,
  })`);
  assert.equal(early.theme, "dark");
  assert.match(early.font, /Monaco/);
  assert.equal(early.visibility, "hidden");
  assert.equal(early.ready, undefined);
  assert.equal(await tab.evaluate("document.querySelector('[data-startup-step=manifest]').dataset.state"), "working");
  assert.match(await tab.evaluate<string>("document.querySelector('#startup-detail').textContent"), /book settings/i);
  assert.equal(await tab.evaluate("document.querySelector('#startup-progress').value"), 0);
  await tab.evaluate("window.releaseViewerManifest()");
  await tab.waitFor(READY, { timeout: 30000 });
  assert.deepEqual(
    await tab.evaluate(
      "[...document.querySelectorAll('.workspace > .split .pane:not([hidden])')].map(p=>p.dataset.pane)",
    ),
    ["md", "tex"],
  );
  assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('.workspace')).visibility"), "visible");
  const before = await tab.evaluate<string>("location.search");
  await tab.evaluate(
    "document.querySelector('#code-font').value='menlo';document.querySelector('#code-font').dispatchEvent(new Event('change'))",
  );
  assert.equal(await tab.evaluate("location.search"), before, "font preferences belong only to local storage");
  assert.equal(await tab.evaluate("new URLSearchParams(location.search).has('theme')"), false);
});

test("build logs keep a running cue at the end and remove it when the build stops", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    const NativeWebSocket = window.WebSocket;
    window.WebSocket = class extends NativeWebSocket {
      constructor(...args) {
        super(...args);
        if (String(args[0]).includes('/build/log')) {
          window.testBuildLogSocket = this;
          this.addEventListener('message', () => window.receivedBuildLog = true, { once: true });
        }
      }
    };
  `);
  await tab.navigate(`${server.baseUrl}/`);
  await tab.waitFor(READY, { timeout: 30000 });
  const status = (state: string) =>
    tab.evaluate(`(async () => {
    const { eventStream } = await import('./build/event-stream.js');
    const { project } = await import('./build/state.js');
    eventStream.source.dispatchEvent(new MessageEvent('build', {
      data: JSON.stringify({ dir: project.dir, state: ${JSON.stringify(state)} }),
    }));
  })()`);
  const output = (text: string, reset = false) =>
    tab.evaluate(`window.testBuildLogSocket.dispatchEvent(new MessageEvent('message', {
    data: JSON.stringify(${JSON.stringify({ text, reset })}),
  }))`);
  await status("building");
  await tab.evaluate("document.querySelector('#pdf-build-status').click()");
  await tab.waitFor("window.receivedBuildLog && document.querySelector('.build-log-progress:not([hidden])')");
  await output("First line\nPartial", true);
  await output(" output");
  assert.equal(
    await tab.evaluate("document.querySelector('.build-log-text').textContent"),
    "First line\nPartial output",
  );
  assert.equal(
    await tab.evaluate("document.querySelector('.build-log-dialog pre').lastElementChild.className"),
    "build-log-progress",
  );
  await output("line\n".repeat(300), true);
  await tab.evaluate("document.querySelector('.build-log-dialog pre').scrollTop = 0");
  await output("More output\n");
  assert.equal(await tab.evaluate("document.querySelector('.build-log-dialog pre').scrollTop"), 0);
  await status("done");
  await tab.waitFor("document.querySelector('.build-log-progress').hidden");
  await status("building");
  await tab.waitFor("!document.querySelector('.build-log-progress').hidden");
  await status("failed");
  await tab.waitFor("document.querySelector('.build-log-progress').hidden");
  await tab.evaluate("document.querySelector('.build-log-close').click()");
  await tab.waitFor("!document.querySelector('.build-log-dialog')");
});

test("PDF mode is global, defaults to chapter, and URL-owned settings never revive local copies", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    if (!sessionStorage.getItem('seed-url-default-test')) {
      sessionStorage.setItem('seed-url-default-test', '1');
      localStorage.setItem('formalization-viewer-layout-v2', JSON.stringify({tree:{pane:'lean'}}));
      localStorage.setItem('formalization-viewer-pdf-mode', 'full');
      localStorage.setItem('formalization-viewer-session-v1:/polish-space', JSON.stringify({pdf:'/polish-space/build/polish-space-book-debug.pdf',marker:'@0'}));
    }
  `);
  await tab.navigate(`${server.baseUrl}/polish-space/`);
  await tab.waitFor(READY, { timeout: 30000 });
  const snapshot = () =>
    tab.evaluate<{
      mode: string;
      path: string;
      layoutParam: boolean;
      modeParam: string | null;
      localLayout: string | null;
      localMode: string | null;
      sessionPdf: unknown;
      inSettings: boolean;
      inHeader: boolean;
    }>(`(async () => {
    const {state}=await import('./build/state.js');
    const params=new URLSearchParams(location.search);
    return {mode:state.pdfMode,path:state.pdf.path,layoutParam:params.has('layout'),modeParam:params.get('pdfMode'),
      localLayout:localStorage.getItem('formalization-viewer-layout-v2'),localMode:localStorage.getItem('formalization-viewer-pdf-mode'),
      sessionPdf:JSON.parse(localStorage.getItem('formalization-viewer-session-v1:/polish-space')||'{}').pdf,
      inSettings:!!document.querySelector('#settings-menu #pdf-mode-seg'),inHeader:!!document.querySelector('.pane-header #pdf-mode-seg')};
  })()`);
  const initial = await snapshot();
  assert.equal(initial.mode, "chapter");
  assert.match(initial.path, /-preview-/);
  assert.equal(initial.modeParam, null);
  assert.equal(initial.layoutParam, false);
  assert.equal(initial.localLayout, null);
  assert.equal(initial.localMode, null);
  assert.equal(initial.sessionPdf, undefined);
  assert.equal(initial.inSettings, true);
  assert.equal(initial.inHeader, false);
  assert.equal(
    await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=chapter]').getAttribute('aria-pressed')"),
    "true",
  );
  await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=full]').click()");
  await tab.waitFor("new URLSearchParams(location.search).get('pdfMode')==='full'");
  assert.equal(
    await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=full]').getAttribute('aria-pressed')"),
    "true",
  );
  assert.equal(
    await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=chapter]').getAttribute('aria-pressed')"),
    "false",
  );
  assert.equal((await snapshot()).localMode, null);
  await tab.evaluate("window.modeReload=true;setTimeout(()=>location.reload(),0)");
  await tab.waitFor("!window.modeReload && document.body.dataset.viewerReady==='1'", { timeout: 30000 });
  assert.equal((await snapshot()).mode, "full");
  await tab.evaluate(
    "document.querySelector('#book-select').value='/polish-space-ja';document.querySelector('#book-select').dispatchEvent(new Event('change'))",
  );
  await tab.waitFor("location.pathname==='/polish-space-ja/' && document.body.dataset.viewerReady==='1'", {
    timeout: 45000,
  });
  assert.equal((await snapshot()).mode, "full");
  assert.equal(await tab.evaluate("document.querySelector('#pdf-peer-link').href.includes('-preview-')"), false);
  await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=chapter]').click()");
  await tab.waitFor("!new URLSearchParams(location.search).has('pdfMode')");
  assert.equal((await snapshot()).mode, "chapter");
  assert.equal(await tab.evaluate("document.querySelector('#pdf-peer-link').href.includes('-preview-')"), true);
  await tab.evaluate(`(() => {
    const url=new URL(location.href);url.searchParams.delete('layout');url.searchParams.delete('pdfMode');
    history.replaceState(null,'',url);window.modeReload=true;setTimeout(()=>location.reload(),0);
  })()`);
  await tab.waitFor("!window.modeReload && document.body.dataset.viewerReady==='1'", { timeout: 45000 });
  assert.equal((await snapshot()).mode, "chapter");
  assert.equal((await snapshot()).layoutParam, false);
});

test("chapter edge pulls navigate both PDFs, require intent, and support touch release", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(
    "window.viewerErrors=[];const originalError=console.error;console.error=(...args)=>{window.viewerErrors.push(args.map(String).join(' '));originalError(...args)}",
  );
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-appearance-mode','light');localStorage.setItem('formalization-viewer-scroll-sync','on')",
  );
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 45000 });
  await tab.evaluate(
    "import('./build/state.js').then(({state})=>{window.pullState=state;return state.pdf.targetPromise})",
  );
  await tab.waitFor("document.querySelector('#pdf-peer-viewer .pdf-page')", { timeout: 30000 });
  const wheel = (pane: string, delta: number) =>
    tab.evaluate(
      `document.querySelector(${JSON.stringify(pane)}).dispatchEvent(new WheelEvent('wheel',{deltaY:${delta},bubbles:true,cancelable:true}))`,
    );
  const pauseGesture = () => tab.evaluate("new Promise(resolve=>setTimeout(resolve,260))");
  const original = await tab.evaluate<string>("window.pullState.pdf.path");
  assert.match(original, /-preview-preface\.pdf$/);
  // Contents precedes the preface in the selector without becoming the default.
  assert.match(
    await tab.evaluate<string>("document.querySelector('#pdf-select').options[0].value"),
    /-preview-_contents\.pdf$/,
  );
  // Ordinary scrolling into the bottom does not turn.
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=100");
  await wheel("#pdf-viewer", 150);
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=1e9");
  await wheel("#pdf-viewer", 150);
  assert.equal(await tab.evaluate("window.pullState.pdf.path"), original);
  await pauseGesture();
  await wheel("#pdf-viewer", 40);
  assert.equal(await tab.evaluate("document.querySelector('[data-pane=pdf] .chapter-pull').hidden"), false);
  assert.match(
    await tab.evaluate<string>("document.querySelector('[data-pane=pdf] .chapter-pull').textContent"),
    /next chapter/,
  );
  await wheel("#pdf-viewer", 80);
  await tab.waitFor(
    "window.pullState.pdf.path.endsWith('-preview-polish-spaces.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.evaluate("window.pullState.pdf.targetPromise");
  await tab.waitFor(
    "window.pullState.selectedSources.md.endsWith('/polish-spaces.md') && document.querySelector('#pdf-viewer').scrollTop<=2",
    { timeout: 15000 },
  );
  await tab.waitFor(
    "document.querySelector('#pdf-peer-link').href.includes('-preview-polish-spaces.pdf') && document.querySelector('#pdf-peer-viewer .pdf-page') && document.querySelector('#pdf-peer-viewer').scrollTop<=2",
    { timeout: 30000 },
  );
  assert.equal(await tab.evaluate("document.querySelector('#pdf-peer-viewer').scrollTop<=2"), true);
  // Returning from the peer's top lands both panes at the previous chapter's end.
  await pauseGesture();
  await wheel("#pdf-peer-viewer", -150);
  await tab.waitFor(
    "window.pullState.pdf.path.endsWith('-preview-preface.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.evaluate("window.pullState.pdf.targetPromise");
  await tab.waitFor(
    "[...document.querySelectorAll('.pdf-viewer')].every(v=>v.querySelector('.pdf-page') && v.scrollHeight-v.clientHeight-v.scrollTop<3)",
    { timeout: 30000 },
  );
  const touch = (type: string, y: number) =>
    tab.evaluate(`(() => {
    const viewer=document.querySelector('#pdf-viewer');
    const point=new Touch({identifier:1,target:viewer,clientX:100,clientY:${y}});
    viewer.dispatchEvent(new TouchEvent('${type}',{touches:${type === "touchend" || type === "touchcancel" ? "[]" : "[point]"},changedTouches:[point],bubbles:true,cancelable:true}));
  })()`);
  await touch("touchstart", 200);
  await touch("touchmove", 60);
  assert.equal(await tab.evaluate("window.pullState.pdf.path"), original, "touch pulls wait for release");
  await touch("touchcancel", 60);
  assert.equal(await tab.evaluate("window.pullState.pdf.path"), original, "cancelled touches do not navigate");
  await touch("touchstart", 200);
  await touch("touchmove", 60);
  await touch("touchend", 60);
  await tab.waitFor(
    "window.pullState.pdf.path.endsWith('-preview-polish-spaces.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  // Whole-book mode keeps ordinary scrolling even at an edge.
  await tab.evaluate("window.pullState.pdf.targetPromise");
  await tab.evaluate("document.querySelector('#pdf-mode-seg [data-value=full]').click()");
  await tab.waitFor("window.pullState.pdfMode==='full' && document.querySelector('#pdf-viewer .pdf-page')", {
    timeout: 30000,
  });
  const full = await tab.evaluate("window.pullState.pdf.path");
  await pauseGesture();
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=1e9");
  await wheel("#pdf-viewer", 500);
  assert.equal(await tab.evaluate("window.pullState.pdf.path"), full);
});

test("a chapter pull retains its end landing while the requested PDF is still being built", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-appearance-mode','light');localStorage.setItem('formalization-viewer-scroll-sync','off')",
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(
    "import('./build/state.js').then(({state})=>{window.pullState=state;return state.pdf.targetPromise})",
  );
  assert.equal(await tab.evaluate("window.pullState.pdf.path.endsWith('-preview-polish-spaces.pdf')"), true);
  await tab.evaluate(`(() => {
    window.nativePullFetch=window.fetch;
    window.fetch=(input,init)=>String(input).includes('-preview-preface.pdf')
      ? Promise.resolve(new Response('Building',{status:404})) : window.nativePullFetch(input,init);
    const viewer=document.querySelector('#pdf-viewer');viewer.scrollTop=0;
    viewer.dispatchEvent(new WheelEvent('wheel',{deltaY:-150,bubbles:true,cancelable:true}));
  })()`);
  await tab.waitFor(
    "window.pullState.pdf.path.endsWith('-preview-preface.pdf') && document.querySelector('[data-pane=pdf] .pdf-load-status')?.textContent.includes('Building PDF')",
    { timeout: 15000 },
  );
  assert.equal(await tab.evaluate("window.pullState.pdf.loadedPath.endsWith('-preview-polish-spaces.pdf')"), true);
  assert.equal(await tab.evaluate("!!document.querySelector('#pdf-viewer canvas:not([hidden])')"), true);
  await tab.evaluate("window.fetch=window.nativePullFetch;import('./build/pdf.js').then(pdf=>pdf.reloadPdf())");
  await tab.waitFor("window.pullState.pdf.loadedPath===window.pullState.pdf.path && !window.pullState.pdf.pending", {
    timeout: 30000,
  });
  await tab.evaluate("window.pullState.pdf.targetPromise");
  await tab.waitFor(
    "(() => {const v=document.querySelector('#pdf-viewer');return v.scrollHeight-v.clientHeight-v.scrollTop<3})()",
    { timeout: 15000 },
  );
});

test("a single remaining pane fills the phone viewport after removing its split siblings", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 45000 });
  await tab.evaluate(`(() => {
    for (const input of document.querySelectorAll('#settings-menu .pane-check')) {
      if (input.value!=='pdf' && input.checked) {input.checked=false;input.dispatchEvent(new Event('change'));}
    }
  })()`);
  const bounds = await tab.evaluate<{ paneWidth: number; workspaceWidth: number; panes: number }>(`(() => {
    const workspace=document.querySelector('.workspace');
    return {paneWidth:document.querySelector('[data-pane=pdf]').getBoundingClientRect().width,
      workspaceWidth:workspace.clientWidth,panes:[...workspace.querySelectorAll('.pane')].filter(p=>!p.hidden).length};
  })()`);
  assert.equal(bounds.panes, 1);
  assert.ok(
    bounds.paneWidth >= bounds.workspaceWidth - 10,
    `single pane must fill the workspace: ${JSON.stringify(bounds)}`,
  );
});

test("PDF headers and maximized overlay buttons share global settings with the hamburger menu", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.onNewDocument(`
    if(!sessionStorage.getItem('overlay-shortcut-seeded')) {
      sessionStorage.setItem('overlay-shortcut-seeded','1');
      localStorage.setItem('formalization-viewer-highlights','on');
      localStorage.setItem('formalization-viewer-links','off');
    }
  `);
  await tab.navigate(
    `${server.baseUrl}/polish-space-ja/?v=1&layout=row(pdf,pdf-peer,md)&marker=closed_subspace_polish`,
  );
  await tab.waitFor(READY, { timeout: 45000 });
  for (const name of ["pdf", "pdf-peer"]) {
    assert.equal(
      await tab.evaluate(`document.querySelectorAll('[data-pane="${name}"] .pane-header .overlay-toggle').length`),
      2,
    );
    const clipped = await tab.evaluate(`(()=>{
      const pane=document.querySelector('[data-pane="${name}"]').getBoundingClientRect();
      return [...document.querySelectorAll('[data-pane="${name}"] .pane-actions button')].filter(b=>!b.hidden).some(b=>{
        const r=b.getBoundingClientRect();return r.left<pane.left || r.right>pane.right;
      });
    })()`);
    assert.equal(clipped, false, `PDF controls fit a narrow ${name} header`);
  }
  const consistent = async (marks: boolean, links: boolean) =>
    assert.equal(
      await tab.evaluate(`
    document.body.classList.contains('marks-off')===${!marks} && document.body.classList.contains('links-on')===${links} &&
    [...document.querySelectorAll('.overlay-toggle[data-overlay=highlights]')].every(b=>b.getAttribute('aria-pressed')==='${marks}') &&
    [...document.querySelectorAll('.overlay-toggle[data-overlay=links]')].every(b=>b.getAttribute('aria-pressed')==='${links}') &&
    document.querySelector('#highlights-seg [data-value=${marks ? "on" : "off"}]').getAttribute('aria-pressed')==='true' &&
    document.querySelector('#links-seg [data-value=${links ? "on" : "off"}]').getAttribute('aria-pressed')==='true'
  `),
      true,
    );
  await consistent(true, false);
  await tab.evaluate(
    "document.querySelector('[data-pane=pdf] .overlay-toggle[data-overlay=highlights]').click();document.querySelector('[data-pane=pdf-peer] .overlay-toggle[data-overlay=links]').click()",
  );
  await consistent(false, true);
  await tab.evaluate("document.querySelector('[data-pane=pdf] .pane-maximize').click()");
  assert.equal(await tab.evaluate("document.querySelector('#pane-tools').hidden"), false);
  assert.equal(
    await tab.evaluate("document.querySelector('#pane-tools').getBoundingClientRect().right<=innerWidth"),
    true,
  );
  await tab.evaluate(
    "document.querySelector('#pane-tools [data-overlay=highlights]').click();document.querySelector('#pane-tools [data-overlay=links]').click()",
  );
  await consistent(true, false);
  assert.equal(await tab.evaluate("new URLSearchParams(location.search).get('focus')"), "pdf");
  await tab.evaluate(
    "document.querySelector('#pane-restore').click();document.querySelector('#highlights-seg [data-value=off]').click();document.querySelector('#links-seg [data-value=on]').click()",
  );
  await consistent(false, true);
  assert.equal(await tab.evaluate("document.querySelector('#pane-tools').hidden"), true);
  await tab.evaluate("window.overlayReload=true;setTimeout(()=>location.reload(),0)");
  await tab.waitFor("!window.overlayReload && document.body.dataset.viewerReady==='1'", { timeout: 45000 });
  await consistent(false, true);
  await tab.evaluate(
    "document.querySelector('#highlights-seg [data-value=on]').click();document.querySelector('#links-seg [data-value=off]').click()",
  );
  await consistent(true, false);
});

test("pane maximize fills a phone screen and restores split ratios and reading positions", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-scroll-sync','off');localStorage.setItem('formalization-viewer-appearance-mode','light')",
  );
  const tree = {
    dir: "col",
    children: [
      { dir: "row", children: [{ pane: "pdf" }, { pane: "pdf-peer" }, { pane: "md" }], ratios: [3, 2, 1] },
      { dir: "row", children: [{ pane: "lean" }, { pane: "tex" }, { pane: "infoview" }], ratios: [4, 2, 1] },
    ],
    ratios: [3, 2],
  };
  const layout = encodeURIComponent(JSON.stringify({ tree }));
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&layout=${layout}&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 45000 });
  await tab.evaluate(
    "import('./build/state.js').then(({state})=>{window.maximizeState=state;return state.pdf.targetPromise})",
  );
  assert.equal(await tab.evaluate("document.querySelectorAll('.pane-maximize').length"), 6);
  assert.equal(await tab.evaluate("document.querySelectorAll('.pane-close').length"), 6);
  const clippedButtons = await tab.evaluate<
    string[]
  >(`[...document.querySelectorAll('.pane-maximize, .pane-close')].filter(button=>{
    const pane=button.closest('.pane').getBoundingClientRect(), rect=button.getBoundingClientRect();
    return rect.left<pane.left || rect.right>pane.right;
  }).map(button=>button.closest('.pane').dataset.pane)`);
  assert.deepEqual(clippedButtons, [], "maximize and close buttons stay inside narrow pane headers");
  const original = await tab.evaluate<string>("JSON.stringify(window.maximizeState.layout.tree)");
  const anchor = () =>
    tab.evaluate<number>(
      "import('./build/pdf.js').then(pdf=>{const a=pdf.capturePdfScrollAnchor();return a.pageNumber+a.fraction})",
    );
  const settle = () => tab.evaluate("new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))");
  const toggle = (pane: string) =>
    tab.evaluate(
      `(() => {const restore=document.querySelector('#pane-restore'); (restore.hidden ? document.querySelector('[data-pane="${pane}"] .pane-maximize') : restore).click()})()`,
    );
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=500");
  const before = await anchor();
  await toggle("pdf");
  await settle();
  const focused = await tab.evaluate<{
    visible: string[];
    width: number;
    pressed: string;
    maximized: string;
    selected: number;
  }>(`(() => ({
    visible:[...document.querySelectorAll('.pane')].filter(p=>!p.hidden).map(p=>p.dataset.pane),
    width:document.querySelector('[data-pane=pdf]').getBoundingClientRect().width,
    pressed:document.querySelector('[data-pane=pdf] .pane-maximize').getAttribute('aria-pressed'),
    maximized:new URLSearchParams(location.search).get('focus'),
    selected:document.querySelectorAll('.pane-check:checked').length,
  }))()`);
  assert.deepEqual(focused.visible, ["pdf"]);
  assert.equal(
    focused.width,
    await tab.evaluate("document.documentElement.clientWidth"),
    `maximized pane width: ${focused.width}`,
  );
  assert.equal(focused.pressed, "true");
  assert.equal(focused.maximized, "pdf");
  assert.equal(focused.selected, 6, "maximization keeps the original pane selections");
  const immersive = await tab.evaluate<{
    toolbar: string;
    header: string;
    rail: string;
    height: number;
    restore: boolean;
  }>(`(() => ({
    toolbar:getComputedStyle(document.querySelector('.toolbar')).display,
    header:getComputedStyle(document.querySelector('[data-pane=pdf] .pane-header')).display,
    rail:getComputedStyle(document.querySelector('[data-pane=pdf] .mark-rail')).display,
    height:document.querySelector('#pdf-viewer').clientHeight,
    restore:!document.querySelector('#pane-restore').hidden
  }))()`);
  assert.deepEqual([immersive.toolbar, immersive.header, immersive.rail], ["none", "none", "none"]);
  assert.ok(immersive.height >= 840, `immersive PDF height: ${immersive.height}`);
  assert.equal(immersive.restore, true, "iPhone fallback keeps an accessible restore button");
  assert.equal(await tab.evaluate("JSON.stringify(window.maximizeState.layout.tree)"), original);
  assert.ok(Math.abs((await anchor()) - before) < 0.1, "maximizing keeps the PDF reading position");
  await tab.evaluate("window.scrollTo(0,3000)");
  await tab.waitFor("window.scrollY>=2999");
  const moved = await anchor();
  await toggle("pdf");
  await settle();
  assert.equal(await tab.evaluate("JSON.stringify(window.maximizeState.layout.tree)"), original);
  assert.equal(await tab.evaluate("[...document.querySelectorAll('.pane')].filter(p=>!p.hidden).length"), 6);
  assert.ok(Math.abs((await anchor()) - moved) < 0.1, "restoring keeps the position read while maximized");
  for (const pane of ["md", "lean", "tex", "infoview", "pdf-peer"]) {
    await toggle(pane);
    await settle();
    assert.deepEqual(
      await tab.evaluate("[...document.querySelectorAll('.pane')].filter(p=>!p.hidden).map(p=>p.dataset.pane)"),
      [pane],
    );
    await toggle(pane);
    await settle();
    assert.equal(await tab.evaluate("JSON.stringify(window.maximizeState.layout.tree)"), original);
  }
  await toggle("pdf");
  await tab.evaluate("window.maximizeReload=true;setTimeout(()=>location.reload(),0)");
  await tab.waitFor("!window.maximizeReload && document.body.dataset.viewerReady==='1'", { timeout: 45000 });
  assert.deepEqual(
    await tab.evaluate("[...document.querySelectorAll('.pane')].filter(p=>!p.hidden).map(p=>p.dataset.pane)"),
    ["pdf"],
  );
  await toggle("pdf");
  assert.equal(
    await tab.evaluate(
      "import('./build/session-store.js').then(({sharedPreference})=>JSON.stringify(JSON.parse(sharedPreference(location.search,'formalization-viewer-layout-v2')).tree))",
    ),
    original,
  );
});

test("restoring a maximized default layout removes the layout URL parameter", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate("document.querySelector('[data-pane=md] .pane-maximize').click()");
  assert.equal(await tab.evaluate("new URLSearchParams(location.search).get('focus')"), "md");
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  assert.equal(await tab.evaluate("new URLSearchParams(location.search).has('layout')"), false);
});

test("pane close buttons hide panes like the menu checkboxes and keep the last pane open", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  const tree = { dir: "row", children: [{ pane: "md" }, { pane: "lean" }] };
  const layout = encodeURIComponent(JSON.stringify({ tree }));
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=${layout}&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  const visible = () =>
    tab.evaluate<string[]>(
      "[...document.querySelectorAll('.workspace .pane')].filter(p=>p.offsetParent).map(p=>p.dataset.pane)",
    );
  assert.deepEqual((await visible()).sort(), ["lean", "md"]);
  await tab.evaluate("document.querySelector('[data-pane=lean] .pane-close').click()");
  assert.deepEqual(await visible(), ["md"]);
  assert.equal(await tab.evaluate("document.querySelector('.pane-check[value=lean]').checked"), false);
  assert.equal(await tab.evaluate("document.querySelector('[data-pane=md] .pane-close').disabled"), true);
  await tab.evaluate("document.querySelector('[data-pane=md] .pane-close').click()");
  assert.deepEqual(await visible(), ["md"]);
});

test("book selection stays in the menu while pane document selectors fit a phone viewport", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 45000 });
  assert.equal(await tab.evaluate("document.querySelectorAll('.pane-header select').length"), 3);
  assert.equal(await tab.evaluate("document.querySelector('#book-select').closest('#settings-menu')!==null"), true);
  assert.equal(
    await tab.evaluate(
      "['pdf-select','md-select','lean-select'].every(id=>document.getElementById(id).closest('.pane-header'))",
    ),
    true,
  );
  await openDocumentMenu(tab);
  for (const [id, pane] of [
    ["book-select-label", null],
    ["pdf-document-control", "pdf"],
    ["md-document-control", "md"],
    ["lean-document-control", "lean"],
  ] as const) {
    if (pane) {
      await tab.evaluate(`(() => {
        for (const input of document.querySelectorAll('.pane-check')) input.checked=input.value==='${pane}';
        document.querySelector('.pane-check').dispatchEvent(new Event('change'));
      })()`);
    }
    await tab.evaluate(`document.querySelector('#${id} .cselect-field').click()`);
    const rect = await tab.evaluate<{
      left: number;
      right: number;
      top: number;
      bottom: number;
      options: number;
    }>(`(() => {
      const pop=document.querySelector('#${id} .cselect-popover'), r=pop.getBoundingClientRect();
      return {left:r.left,right:r.right,top:r.top,bottom:r.bottom,options:pop.querySelectorAll('[role=option]').length};
    })()`);
    assert.ok(rect.options > 0, `choices for ${id}`);
    assert.ok(
      rect.left >= 0 && rect.right <= 391 && rect.top >= 0 && rect.bottom <= 845,
      `${id}: ${JSON.stringify(rect)}`,
    );
    await tab.evaluate(
      `document.querySelector('#${id} .cselect-search').dispatchEvent(new KeyboardEvent('keydown',{key:'Escape',bubbles:true,cancelable:true}))`,
    );
    if (!pane) {
      assert.equal(
        await tab.evaluate("document.querySelector('#settings-menu').matches(':popover-open')"),
        true,
        "Escape closes the dropdown before the menu",
      );
      await tab.evaluate("document.querySelector('#settings-toggle').click()");
    }
  }
  await tab.evaluate(`(() => {
    for (const input of document.querySelectorAll('.pane-check')) input.checked=input.value==='md';
    document.querySelector('.pane-check').dispatchEvent(new Event('change'));
  })()`);
  await tab.evaluate("document.querySelector('#md-document-control .cselect-field').click()");
  await tab.evaluate(`(() => {
    const select=document.querySelector('#md-select');
    const index=[...select.options].findIndex(o=>o.value.endsWith('/polish-spaces.md'));
    document.querySelector('#md-document-control [data-i="'+index+'"]').click();
  })()`);
  await tab.waitFor("document.querySelector('#md-source').textContent.includes('# ポーランド空間')", {
    timeout: 15000,
  });
});

test("maximized reading uses page scrolling for chapter pulls and restores source positions", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-scroll-sync','off');localStorage.setItem('formalization-viewer-appearance-mode','light')",
  );
  const layout = encodeURIComponent(JSON.stringify({ tree: { pane: "pdf" }, maximized: "pdf" }));
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=${layout}&marker=preface_rational_complexity`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(
    "import('./build/state.js').then(({state})=>{window.rootScrollState=state;return state.pdf.targetPromise})",
  );
  assert.equal(
    await tab.evaluate("document.querySelector('#pdf-viewer').classList.contains('document-scroller')"),
    true,
  );
  await tab.evaluate("window.scrollTo(0,document.documentElement.scrollHeight)");
  await tab.waitFor("window.scrollY>1000");
  assert.equal(
    await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop"),
    0,
    "the page scrolls, not a nested PDF container",
  );
  await tab.evaluate(
    "document.querySelector('#pdf-viewer').dispatchEvent(new WheelEvent('wheel',{deltaY:150,bubbles:true,cancelable:true}))",
  );
  await tab.waitFor(
    "window.rootScrollState.pdf.loadedPath?.endsWith('-preview-polish-spaces.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.evaluate("window.rootScrollState.pdf.targetPromise");
  await tab.waitFor("window.scrollY<=2");
  await tab.evaluate("new Promise(resolve=>setTimeout(resolve,260))");
  await tab.evaluate(
    "document.querySelector('#pdf-viewer').dispatchEvent(new WheelEvent('wheel',{deltaY:-150,bubbles:true,cancelable:true}))",
  );
  await tab.waitFor(
    "window.rootScrollState.pdf.loadedPath?.endsWith('-preview-preface.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.evaluate("window.rootScrollState.pdf.targetPromise");
  await tab.waitFor("document.documentElement.scrollHeight-innerHeight-scrollY<3");
  await tab.evaluate(`(() => {
    document.querySelector('#pane-restore').click();
    for (const input of document.querySelectorAll('.pane-check')) input.checked=input.value==='md';
    document.querySelector('.pane-check').dispatchEvent(new Event('change'));
    document.querySelector('[data-pane=md] .pane-maximize').click();
  })()`);
  await tab.evaluate("new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))");
  await tab.waitFor("document.querySelector('#md-source .line')", { timeout: 30000 });
  await tab.evaluate("window.scrollTo(0,1000)");
  await tab.waitFor("window.scrollY>=999");
  const readingLine = await tab.evaluate<string>(
    "[...document.querySelectorAll('#md-source .line')].find(line=>line.getBoundingClientRect().bottom>0).textContent",
  );
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  await tab.evaluate("new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))");
  assert.equal(await tab.evaluate("window.scrollY"), 0);
  const restored = await tab.evaluate<string>(
    "[...document.querySelectorAll('#md-source .line')].find(line=>line.getBoundingClientRect().bottom>document.querySelector('#md-source').getBoundingClientRect().top).textContent",
  );
  assert.equal(restored, readingLine, "returning to a split pane keeps the source reading line");
});

test("edge touch pans cannot trigger browser refresh, while normal scrolling and zoom remain native", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.setViewport(390, 844);
  const layout = encodeURIComponent(
    JSON.stringify({ tree: { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }] }, maximized: "pdf" }),
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&pdfMode=full&layout=${layout}`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(`window.edgePan=(dx,dy,count=1)=>{
    const viewer=document.querySelector('#pdf-viewer');
    const fire=(type,x,y)=>{
      const event=new Event(type,{bubbles:true,cancelable:true});
      Object.defineProperty(event,'touches',{value:Array.from({length:count},(_,i)=>({clientX:x+i*30,clientY:y}))});
      viewer.dispatchEvent(event);return event.defaultPrevented;
    };
    fire('touchstart',100,100);
    const blocked=fire('touchmove',100+dx,100+dy);
    fire('touchend',100+dx,100+dy);
    return blocked;
  }`);
  await tab.evaluate("window.scrollTo(0,0)");
  assert.equal(await tab.evaluate("getComputedStyle(document.documentElement).overscrollBehaviorY"), "none");
  assert.equal(await tab.evaluate("window.edgePan(0,60)"), true, "pulling down at the page top is canceled");
  assert.equal(await tab.evaluate("window.edgePan(60,0)"), false, "horizontal gestures remain native");
  assert.equal(await tab.evaluate("window.edgePan(0,60,2)"), false, "pinch zoom remains native");
  await tab.evaluate("window.scrollTo(0,500)");
  assert.equal(await tab.evaluate("window.edgePan(0,60)"), false, "ordinary page scrolling remains native");
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=500");
  assert.equal(await tab.evaluate("window.edgePan(0,60)"), false, "a nested pane may scroll toward its top");
  await tab.evaluate("document.querySelector('#pdf-viewer').scrollTop=0");
  assert.equal(await tab.evaluate("window.edgePan(0,60)"), true, "a nested pane cannot chain into browser refresh");
});

test("a maximized PDF does not load hidden source panes, their highlighter, or Lean", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    const nativeFetch=window.fetch.bind(window);
    window.hiddenSourceRequests=[];
    window.releaseHiddenSources=[];
    window.fetch=(input,init)=>/\\.(?:md|lean|tex)(?:[?#]|$)/.test(String(input))
      ? new Promise(resolve=>{window.hiddenSourceRequests.push(String(input));window.releaseHiddenSources.push(()=>resolve(nativeFetch(input,init)));})
      : nativeFetch(input,init);
  `);
  const layout = encodeURIComponent(
    JSON.stringify({
      tree: { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }, { pane: "lean" }] },
      maximized: "pdf",
    }),
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=${layout}&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 30000 });
  assert.deepEqual(await tab.evaluate("window.hiddenSourceRequests"), []);
  assert.equal(
    await tab.evaluate(
      "performance.getEntriesByType('resource').some(r=>r.name.includes('treesitter/') || r.name.includes('/lsp/'))",
    ),
    false,
  );
  assert.equal(await tab.evaluate("!!document.querySelector('#pdf-viewer canvas:not([hidden])')"), true);
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  await tab.waitFor("window.hiddenSourceRequests.length>0");
  assert.equal(await tab.evaluate("!!document.querySelector('#pdf-viewer canvas:not([hidden])')"), true);
  await tab.evaluate("window.releaseHiddenSources.forEach(release=>release())");
  await tab.waitFor("document.querySelector('#md-source .line') && document.querySelector('#lean-source .line')", {
    timeout: 30000,
  });
});

test("a maximized Markdown pane defers PDFs until the PDF pane is shown", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    const nativeFetch=window.fetch.bind(window);
    window.hiddenPdfRequests=[];
    window.releaseHiddenPdfs=[];
    window.fetch=(input,init)=>String(input).includes('.pdf')
      ? new Promise(resolve=>{window.hiddenPdfRequests.push(String(input));window.releaseHiddenPdfs.push(()=>resolve(nativeFetch(input,init)));})
      : nativeFetch(input,init);
  `);
  const layout = encodeURIComponent(
    JSON.stringify({ tree: { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }] }, maximized: "md" }),
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=${layout}&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 30000 });
  assert.deepEqual(await tab.evaluate("window.hiddenPdfRequests"), []);
  assert.equal(
    await tab.evaluate("performance.getEntriesByType('resource').some(r=>r.name.includes('/vendor/pdfjs/'))"),
    false,
  );
  assert.equal(await tab.evaluate("!!document.querySelector('#md-source .line')"), true);
  await tab.evaluate("document.querySelector('#pane-restore').click()");
  await tab.waitFor("window.hiddenPdfRequests.length>0");
  assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('.workspace')).visibility"), "visible");
  await tab.evaluate("window.releaseHiddenPdfs.forEach(release=>release())");
  await tab.waitFor("document.querySelector('#pdf-viewer canvas:not([hidden])')", { timeout: 30000 });
});

test("a slow visible PDF does not block reading the visible Markdown pane", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    const nativeFetch=window.fetch.bind(window);
    window.fetch=(input,init)=>String(input).includes('.pdf')
      ? new Promise(resolve=>window.releaseSlowPdf=()=>resolve(nativeFetch(input,init)))
      : nativeFetch(input,init);
  `);
  const layout = encodeURIComponent(
    JSON.stringify({ tree: { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }] } }),
  );
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&layout=${layout}&marker=closed_subspace_polish`);
  await tab.waitFor("typeof window.releaseSlowPdf==='function' && document.querySelector('#md-source .line')", {
    timeout: 30000,
  });
  assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('.workspace')).visibility"), "visible");
  assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('.view-startup')).display"), "none");
  await tab.evaluate("window.releaseSlowPdf()");
  await tab.waitFor(READY, { timeout: 30000 });
});

test("the startup card updates before application modules finish loading", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.blockRequests(["*/build/app.js"]);
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1`);
  await tab.waitFor("document.querySelector('#startup-detail').textContent.includes('files')");
  const before = await tab.evaluate<string>("document.querySelector('#startup-detail').textContent");
  await tab.waitFor(`document.querySelector('#startup-detail').textContent!==${JSON.stringify(before)}`);
  assert.equal(await tab.evaluate("document.documentElement.dataset.startupPhase"), undefined);
  assert.equal(await tab.evaluate("document.querySelector('#startup-progress').hasAttribute('value')"), false);
  await tab.blockRequests([]);
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 45000 });
});

test("build watch events leave the current PDF intact until a completed build can replace it", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 30000 });
  await tab.evaluate(`(async()=>{
    const {state}=await import('./build/state.js');
    await state.pdf.targetPromise;
    const {eventStream}=await import('./build/event-stream.js');
    window.buildState=state;
    window.oldBuildPage=document.querySelector('#pdf-viewer .pdf-page');
    window.emitBuildEvent=(type,data)=>eventStream.source.dispatchEvent(new MessageEvent(type,{data:JSON.stringify(data)}));
    window.emitBuildEvent('build',{dir:'polish-space',state:'building'});
    window.emitBuildEvent('watch',{path:'polish-space/'+state.pdf.path.slice(state.pdf.path.indexOf('build/'))});
  })()`);
  await tab.evaluate("new Promise(resolve=>setTimeout(resolve,700))");
  assert.equal(await tab.evaluate("window.oldBuildPage.isConnected"), true);
  assert.match(
    await tab.evaluate<string>("document.querySelector('[data-pane=pdf] .pdf-load-status').textContent"),
    /Building PDF/,
  );
  await tab.evaluate("window.emitBuildEvent('build',{dir:'polish-space',state:'done'})");
  await tab.waitFor("!window.oldBuildPage.isConnected", { timeout: 30000 });
  await tab.evaluate("window.buildState.pdf.targetPromise");
  await tab.evaluate(
    `window.oldBuildPage=document.querySelector('#pdf-viewer .pdf-page');window.emitBuildEvent('build',{dir:'polish-space',state:'building'});window.emitBuildEvent('build',{dir:'polish-space',state:'failed'})`,
  );
  assert.equal(await tab.evaluate("window.oldBuildPage.isConnected"), true);
  assert.match(
    await tab.evaluate<string>("document.querySelector('[data-pane=pdf] .pdf-load-status').textContent"),
    /failed/,
  );
});

test("startup reports source-map and PDF preparation progress before revealing the panes", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(`
    const nativeFetch=window.fetch.bind(window);
    window.startupDetails=[];
    new MutationObserver(()=>{
      for(const label of document.querySelectorAll('#startup-detail, .pdf-load-status')) {
        const detail=label.textContent;
        if(detail && !window.startupDetails.includes(detail)) window.startupDetails.push(detail);
      }
    }).observe(document,{subtree:true,childList:true,characterData:true});
    window.fetch=(input,init)=>String(input).includes('-sourcemap.json')
      ? new Promise(resolve=>window.releaseStartupMap=()=>resolve(nativeFetch(input,init)))
      : nativeFetch(input,init);
  `);
  await tab.navigate(`${server.baseUrl}/polish-space/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor("typeof window.releaseStartupMap==='function'");
  assert.equal(await tab.evaluate("document.querySelector('[data-startup-step=manifest]').dataset.state"), "done");
  assert.equal(await tab.evaluate("document.querySelector('[data-startup-step=map]').dataset.state"), "working");
  assert.equal(await tab.evaluate("document.querySelector('#startup-progress').value"), 1);
  assert.match(await tab.evaluate<string>("document.querySelector('#startup-detail').textContent"), /source map/i);
  await tab.evaluate("window.releaseStartupMap()");
  await tab.waitFor(READY, { timeout: 45000 });
  const details = await tab.evaluate<string[]>("window.startupDetails");
  assert.ok(
    details.some((s) => /Analyzing PDF layout/.test(s)),
    JSON.stringify(details),
  );
  assert.ok(
    details.some((s) => /Rendering page/.test(s)),
    JSON.stringify(details),
  );
  assert.ok(
    details.some((s) => /source documents/.test(s)),
    JSON.stringify(details),
  );
  assert.equal(await tab.evaluate("getComputedStyle(document.querySelector('.view-startup')).display"), "none");
});

test("PDF updates keep both old panes readable and preserve scrolling until their replacements are prepared", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-scroll-sync','off');localStorage.setItem('formalization-viewer-appearance-mode','light')",
  );
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 45000 });
  await tab.waitFor(
    "document.querySelector('#pdf-peer-viewer canvas:not([hidden])') && document.querySelector('[data-pane=pdf-peer] .pdf-load-status')?.hidden",
    { timeout: 30000 },
  );
  await tab.evaluate(`(async()=>{
    const {state}=await import('./build/state.js');
    await state.pdf.targetPromise;
    window.updateState=state;
    window.oldPrimaryPage=document.querySelector('#pdf-viewer .pdf-page');
    window.oldPeerPage=document.querySelector('#pdf-peer-viewer .pdf-page');
    window.updateToken=state.pdf.renderToken;
    const nativeFetch=window.fetch.bind(window);
    window.releasePdfUpdates=[];
    window.fetch=(input,init)=>String(input).includes('.pdf')
      ? new Promise(resolve=>window.releasePdfUpdates.push(()=>resolve(nativeFetch(input,init))))
      : nativeFetch(input,init);
    const primary=await import('./build/pdf.js');
    const peer=await import('./build/parallel-pdf.js');
    window.updatePromise=Promise.all([
      primary.setPdf(state.pdf.path,{preserveScroll:true,scrollToActive:false}),
      peer.initParallelPdf(document.querySelector('#pdf-peer-link').getAttribute('href'),undefined,{preserveScroll:true})
    ]);
  })()`);
  await tab.waitFor("window.releasePdfUpdates.length===2", { timeout: 15000 });
  assert.equal(await tab.evaluate("window.oldPrimaryPage.isConnected && window.oldPeerPage.isConnected"), true);
  assert.equal(await tab.evaluate("window.updateState.pdf.renderToken===window.updateToken"), true);
  assert.equal(
    await tab.evaluate("[...document.querySelectorAll('.pdf-load-status')].filter(el=>!el.hidden).length"),
    2,
  );
  await tab.evaluate(`(async()=>{
    document.querySelector('#pdf-viewer').scrollTop=1500;
    await new Promise(resolve=>setTimeout(resolve,150));
    window.beforeUpdateAnchor=(await import('./build/pdf.js')).capturePdfScrollAnchor();
    window.releasePdfUpdates.forEach(release=>release());
    await window.updatePromise;
    await window.updateState.pdf.targetPromise;
  })()`);
  assert.equal(await tab.evaluate("!window.oldPrimaryPage.isConnected && !window.oldPeerPage.isConnected"), true);
  const delta = await tab.evaluate<number>(`(async()=>{
    const after=(await import('./build/pdf.js')).capturePdfScrollAnchor();
    return Math.abs(after.pageNumber+after.fraction-window.beforeUpdateAnchor.pageNumber-window.beforeUpdateAnchor.fraction);
  })()`);
  assert.ok(delta < 0.02, `reading position changed by ${delta} pages`);
  assert.equal(
    await tab.evaluate(
      "!!document.querySelector('#pdf-viewer canvas:not([hidden])') && !!document.querySelector('#pdf-peer-viewer canvas:not([hidden])')",
    ),
    true,
  );
});

test("chapter previews skip leading part and parity pages in both languages without renumbering links", async (t) => {
  const tab = await browser.newPage();
  t.after(() => tab.close());
  await tab.onNewDocument(
    "window.viewerErrors=[];const originalError=console.error;console.error=(...args)=>{window.viewerErrors.push(args.map(String).join(' '));originalError(...args)}",
  );
  await tab.onNewDocument(
    "localStorage.setItem('formalization-viewer-scroll-sync','off');localStorage.setItem('formalization-viewer-appearance-mode','light')",
  );
  await tab.navigate(`${server.baseUrl}/polish-space-ja/?v=1&marker=closed_subspace_polish`);
  await tab.waitFor(READY, { timeout: 45000 });
  await tab.evaluate(
    "import('./build/state.js').then(({state})=>{window.previewState=state;return state.pdf.targetPromise})",
  );
  await tab.waitFor("document.querySelector('#pdf-peer-viewer .pdf-page')", { timeout: 30000 });
  for (const viewer of ["pdf-viewer", "pdf-peer-viewer"]) {
    assert.ok(
      Number(await tab.evaluate(`document.querySelector('#${viewer} .pdf-page').dataset.page`)) > 1,
      "the part divider before this chapter is omitted",
    );
    assert.equal(await tab.evaluate(`document.querySelector('#${viewer} [data-page="1"]')===null`), true);
  }
  await tab.evaluate(`(() => {
    const select=document.querySelector('#pdf-select');
    select.value=[...select.options].find(o=>o.value.endsWith('-preview-cantor-baire-space.pdf')).value;
    select.dispatchEvent(new Event('change'));
  })()`);
  await tab.waitFor(
    "window.previewState.pdf.loadedPath?.endsWith('-preview-cantor-baire-space.pdf') && document.querySelector('#pdf-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.evaluate("window.previewState.pdf.targetPromise");
  await tab.waitFor(
    "document.querySelector('#pdf-peer-link').href.includes('-preview-cantor-baire-space.pdf') && document.querySelector('#pdf-peer-viewer .pdf-page')",
    { timeout: 30000 },
  );
  await tab.waitFor("document.querySelector('[data-pane=pdf-peer] .pdf-load-status')?.hidden", { timeout: 30000 });
  const openings = await tab.evaluate<Array<{ start: number; first: string; body: string }>>(`(async () => {
    const state=window.previewState;
    const peerTask=state.pdfjs.getDocument({url:document.querySelector('#pdf-peer-link').href});
    const peer=await peerTask.promise;
    const read=async (doc,id) => {
      const start=Number(document.querySelector('#'+id+' .pdf-page').dataset.page);
      const text=async (number)=>(await (await doc.getPage(number)).getTextContent()).items.map(item=>item.str||'').join('').replace(/\\s/g,'');
      return {start,first:await text(1),body:await text(start)};
    };
    try {return [await read(state.pdf.document,'pdf-viewer'),await read(peer,'pdf-peer-viewer')];}
    finally {await peerTask.destroy();}
  })()`);
  for (const opening of openings) {
    assert.equal(
      opening.start,
      /^[0-9ivxlcdm]*$/i.test(opening.first) ? 2 : 1,
      "only a folio-only opening is skipped; an actual first chapter page stays visible",
    );
    assert.ok(opening.body.length > 100, "the first displayed page contains chapter content");
  }
  const targetsIntact = await tab.evaluate<boolean>(`(async () => {
    const state=window.previewState;
    for (const [index,target] of state.pdf.targets) {
      const number=state.entries[index].texMatch.entry;
      const dest=await state.pdf.document.getDestination('booklink-entry-'+number);
      const page=await state.pdf.document.getPageIndex(dest[0])+1;
      if (page!==target.pageNumber || !state.pdf.pageStates.has(page)) return false;
    }
    return state.pdf.targets.size>0;
  })()`);
  assert.equal(targetsIntact, true, "source-map destinations keep the PDF's original page indices");
});
