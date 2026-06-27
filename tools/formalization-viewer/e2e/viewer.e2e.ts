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
import { CdpBrowser, type CdpPage } from "./cdp.ts";
import { startViewerServer, type ViewerServer } from "./viewer-server.ts";

const REPO_ROOT = path.resolve(import.meta.dirname, "..", "..", "..");
const MD = '.pane[data-pane="md"]';

let server: ViewerServer;
let browser: CdpBrowser;
let page: CdpPage;

before(async () => {
  server = await startViewerServer(REPO_ROOT, "polish-space");
  browser = await CdpBrowser.launch();
  page = await browser.newPage();
  await page.navigate(`${server.baseUrl}/`);
  // The SPA fetches sources + the sourcemap, then renders the panes.
  await page.waitFor("document.querySelectorAll('#md-source .line').length > 0", { timeout: 30000 });
});

after(async () => {
  await browser?.close();
  server?.stop();
});

test("boots: every pane mounts and the source pane renders with booklink marks", async () => {
  const dom = await page.evaluate<{ panes: string[]; mdLines: number; mdMarks: number; leanLines: number }>(`(() => ({
    panes: [...document.querySelectorAll('.pane')].map((p) => p.dataset.pane).sort(),
    mdLines: document.querySelectorAll('#md-source .line').length,
    mdMarks: document.querySelectorAll('#md-source .mark').length,
    leanLines: document.querySelectorAll('#lean-source .line').length,
  }))()`);
  assert.deepEqual(dom.panes, ["infoview", "lean", "md", "pdf", "tex"]);
  assert.ok(dom.mdLines > 50, `expected the md pane to render many lines, got ${dom.mdLines}`);
  assert.ok(dom.mdMarks > 0, "renderSource should emit booklink .mark spans against the live sourcemap");
  assert.ok(dom.leanLines > 0, `expected the lean pane to render, got ${dom.leanLines} lines`);
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
  await page.evaluate(`document.querySelector('${MD} .cselect-field').click()`);
  await page.waitFor(`!document.querySelector('${MD} .cselect-popover').hidden`);
  const total = await page.evaluate<number>(`document.querySelectorAll('${MD} .cselect-option').length`);
  assert.ok(total > 3, `expected several chapter options, got ${total}`);

  await page.evaluate(`(() => {
    const search = document.querySelector('${MD} .cselect-search');
    search.value = 'borel';
    search.dispatchEvent(new Event('input', { bubbles: true }));
  })()`);
  await page.waitFor(`document.querySelectorAll('${MD} .cselect-option').length < ${total}`);

  const filtered = await page.evaluate<string[]>(
    `[...document.querySelectorAll('${MD} .cselect-option')].map((o) => o.textContent.toLowerCase())`,
  );
  assert.ok(filtered.length >= 1 && filtered.length < total, "the query should narrow the option list");
  assert.ok(
    filtered.every((label) => label.includes("borel")),
    `every filtered option should match the query, got ${JSON.stringify(filtered)}`,
  );
  await page.evaluate(
    `document.querySelector('${MD} .cselect-search').dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }))`,
  );
});

test("choosing a different file in the dropdown switches the rendered source", async () => {
  await page.evaluate(`document.querySelector('${MD} .cselect-field').click()`);
  await page.waitFor(`!document.querySelector('${MD} .cselect-popover').hidden`);

  // Click the first option whose native value differs from the current file.
  const chosen = await page.evaluate<string | null>(`(() => {
    const pane = document.querySelector('${MD}');
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
