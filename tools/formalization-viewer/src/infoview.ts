import { t } from "./i18n.js";
import { setHTML } from "./safe-html.js";
// The Lean infoview pane: renders the current goal state, the expected type, and
// the active file's diagnostics into the infoview DOM. This is a pure render of
// state.lsp into els; the LSP connection and position tracking (connectInfoview)
// stay in app.ts and call renderInfoview whenever that state changes. One-way
// deps: infoview -> state/util/lean-lsp, never back into app.ts.

import { state, els } from "./state.js";
import { escapeHtml, displayPath } from "./util.js";
import { diagnosticsFor as lspDiagnosticsFor } from "./lean-lsp.js";

const DIAGNOSTIC_SEVERITY: Record<number, string> = { 1: "error", 2: "warning", 3: "info", 4: "hint" };

function infoviewStatusText(status: string): string {
  switch (status) {
    case "ready":
      return t("LSP: ready");
    case "static":
      return t("LSP: cached");
    case "connecting":
      return t("LSP: connecting…");
    case "reconnecting":
      return t("LSP: reconnecting…");
    case "closed":
      return t("LSP: server stopped");
    case "error":
      return t("LSP: error");
    default:
      return t("LSP: off");
  }
}

function renderGoalsSection(goal: any): string {
  const goals = goal?.goals || [];
  if (!goals.length) {
    const note = state.lsp.position ? t("No goals.") : t("Click a line in the Lean pane to inspect goals.");
    return `<section class="infoview-section"><h4>${t("Goals")}</h4><div class="infoview-empty">${note}</div></section>`;
  }
  const body = goals.map((text: string) => `<pre class="infoview-goal">${escapeHtml(text)}</pre>`).join("");
  const label = goals.length === 1 ? t("1 goal") : t("{0} goals", goals.length);
  return `<section class="infoview-section"><h4>${label}</h4>${body}</section>`;
}

function renderMessagesSection(uri: string | null): string {
  const diagnostics = uri ? lspDiagnosticsFor(uri) : [];
  if (!diagnostics.length) {
    return `<section class="infoview-section"><h4>${t("Messages")}</h4><div class="infoview-empty">${t("No messages.")}</div></section>`;
  }
  const items = diagnostics
    .slice()
    .sort(
      (a: any, b: any) => a.range.start.line - b.range.start.line || a.range.start.character - b.range.start.character,
    )
    .map((diagnostic: any) => {
      const severity = DIAGNOSTIC_SEVERITY[diagnostic.severity] || "info";
      const loc = `${diagnostic.range.start.line + 1}:${diagnostic.range.start.character + 1}`;
      return `<div class="infoview-msg sev-${severity}"><span class="infoview-msg-loc">${loc}</span><pre class="infoview-msg-text">${escapeHtml(diagnostic.message)}</pre></div>`;
    })
    .join("");
  return `<section class="infoview-section"><h4>${t("Messages ({0})", diagnostics.length)}</h4>${items}</section>`;
}

export function renderInfoview(): void {
  if (!els.infoviewBody) return;
  const { status, uri, position } = state.lsp;
  if (els.infoviewStatus) {
    els.infoviewStatus.textContent = infoviewStatusText(status);
    els.infoviewStatus.dataset.status = status;
  }
  if (status === "unavailable") {
    setHTML(
      els.infoviewBody,
      `<div class="infoview-empty">${t("Lean LSP bridge not available. Start the viewer with")} <code>make formalization-viewer</code> ${t("to enable live goals and diagnostics.")}</div>`,
    );
    return;
  }
  const posLabel = position
    ? `${displayPath(state.selectedSources.lean)}:${position.line + 1}:${position.character + 1}`
    : displayPath(state.selectedSources.lean);
  const sections = [`<div class="infoview-pos">${escapeHtml(posLabel)}</div>`];
  sections.push(renderGoalsSection(state.lsp.goal));
  if (state.lsp.termGoal?.goal) {
    sections.push(
      `<section class="infoview-section"><h4>${t("Expected type")}</h4><pre class="infoview-goal">${escapeHtml(state.lsp.termGoal.goal)}</pre></section>`,
    );
  }
  sections.push(renderMessagesSection(uri));
  setHTML(els.infoviewBody, sections.join(""));
}
