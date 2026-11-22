// Exact original Lean ranges form a persistent reverse lookup as well as a
// selection layer. No text search, head-only match, or theorem-wide fallback.
import { state, project } from "./state.js";
import { mountPrefix, repoPath } from "./util.js";
import { bucketByLine, buildLineStarts } from "./source-offsets.js";
import { formulaLinkSegments, formulaRangeCoverage } from "./formula-links.js";
import { suppressPaneSync } from "./sync.js";
import type { FormulaEvidence } from "./correspondence-model.js";
import { t } from "./i18n.js";

interface LeanRange {
  formulaIndex: number;
  operatorStart: number;
  source: string;
  sourceHash: string;
  startOffset: number;
  endOffset: number;
}
interface Locations {
  status: string;
  ranges: LeanRange[];
}
let request: { source: string; result: Promise<Locations> } | undefined;
let version = 0;
let anchorVersion = 0;
let rendered: { path: string; text: string; source: string } | undefined;

export function clearLeanFormula(invalidate = false): void {
  version++;
  document
    .querySelectorAll(".lean-formula-overlay")
    .forEach((node) =>
      node.classList.remove("lean-formula-overlay", "formula-selected", "formula-hovered", "formula-partial-active"),
    );
  if (!invalidate) return;
  request = undefined;
  rendered = undefined;
  anchorVersion++;
  document.querySelectorAll(".lean-formula-anchor").forEach((node) => {
    const parent = node.parentNode;
    node.replaceWith(...node.childNodes);
    parent?.normalize();
  });
}
function locations(source: string): Promise<Locations> {
  if (!request || request.source !== source) {
    const result = fetch(
      `${mountPrefix()}${project.mount}/correspondence-lean.json?source=${encodeURIComponent(source)}`,
      { cache: "no-cache" },
    ).then(async (response) => {
      if (!response.ok) throw new Error("Lean source locations unavailable");
      return (await response.json()) as Locations;
    });
    request = { source, result };
    void result.catch(() => {
      if (request?.result === result) request = undefined;
    });
  }
  return request.result;
}
export async function prepareLeanFormulaAnchors(source: string, formulas: FormulaEvidence[]): Promise<Locations> {
  const pending = locations(source);
  const data = await pending;
  if (request?.result !== pending) return data;
  const path = state.selectedSources.lean ?? "",
    text = state.sources?.lean ?? "";
  const pre = document.getElementById("lean-source")!;
  if (data.status !== "current") return data;
  if (
    rendered?.path === path &&
    rendered.text === text &&
    rendered.source === source &&
    pre.querySelector(".lean-formula-anchor")
  )
    return data;
  const token = ++anchorVersion;
  const digest = Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(text))))
    .map((byte) => byte.toString(16).padStart(2, "0"))
    .join("");
  if (token !== anchorVersion || path !== state.selectedSources.lean || text !== state.sources?.lean) return data;
  pre.querySelectorAll(".lean-formula-anchor").forEach((node) => {
    const parent = node.parentNode;
    node.replaceWith(...node.childNodes);
    parent?.normalize();
  });
  const tags = new Map(formulas.filter((row) => row.pdfTag).map((row) => [row.index, row.pdfTag!]));
  const byIndex = new Map(formulas.map((row) => [row.index, row]));
  const spans = data.ranges
    .filter((row) => repoPath(row.source) === path && row.sourceHash === digest && tags.has(row.formulaIndex))
    .map((row) => ({
      ...row,
      tags: [tags.get(row.formulaIndex)!],
      wholeTags:
        formulaRangeCoverage(byIndex.get(row.formulaIndex)!, row.operatorStart) === "whole"
          ? [tags.get(row.formulaIndex)!]
          : [],
    }));
  const indexByTag = new Map(formulas.filter((row) => row.pdfTag).map((row) => [row.pdfTag!, row.index]));
  const focusable = new Set<string>();
  for (const [lineIndex, ranges] of bucketByLine(buildLineStarts(text), text.length, spans)) {
    const line = pre.querySelector(`.line[data-line="${lineIndex + 1}"]`);
    if (!line) continue;
    const walker = document.createTreeWalker(line, NodeFilter.SHOW_TEXT);
    const pieces: Array<{ node: Text; start: number; end: number }> = [];
    let offset = 0;
    for (let node = walker.nextNode(); node; node = walker.nextNode()) {
      const part = node as Text;
      pieces.push({ node: part, start: offset, end: offset + part.length });
      offset += part.length;
    }
    for (const span of formulaLinkSegments(ranges).reverse())
      for (const piece of pieces) {
        const start = Math.max(span.start, piece.start) - piece.start,
          end = Math.min(span.end, piece.end) - piece.start;
        if (end <= start) continue;
        piece.node.splitText(end);
        const middle = piece.node.splitText(start),
          overlay = document.createElement("span");
        overlay.className = "lean-formula-anchor";
        overlay.dataset.formulaTags = JSON.stringify(span.tags);
        overlay.dataset.formulaWholeTags = JSON.stringify(span.wholeTags ?? []);
        const identity = `${lineIndex}:${span.start}:${span.end}`;
        if (!focusable.has(identity)) {
          overlay.tabIndex = 0;
          focusable.add(identity);
        }
        overlay.setAttribute("role", "button");
        overlay.setAttribute("aria-label", span.tags.map((tag) => t("Formula {0}", indexByTag.get(tag)!)).join(" · "));
        middle.replaceWith(overlay);
        overlay.append(middle);
      }
  }
  rendered = { path, text, source };
  return data;
}
export async function showLeanFormula(
  source: string,
  index: number,
  tag: string,
  status: HTMLElement,
  reveal: (source: string) => Promise<void>,
  formulas: FormulaEvidence[],
  changed: () => void,
  scroll = true,
): Promise<void> {
  const token = ++version;
  status.textContent = t("Locating the original Lean expression…");
  try {
    const data = await locations(source);
    if (token !== version) return;
    const ranges = data.status === "current" ? data.ranges.filter((row) => row.formulaIndex === index) : [];
    if (!ranges.length) {
      status.dataset.coverage = "none";
      status.textContent = t("No exact original Lean expression location is available.");
      return;
    }
    const first = ranges.find((row) => repoPath(row.source) === state.selectedSources.lean) ?? ranges[0];
    await reveal(repoPath(first.source));
    if (token !== version) return;
    await prepareLeanFormulaAnchors(source, formulas);
    if (token !== version) return;
    changed();
    const nodes = Array.from(document.querySelectorAll<HTMLElement>("#lean-source .lean-formula-anchor")).filter(
      (node) => (JSON.parse(node.dataset.formulaTags!) as string[]).includes(tag),
    );
    const row = formulas.find((row) => row.index === index);
    const whole = new Set(
      ranges
        .filter((range) => row && formulaRangeCoverage(row, range.operatorStart) === "whole")
        .map((range) => `${range.source}:${range.startOffset}:${range.endOffset}`),
    ).size;
    const partial = new Set(
      ranges
        .filter((range) => !row || formulaRangeCoverage(row, range.operatorStart) === "partial")
        .map((range) => `${range.source}:${range.startOffset}:${range.endOffset}`),
    ).size;
    status.dataset.coverage = nodes.length ? (whole ? "whole" : "partial") : "none";
    status.textContent = !nodes.length
      ? t("No exact original Lean expression location is available.")
      : whole
        ? t("Whole expression matches: {0}. Subexpression matches: {1}.", whole, partial)
        : t("No whole-expression match. Only subexpression matches: {0}.", partial);
    if (scroll && nodes.length) {
      suppressPaneSync("lean");
      nodes[0].scrollIntoView({ block: "nearest", inline: "nearest" });
    }
  } catch (error) {
    if (token !== version) return;
    status.textContent = t("Original Lean expression locations could not be loaded.");
    console.warn("[viewer] Lean formula locations", error);
  }
}
