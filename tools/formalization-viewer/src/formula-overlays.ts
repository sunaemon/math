import { clearLeanFormula, prepareLeanFormulaAnchors, showLeanFormula } from "./lean-formula.js";
import { suppressPaneSync, visiblePaneNames } from "./sync.js";
import { t } from "./i18n.js";
import { state, project } from "./state.js";
import { mountPrefix, repoPath } from "./util.js";
import { readPreference, writePreference } from "./session-store.js";
import { pdfPageText } from "./pdf-page-text.js";
import { pdfOverlayAtPoint } from "./pdf-text-layer.js";
import { taggedFormulaRects, type FormulaRect } from "./formula-geometry.js";
import { formulaLineSpans } from "./source-offsets.js";
import type { CorrespondenceReport, FormulaEvidence } from "./correspondence-model.js";
import { openCorrespondenceFormula } from "./correspondence.js";

const selectedTags = new Set<string>();
const hoveredTags = new Set<string>();
const linkSelector = ".formula-overlay,.pdf-formula,.lean-formula-anchor";
function nodeTags(node: HTMLElement): string[] {
  const tags: string[] = node.dataset.formulaTags
    ? JSON.parse(node.dataset.formulaTags)
    : node.dataset.formulaTag
      ? [node.dataset.formulaTag]
      : [];
  const whole: string[] = JSON.parse(node.dataset.formulaWholeTags ?? "[]");
  return [...whole, ...tags.filter((tag) => !whole.includes(tag))];
}
function emphasize(node: HTMLElement): void {
  const tags = nodeTags(node);
  const selected = tags.some((tag) => selectedTags.has(tag));
  const hovered = tags.some((tag) => hoveredTags.has(tag));
  const lean = node.classList.contains("lean-formula-anchor");
  const whole: string[] = lean ? JSON.parse(node.dataset.formulaWholeTags ?? "[]") : tags;
  const selectedWhole = whole.some((tag) => selectedTags.has(tag));
  const hoveredWhole = whole.some((tag) => hoveredTags.has(tag));
  node.classList.toggle("formula-selected", selectedWhole);
  node.classList.toggle("formula-hovered", hoveredWhole);
  if (lean) {
    node.classList.toggle("lean-formula-overlay", selected || hovered);
    node.classList.toggle("formula-partial-active", (selected || hovered) && !selectedWhole && !hoveredWhole);
  }
}
function emphasizeAll(): void {
  document.querySelectorAll<HTMLElement>(linkSelector).forEach(emphasize);
}

const preference = "formalization-viewer-formula-overlays";
let enabled = true;
let refresh: (force?: boolean) => void = () => {};
export function refreshFormulaOverlays(force = false): void {
  refresh(force);
}
const evidence = new Map<string, { source: string; row: FormulaEvidence }>();
const surfaces = new Set<WeakRef<HTMLElement>>();
const seenSurfaces = new WeakSet<HTMLElement>();
const pageGeometry = new WeakMap<
  HTMLElement,
  { boxes: Map<string, FormulaRect[]>; width: number; height: number; crop: number }
>();

function drawPdf(surface: HTMLElement): void {
  surface.querySelectorAll(".pdf-formula").forEach((node) => node.remove());
  const geometry = pageGeometry.get(surface);
  if (!enabled || !geometry) return;
  for (const [tag, rects] of geometry.boxes) {
    const match = evidence.get(tag);
    if (!match) continue;
    for (const [index, rect] of rects.entries()) {
      const node = document.createElement("span");
      node.className = "pdf-formula";
      node.dataset.formula = String(match.row.index);
      node.dataset.formulaTag = tag;
      const label = t("Formula {0}: {1}", match.row.index, match.row.lean ?? match.row.typeStatus);
      node.style.left = `${((rect.left - geometry.crop) / geometry.width) * 100}%`;
      node.style.top = `${(rect.top / geometry.height) * 100}%`;
      node.style.width = `${((rect.right - rect.left) / geometry.width) * 100}%`;
      node.style.height = `${((rect.bottom - rect.top) / geometry.height) * 100}%`;
      if (index === 0) {
        node.tabIndex = 0;
        node.setAttribute("role", "button");
        node.setAttribute("aria-label", label);
      }
      emphasize(node);
      surface.append(node);
    }
  }
}

export async function paintFormulaPdfLayer(
  page: any,
  canvas: HTMLCanvasElement,
  crop: { x0: number; x1: number } | null,
): Promise<void> {
  const surface = canvas.parentElement;
  if (!surface) return;
  const viewport = page.getViewport({ scale: 1 });
  const content = await pdfPageText(page);
  pageGeometry.set(surface, {
    boxes: taggedFormulaRects(content, viewport.transform),
    width: crop ? crop.x1 - crop.x0 : viewport.width,
    height: viewport.height,
    crop: crop?.x0 ?? 0,
  });
  if (!seenSurfaces.has(surface)) {
    surfaces.add(new WeakRef(surface));
    seenSurfaces.add(surface);
  }
  drawPdf(surface);
}

function redrawPdf(): void {
  for (const ref of surfaces) {
    const surface = ref.deref();
    if (!surface) {
      surfaces.delete(ref);
      continue;
    }
    drawPdf(surface);
  }
}
function clearMd(pre: HTMLElement): void {
  for (const node of pre.querySelectorAll(".formula-overlay")) {
    const parent = node.parentNode;
    node.replaceWith(...node.childNodes);
    parent?.normalize();
  }
}
function drawMd(pre: HTMLElement, text: string, report: CorrespondenceReport): void {
  clearMd(pre);
  if (!enabled) return;
  const lines = formulaLineSpans(text, report);
  const focusable = new Set<number>();
  for (const [lineIndex, spans] of lines) {
    const line = pre.querySelector<HTMLElement>(`.line[data-line="${lineIndex + 1}"]`);
    if (!line) continue;
    const walker = document.createTreeWalker(line, NodeFilter.SHOW_TEXT);
    const pieces: Array<{ node: Text; start: number; end: number }> = [];
    let offset = 0;
    for (let node = walker.nextNode(); node; node = walker.nextNode()) {
      const textNode = node as Text;
      pieces.push({ node: textNode, start: offset, end: offset + textNode.length });
      offset += textNode.length;
    }
    for (const span of [...spans].sort((a, b) => b.start - a.start)) {
      const row = report.formulas.find((row) => row.index === span.index);
      if (!row?.pdfTag) continue;
      for (const piece of pieces) {
        const start = Math.max(span.start, piece.start) - piece.start,
          end = Math.min(span.end, piece.end) - piece.start;
        if (end <= start) continue;
        piece.node.splitText(end);
        const middle = piece.node.splitText(start);
        const node = document.createElement("span");
        node.className = "formula-overlay";
        node.dataset.formula = String(row.index);
        node.dataset.formulaTag = row.pdfTag;
        const label = t("Formula {0}: {1}", row.index, row.lean ?? row.typeStatus);
        if (!focusable.has(row.index)) {
          node.tabIndex = 0;
          node.setAttribute("role", "button");
          node.setAttribute("aria-label", label);
          focusable.add(row.index);
        }
        middle.replaceWith(node);
        node.append(middle);
      }
    }
  }
}

export function initFormulaOverlays(
  activateLemma: (index: number) => Promise<void>,
  revealLean: (source: string) => Promise<void>,
  renderPdfPage: (page: number, token: number) => Promise<void>,
): void {
  const pre = document.getElementById("md-source")!;
  const toggle = document.getElementById("formula-overlays-toggle") as HTMLButtonElement;
  const popup = document.createElement("div");
  popup.id = "formula-popup";
  popup.hidden = true;
  popup.setAttribute("role", "dialog");
  popup.setAttribute("aria-label", t("Formula correspondence"));
  document.body.append(popup);
  enabled = readPreference(preference) !== "off";
  let report: CorrespondenceReport | null = null,
    loaded = "",
    text = "",
    generation = 0,
    interaction = 0;
  let controller: AbortController | undefined;
  let pinned: HTMLElement | undefined;
  let hoverKey = "";
  let hoverTimer: ReturnType<typeof setTimeout> | undefined;
  const clearHoverTimer = () => {
    clearTimeout(hoverTimer);
    hoverTimer = undefined;
  };
  const dismiss = () => {
    interaction++;
    clearHoverTimer();
    hoverKey = "";
    pinned = undefined;
    selectedTags.clear();
    hoveredTags.clear();
    clearLeanFormula();
    popup.hidden = true;
    emphasizeAll();
  };
  const source = () => `${project.dir}/${state.selectedSources.md ?? ""}`;
  const prepareLean = () => {
    if (!report || report.status !== "current" || !visiblePaneNames().includes("lean")) return;
    void prepareLeanFormulaAnchors(loaded, report.formulas)
      .then(emphasizeAll)
      .catch((error) => console.warn("[viewer] Lean formula anchors", error));
  };
  const redraw = () => {
    toggle.setAttribute("aria-pressed", String(enabled));
    if (report && loaded === source()) drawMd(pre, text, report);
    else clearMd(pre);
    redrawPdf();
    emphasizeAll();
  };
  async function load(force = false): Promise<void> {
    const current = source();
    if (!enabled || project.static) {
      clearMd(pre);
      redrawPdf();
      return;
    }
    if (!force && loaded === current && text === state.sources?.md && report) {
      if (!pre.querySelector(".formula-overlay")) redraw();
      prepareLean();
      return;
    }
    const token = ++generation;
    controller?.abort();
    controller = new AbortController();
    dismiss();
    clearMd(pre);
    clearLeanFormula(true);
    if (force) {
      evidence.clear();
      redrawPdf();
      loaded = "";
    }
    try {
      const response = await fetch(
        `${mountPrefix()}${project.mount}/correspondence.json?source=${encodeURIComponent(current)}`,
        { cache: "no-cache", signal: controller.signal },
      );
      if (!response.ok) return;
      const data = (await response.json()) as CorrespondenceReport;
      if (token !== generation || current !== source()) return;
      for (const [tag, value] of evidence) if (value.source === current) evidence.delete(tag);
      report = data;
      loaded = current;
      text = state.sources?.md ?? "";
      if (data.status === "current")
        for (const row of data.formulas) if (row.pdfTag) evidence.set(row.pdfTag, { source: current, row });
      redraw();
      prepareLean();
    } catch (error) {
      if (!controller.signal.aborted) console.warn("[viewer] formula overlays", error);
    }
  }
  function revealSource(kind: "md" | "lean", tags: string[]): void {
    const match = Array.from(
      document.querySelectorAll<HTMLElement>(`#${kind}-source ${linkSelector.split(",").join(`,#${kind}-source `)}`),
    ).find((node) => nodeTags(node).some((tag) => tags.includes(tag)));
    if (match) {
      suppressPaneSync(kind);
      match.scrollIntoView({ block: "nearest", inline: "nearest" });
    }
  }
  async function revealPdf(tags: string[], row: FormulaEvidence, current: () => boolean): Promise<void> {
    if (!visiblePaneNames().includes("pdf") || !state.pdf.document) return;
    const find = () =>
      Array.from(state.panes.pdf.querySelectorAll<HTMLElement>(".pdf-formula")).find((node) =>
        nodeTags(node).some((tag) => tags.includes(tag)),
      );
    const scroll = (node: HTMLElement) => {
      suppressPaneSync("pdf");
      node.scrollIntoView({ block: "nearest", inline: "nearest" });
    };
    const visible = find();
    if (visible) {
      scroll(visible);
      return;
    }
    const doc = state.pdf.document,
      token = state.pdf.renderToken;
    await state.pdf.targetPromise;
    if (!current() || state.pdf.document !== doc) return;
    const entries = state.entries
      .map((entry, index) => ({ entry, index }))
      .filter(({ entry }) => repoPath(entry.match?.source) === state.selectedSources.md);
    const covering = entries.filter(
      ({ entry }) => entry.match.startOffset <= row.bodyStart && row.bodyStart < entry.match.endOffset,
    );
    const pages = new Set<number>();
    for (const band of state.pdf.entryBands)
      if (covering.some(({ index }) => index === band.index))
        for (const part of band.segments) pages.add(part.pageNumber);
    const chapterPages = entries
      .map(({ index }) => state.pdf.targets.get(index)?.pageNumber)
      .filter((page): page is number => page !== undefined);
    if (chapterPages.length)
      for (let n = Math.min(...chapterPages); n <= Math.min(doc.numPages, Math.max(...chapterPages) + 1); n++)
        pages.add(n);
    else if (doc.numPages <= 40) for (let n = 1; n <= doc.numPages; n++) pages.add(n);
    for (const pageNumber of pages) {
      const content = await pdfPageText(await doc.getPage(pageNumber));
      if (!current() || state.pdf.document !== doc) return;
      if (!content.items.some((item: any) => tags.includes(item.tag))) continue;
      await renderPdfPage(pageNumber, token);
      if (!current() || state.pdf.document !== doc) return;
      emphasizeAll();
      const found = find();
      if (found) scroll(found);
      return;
    }
  }
  function show(node: HTMLElement, hover = false): void {
    const tags = nodeTags(node).filter((tag) => evidence.has(tag));
    const matches = tags.map((tag) => evidence.get(tag)!);
    const match = matches[0];
    if (!match) return;
    const token = ++interaction;
    const current = () => token === interaction && !popup.hidden;
    clearLeanFormula();
    if (hover) {
      hoveredTags.clear();
      tags.forEach((tag) => hoveredTags.add(tag));
    } else {
      pinned = node;
      selectedTags.clear();
      hoveredTags.clear();
      tags.forEach((tag) => selectedTags.add(tag));
    }
    emphasizeAll();
    popup.dataset.formulaTag = tags[0];
    popup.dataset.mode = hover ? "hover" : "pinned";
    popup.replaceChildren();
    const heading = document.createElement("strong");
    heading.textContent = matches.map(({ row }) => t("Formula {0}", row.index)).join(" · ");
    popup.append(heading);
    for (const value of [
      match.row.book,
      ...(match.row.expressionFragments ?? [match.row]).map((part) => part.lean ?? part.typeReason ?? ""),
    ]) {
      const block = document.createElement("pre");
      block.textContent = value;
      popup.append(block);
    }
    if (matches.length > 1) {
      const related = document.createElement("details"),
        title = document.createElement("summary");
      title.textContent = t("Corresponding formulas: {0}", matches.length);
      related.append(title);
      for (const other of matches) {
        const block = document.createElement("pre");
        block.textContent = `#${other.row.index}: ${other.row.book}`;
        related.append(block);
      }
      popup.append(related);
    }
    const status = document.createElement("p");
    status.textContent = match.row.typeStatus;
    popup.append(status);
    const leanStatus = document.createElement("p");
    leanStatus.className = "formula-lean-status";
    popup.append(leanStatus);
    for (const op of match.row.operators) {
      const line = document.createElement("div");
      line.textContent = `${op.rule} → ${
        (op.calls ?? [])
          .map((call: any) => call.head)
          .filter(Boolean)
          .join(", ") ||
        op.expectedHead ||
        ""
      }`;
      popup.append(line);
    }
    const details = document.createElement("button");
    details.type = "button";
    details.textContent = t("Correspondence / AST");
    details.addEventListener("click", () => {
      dismiss();
      openCorrespondenceFormula(match.row.index);
    });
    popup.append(details);
    const close = document.createElement("button");
    close.type = "button";
    close.textContent = t("Close");
    close.addEventListener("click", dismiss);
    popup.append(close);
    popup.hidden = false;
    const rect = node.getBoundingClientRect();
    popup.style.left = `${Math.max(8, Math.min(rect.left, innerWidth - popup.offsetWidth - 8))}px`;
    popup.style.top = `${Math.max(8, Math.min(rect.bottom + 6, innerHeight - popup.offsetHeight - 8))}px`;
    const origin = node.closest("#lean-source") ? "lean" : node.closest("#md-source") ? "md" : "pdf";
    if (origin !== "md") revealSource("md", tags);
    if (origin !== "pdf")
      void revealPdf(tags, match.row, current).catch((error) => console.warn("[viewer] formula PDF navigation", error));
    const entry = node.closest<HTMLElement>(".mark")?.dataset.entry;
    void (async () => {
      if (!hover && origin === "md" && entry !== undefined) await activateLemma(Number(entry));
      if (!current()) return;
      await showLeanFormula(
        match.source,
        match.row.index,
        tags[0],
        leanStatus,
        revealLean,
        report?.formulas ?? [],
        emphasizeAll,
        origin !== "lean",
      );
      if (current() && origin !== "lean") revealSource("lean", tags);
    })();
  }
  function hit(target: Element | null, x: number, y: number): HTMLElement | null {
    return target?.closest<HTMLElement>(linkSelector) ?? pdfOverlayAtPoint(target, ".pdf-formula", x, y);
  }
  function leaveHover(): void {
    hoveredTags.clear();
    hoverKey = "";
    interaction++;
    clearLeanFormula();
    emphasizeAll();
    if (pinned?.isConnected) show(pinned);
    else popup.hidden = true;
  }
  function hover(node: HTMLElement | null): void {
    const key = node
      ? `${node.closest("#lean-source") ? "lean" : node.closest("#md-source") ? "md" : "pdf"}:${nodeTags(node).join("|")}`
      : "";
    if (key === hoverKey) return;
    hoverKey = key;
    clearHoverTimer();
    if (!node) {
      hoverTimer = setTimeout(leaveHover, 140);
      return;
    }
    hoverTimer = setTimeout(() => {
      if (node.isConnected) show(node, true);
    }, 100);
  }
  document.addEventListener("pointermove", (event) => {
    if (!enabled || event.pointerType === "touch" || event.buttons || window.getSelection()?.isCollapsed === false)
      return;
    const target = event.target as Element | null;
    if (target?.closest("#formula-popup")) {
      clearHoverTimer();
      hoverKey = "popup";
      return;
    }
    hover(hit(target, event.clientX, event.clientY));
  });
  document.addEventListener("pointerout", (event) => {
    if (!event.relatedTarget) hover(null);
  });
  document.addEventListener("focusin", (event) => {
    const target = event.target as Element | null;
    if (target?.closest("#formula-popup")) {
      clearHoverTimer();
      hoverKey = "popup";
      return;
    }
    if (enabled) hover(target?.closest<HTMLElement>(linkSelector) ?? null);
  });
  document.addEventListener("focusout", (event) => {
    if (!(event.relatedTarget as Element | null)?.closest(linkSelector + ",#formula-popup")) hover(null);
  });
  document.addEventListener(
    "click",
    (event) => {
      if (!enabled || window.getSelection()?.isCollapsed === false) return;
      const target = event.target as Element | null,
        node = hit(target, event.clientX, event.clientY);
      if (node) {
        event.preventDefault();
        event.stopPropagation();
        clearHoverTimer();
        show(node);
      } else if (!target?.closest("#formula-popup")) dismiss();
    },
    true,
  );
  document.addEventListener(
    "keydown",
    (event) => {
      if (event.key === "Escape") {
        dismiss();
        return;
      }
      const node = (event.target as Element | null)?.closest<HTMLElement>(linkSelector);
      if (enabled && node && !event.repeat && ["Enter", " "].includes(event.key)) {
        event.preventDefault();
        event.stopPropagation();
        clearHoverTimer();
        show(node);
      }
    },
    true,
  );
  toggle.addEventListener("click", () => {
    enabled = !enabled;
    writePreference(preference, enabled ? "on" : "off", "on");
    dismiss();
    if (!enabled) clearLeanFormula(true);
    redraw();
    if (enabled) void load();
  });
  refresh = (force = false) => {
    if (!force && !popup.hidden && loaded === source() && text === state.sources?.md) {
      prepareLean();
      return;
    }
    void load(force);
  };
  redraw();
  void load();
}
