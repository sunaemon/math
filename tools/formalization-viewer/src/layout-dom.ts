import { t } from "./i18n.js";
// Pane layout construction and accessible splitter controls. App supplies the
// persistence and PDF geometry effects; this module never imports app.
import { state } from "./state.js";
import type { LayoutNode } from "./layout-tree.js";
interface LayoutCallbacks {
  save(): void;
  refresh(): void;
}

export function applySplitFlex(container: HTMLElement, node: LayoutNode): void {
  const ratios = node.ratios ?? [];
  const total = ratios.reduce((sum, ratio) => sum + ratio, 0) || (node.children ?? []).length;
  const slots = [...container.children].filter((child) => !child.classList.contains("splitter")) as HTMLElement[];
  container.querySelectorAll<HTMLElement>(":scope > .splitter").forEach((splitter, i) => {
    const boundary = ratios.slice(0, i + 1).reduce((a, b) => a + b, 0) / total;
    splitter.setAttribute("aria-valuemin", "0");
    splitter.setAttribute("aria-valuemax", "100");
    splitter.setAttribute("aria-valuenow", String(Math.round(boundary * 100)));
  });
  slots.forEach((slot, i) => {
    slot.style.flex = `${ratios[i] / total} 1 0`;
  });
}

function buildSplitter(node: LayoutNode, leftIndex: number, callbacks: LayoutCallbacks): HTMLElement {
  const splitter = document.createElement("div");
  splitter.className = `splitter splitter-${node.dir === "row" ? "vertical" : "horizontal"}`;
  splitter.setAttribute("role", "separator");
  splitter.setAttribute("aria-orientation", node.dir === "row" ? "vertical" : "horizontal");
  splitter.setAttribute("aria-label", t("Resize panes"));
  splitter.tabIndex = 0;
  splitter.addEventListener("keydown", (event) => {
    const keys = node.dir === "row" ? ["ArrowLeft", "ArrowRight"] : ["ArrowUp", "ArrowDown"];
    if (!keys.includes(event.key)) return;
    event.preventDefault();
    const ratios = node.ratios ?? (node.children ?? []).map(() => 1);
    const total = ratios.reduce((a, b) => a + b, 0);
    const boundary = ratios.slice(0, leftIndex + 1).reduce((a, b) => a + b, 0) / total;
    node.ratios = resizePair(ratios, leftIndex, boundary + (event.key === keys[0] ? -0.02 : 0.02));
    if (splitter.parentElement) applySplitFlex(splitter.parentElement, node);
    callbacks.save();
    callbacks.refresh();
  });
  splitter.addEventListener("mousedown", (event) => {
    event.preventDefault();
    state.resizing = { node, leftIndex, container: splitter.parentElement };
    splitter.classList.add("dragging");
    document.body.classList.add("is-resizing");
  });
  return splitter;
}

export function buildLayoutNode(node: LayoutNode | null, callbacks: LayoutCallbacks): HTMLElement | null {
  if (!node) return null;
  if (node.pane) {
    const section = state.paneSections?.[node.pane];
    if (!section) return null;
    section.hidden = false;
    section.classList.remove("pane-hidden");
    section.style.display = "";
    return section;
  }
  const container = document.createElement("div");
  container.className = "split";
  container.dataset.dir = node.dir;
  (node.children ?? []).forEach((child, i) => {
    if (i > 0) container.append(buildSplitter(node, i - 1, callbacks));
    const childEl = buildLayoutNode(child, callbacks);
    if (childEl) container.append(childEl);
  });
  applySplitFlex(container, node);
  return container;
}

export function resizePair(ratios: number[], index: number, pointerRatio: number): number[] {
  const total = ratios.reduce((sum, ratio) => sum + ratio, 0);
  const before = ratios.slice(0, index).reduce((sum, ratio) => sum + ratio, 0);
  const pairTotal = ratios[index] + ratios[index + 1];
  const boundary = pointerRatio * total;
  const first = Math.min(pairTotal - 0.25, Math.max(0.25, boundary - before));
  const next = [...ratios];
  next[index] = first;
  next[index + 1] = pairTotal - first;
  return next;
}
