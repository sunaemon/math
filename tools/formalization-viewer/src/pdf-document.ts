import { t } from "./i18n.js";
import { pdfPageText } from "./pdf-page-text.js";
import { renderPdfTextLayer } from "./pdf-text-layer.js";
import { resolveDefinition } from "./definition-registry.js";
import { project } from "./state.js";
// Document geometry and link overlays shared by the primary and peer PDF panes.
import { groupTextLines, isPageFolio, type TextRun, type LineBox } from "./skip-bands.js";
import { safeHref } from "./util.js";
import { attachTermLink, type FollowPdfLink, type TermLinkContext } from "./term-preview.js";
import { previewStartPage } from "./pdf-preview.js";
import { paintFormulaPdfLayer } from "./formula-overlays.js";
export interface Crop {
  x0: number;
  x1: number;
}

export async function computeDocumentCrop(
  doc: any,
  pageWidth: number,
  current: () => boolean,
  progress?: (done: number, total: number) => void,
): Promise<{ x0: number; x1: number } | null> {
  const total = doc.numPages;
  const step = Math.max(1, Math.floor(total / Math.min(total, 24)));
  let minX = Infinity;
  let maxX = -Infinity;
  let sampled = 0;
  const samples = Math.ceil(total / step);
  for (let pageNumber = 1; pageNumber <= total; pageNumber += step) {
    if (!current()) return null;
    try {
      const page = await doc.getPage(pageNumber);
      const content = await pdfPageText(page);
      let count = 0;
      let pMin = Infinity;
      let pMax = -Infinity;
      for (const item of content.items as any[]) {
        if (!item.str || !item.str.trim()) continue;
        count += 1;
        const x = item.transform[4];
        const width = typeof item.width === "number" ? item.width : 0;
        if (x < pMin) pMin = x;
        if (x + width > pMax) pMax = x + width;
      }
      // Only full body pages define the text block; skip near-empty pages so a
      // sparse index/title page can't shrink the band.
      if (count >= 30 && pMax > pMin) {
        if (pMin < minX) minX = pMin;
        if (pMax > maxX) maxX = pMax;
      }
    } catch {
      // Ignore a page that fails to yield text; others still inform the band.
    }
    progress?.(++sampled, samples);
  }
  if (minX === Infinity || maxX <= minX) return null;
  const pad = 6;
  const x0 = Math.max(0, minX - pad);
  const x1 = Math.min(pageWidth, maxX + pad);
  const width = x1 - x0;
  // Crop only if it meaningfully narrows the page but isn't suspiciously tight.
  return width < pageWidth - 8 && width > pageWidth * 0.4 ? { x0, x1 } : null;
}

export interface PreparedPdfPage {
  pageNumber: number;
  el: HTMLElement;
  canvas: HTMLCanvasElement;
  rendered: boolean;
  rendering: boolean;
}

export async function paintPdfPage(
  page: any,
  canvas: HTMLCanvasElement,
  crop: Crop | null,
  width: number,
): Promise<string> {
  const base = page.getViewport({ scale: 1 });
  const cropWidth = crop ? crop.x1 - crop.x0 : base.width;
  const scale = ((width > 0 ? width : 240) / cropWidth) * (window.devicePixelRatio || 1);
  const viewport = page.getViewport({ scale, offsetX: -(crop?.x0 ?? 0) * scale });
  canvas.width = Math.floor(cropWidth * scale);
  canvas.height = Math.floor(base.height * scale);
  canvas.hidden = false;
  const context = canvas.getContext("2d");
  if (!context) throw new Error("Failed to obtain PDF canvas context");
  await page.render({ canvasContext: context, viewport }).promise;
  await renderPdfTextLayer(page, canvas, crop, width);
  await paintFormulaPdfLayer(page, canvas, crop);
  // Page geometry must not change with device-pixel rounding during repaint.
  return `${cropWidth} / ${base.height}`;
}

export async function preparePdf(
  doc: any,
  path: string,
  width: number,
  dark: boolean,
  current: () => boolean,
  report: (text: string) => void,
  preferredPage?: number,
): Promise<{
  pages: Map<number, PreparedPdfPage>;
  fragment: DocumentFragment;
  crop: Crop | null;
  start: number;
  base: any;
} | null> {
  report(t("Finding chapter opening…"));
  const start = await previewStartPage(doc, path, current);
  if (!current()) return null;
  const first = await doc.getPage(1);
  const base = first.getViewport({ scale: 1 });
  const crop = await computeDocumentCrop(doc, base.width, current, (done, total) =>
    report(t("Analyzing PDF layout · {0} / {1} pages", done, total)),
  );
  if (!current()) return null;
  const fragment = document.createDocumentFragment();
  const pages = new Map<number, PreparedPdfPage>();
  const cropWidth = crop ? crop.x1 - crop.x0 : base.width;
  for (let pageNumber = start; pageNumber <= doc.numPages; pageNumber++) {
    const el = document.createElement("div");
    el.className = "pdf-page";
    el.classList.toggle("is-dark-pdf", dark);
    el.dataset.page = String(pageNumber);
    el.style.aspectRatio = `${cropWidth} / ${base.height}`;
    const canvas = document.createElement("canvas");
    canvas.hidden = true;
    el.append(canvas);
    fragment.append(el);
    pages.set(pageNumber, { pageNumber, el, canvas, rendered: false, rendering: false });
    if ((pageNumber - start + 1) % 64 === 0) {
      report(t("Preparing pages · {0} / {1}", pageNumber - start + 1, doc.numPages - start + 1));
      await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()));
      if (!current()) return null;
    }
  }
  const pageNumber = Math.min(doc.numPages, Math.max(start, Math.floor(preferredPage ?? start)));
  const page = pages.get(pageNumber)!;
  report(t("Rendering page {0}…", pageNumber));
  page.el.style.aspectRatio = await paintPdfPage(await doc.getPage(pageNumber), page.canvas, crop, width);
  page.rendered = true;
  return current() ? { pages, fragment, crop, start, base } : null;
}

export async function documentPageLines(
  doc: any,
  pageNumber: number,
  crop: Crop | null,
  current: () => boolean,
): Promise<LineBox[]> {
  const page = await doc.getPage(pageNumber);
  if (!current()) return [];
  const vp = page.getViewport({ scale: 1 });
  const content = await pdfPageText(page);
  if (!current()) return [];
  const runs: TextRun[] = (content.items as any[])
    .filter(
      (item) =>
        item.str &&
        item.str.trim() &&
        !isPageFolio(item.str, vp.convertToViewportPoint(0, item.transform[5])[1] / vp.height),
    )
    .map((item) => ({
      baseline: item.transform[5],
      height: typeof item.height === "number" ? item.height : 0,
      x: item.transform[4],
      width: typeof item.width === "number" ? item.width : 0,
    }));
  const cropX0 = crop ? crop.x0 : 0;
  const cropWidth = crop ? crop.x1 - crop.x0 : vp.width;
  const lines = groupTextLines(
    runs,
    (y) => vp.convertToViewportPoint(0, y)[1] / vp.height,
    (x) => (x - cropX0) / cropWidth,
  );
  for (const item of content.items as any[]) {
    if (!/^(?:Proof|証明)[.．。]?$/u.test(item.str?.trim() ?? "")) continue;
    const baseline = vp.convertToViewportPoint(0, item.transform[5])[1] / vp.height;
    const line = lines.find((line) => Math.abs(line.baseline - baseline) < 0.004);
    const left = (item.transform[4] - cropX0) / cropWidth;
    if (line && Math.abs(left - line.left) < 0.004)
      line.proofLabelRight = (item.transform[4] + item.width - cropX0) / cropWidth;
  }
  return lines;
}

export function appendPageLinks(
  container: HTMLElement,
  annotations: any[],
  vp: any,
  crop: Crop | null,
  follow: FollowPdfLink,
  terms?: TermLinkContext,
): void {
  const cropX0 = crop?.x0 ?? 0;
  const cropWidth = crop ? crop.x1 - crop.x0 : vp.width;
  for (const annotation of annotations) {
    if (annotation?.subtype !== "Link" || !Array.isArray(annotation.rect)) continue;
    const [x1, y1, x2, y2] = annotation.rect as number[];
    const top = vp.convertToViewportPoint(0, Math.max(y1, y2))[1] / vp.height;
    const bottom = vp.convertToViewportPoint(0, Math.min(y1, y2))[1] / vp.height;
    const left = (Math.min(x1, x2) - cropX0) / cropWidth;
    const right = (Math.max(x1, x2) - cropX0) / cropWidth;
    if (right <= 0 || left >= 1 || bottom <= top) continue;
    const box = document.createElement("a");
    box.className = "pdf-link-box";
    box.style.top = `${(top * 100).toFixed(3)}%`;
    box.style.height = `${((bottom - top) * 100).toFixed(3)}%`;
    box.style.left = `${(Math.max(0, left) * 100).toFixed(3)}%`;
    box.style.width = `${((Math.min(1, right) - Math.max(0, left)) * 100).toFixed(3)}%`;
    if (typeof annotation.url === "string" && annotation.url) {
      const href = safeHref(annotation.url);
      if (!href) continue;
      box.href = href;
      box.target = "_blank";
      box.rel = "noreferrer";
      box.title = annotation.url;
    } else if (annotation.dest) {
      const dest = annotation.dest;
      box.href = "#";
      box.title = typeof dest === "string" ? dest : t("internal link");
      box.addEventListener("click", (event) => {
        if (window.getSelection()?.isCollapsed === false) {
          event.preventDefault();
          event.stopPropagation();
          return;
        }
        event.preventDefault();
        event.stopPropagation();
        const registry = terms?.definitions ? terms.definitions() : project.definitionRegistry;
        const canonical = resolveDefinition(registry, dest)?.canonicalDefinition;
        follow(canonical ?? dest).catch((error) => console.error("[booklink] pdf link", error));
      });
    } else {
      continue;
    }
    if (terms) attachTermLink(box, annotation.dest ?? box.href, terms, follow);
    container.append(box);
  }
}
