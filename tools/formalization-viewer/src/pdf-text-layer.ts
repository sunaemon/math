import { pdfPageText } from "./pdf-page-text.js";
// PDF.js's native text layout preserves reading order, glyph transforms and
// selection. Keep it at CSS resolution; only the canvas uses device pixels.
const layers = new WeakMap<HTMLCanvasElement, { host: HTMLElement; task: any }>();
const PDFJS = new URL("../vendor/pdfjs/pdf.mjs", import.meta.url).href;
export async function renderPdfTextLayer(
  page: any,
  canvas: HTMLCanvasElement,
  crop: { x0: number; x1: number } | null,
  width: number,
): Promise<void> {
  const previous = layers.get(canvas);
  previous?.task?.cancel();
  previous?.host.remove();
  const host = document.createElement("div");
  host.className = "pdf-text-host";
  const layer = document.createElement("div");
  layer.className = "pdf-text-layer";
  host.append(layer);
  const record = { host, task: null as any };
  layers.set(canvas, record);
  const base = page.getViewport({ scale: 1 });
  const scale = (width > 0 ? width : 240) / (crop ? crop.x1 - crop.x0 : base.width);
  layer.style.setProperty("--total-scale-factor", String(scale));
  layer.style.left = `${-(crop?.x0 ?? 0) * scale}px`;
  const pdfjs = await import(PDFJS);
  if (layers.get(canvas) !== record) return;
  canvas.parentElement?.append(host);
  const text = await pdfPageText(page);
  if (layers.get(canvas) !== record) return;
  const task = new pdfjs.TextLayer({
    textContentSource: text,
    container: layer,
    viewport: page.getViewport({ scale }),
  });
  record.task = task;
  layer.style.width = `${base.width * scale}px`;
  layer.style.height = `${base.height * scale}px`;
  try {
    await task.render();
  } catch (error) {
    if (layers.get(canvas) === record) throw error;
  }
}

// The transparent text spans sit above marker bands for selection. Resolve the
// band underneath a text span so plain clicks/hover retain existing navigation.
export function pdfOverlayAtPoint(target: Element | null, selector: string, x: number, y: number): HTMLElement | null {
  const direct = target?.closest(selector) as HTMLElement | null;
  if (direct) return direct;
  if (!target?.closest(".pdf-text-host")) return null;
  const page = target.closest(".pdf-page");
  for (const overlay of page?.querySelectorAll<HTMLElement>(selector) ?? []) {
    const rect = overlay.getBoundingClientRect();
    if (x >= rect.left && x <= rect.right && y >= rect.top && y <= rect.bottom) return overlay;
  }
  return null;
}
