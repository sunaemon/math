import { termTarget } from "./pdf-chapter.js";

interface Box {
  left: number;
  top: number;
  right: number;
  bottom: number;
}

// PDF link rectangles identify the defined word/formula even when its anchor
// starts in the middle of a sentence. Pick the occurrence nearest that anchor,
// rather than highlighting every later use of the same term on the page.
export async function destinationHighlightBoxes(page: any, destination: any[], name?: string): Promise<Box[]> {
  const viewport = page.getViewport({ scale: 1 });
  const [x, y] = viewport.convertToViewportPoint(destination[2] ?? 0, destination[3] ?? viewport.height);
  const target = termTarget(name);
  if (target && name === target.definition) {
    const annotations = await page.getAnnotations();
    const boxes: Box[] = annotations
      .filter(
        (a: any) =>
          a.subtype === "Link" &&
          (a.dest === target.references || a.dest === target.definition) &&
          Array.isArray(a.rect),
      )
      .map((a: any) => {
        const [x1, y1] = viewport.convertToViewportPoint(a.rect[0], a.rect[1]);
        const [x2, y2] = viewport.convertToViewportPoint(a.rect[2], a.rect[3]);
        return { left: Math.min(x1, x2), right: Math.max(x1, x2), top: Math.min(y1, y2), bottom: Math.max(y1, y2) };
      });
    const distance = (b: Box) => Math.max(b.top - y, y - b.bottom, 0) + Math.max(b.left - x, x - b.right, 0) * 0.2;
    boxes.sort((a, b) => distance(a) - distance(b));
    if (boxes[0] && distance(boxes[0]) < 96) return [boxes[0]];
  }
  // Index entries, headings, and definitions without a self-link still have a
  // text line at the destination. Keep the cue on that line, not the whole page.
  const content = await page.getTextContent();
  const boxes: Box[] = content.items
    .filter((item: any) => item.str?.trim())
    .map((item: any) => {
      const [left, baseline] = viewport.convertToViewportPoint(item.transform[4], item.transform[5]);
      const height = item.height || Math.hypot(item.transform[2], item.transform[3]) || 10;
      return { left, right: left + item.width, top: baseline - height, bottom: baseline + height * 0.2 };
    });
  const distance = (b: Box) => Math.max(b.top - y, y - b.bottom, 0);
  boxes.sort((a, b) => distance(a) - distance(b));
  const nearest = boxes[0];
  if (!nearest) return [];
  const line = boxes.filter((b) => Math.abs(b.bottom - nearest.bottom) < 3);
  return [
    {
      left: Math.min(...line.map((b) => b.left)),
      right: Math.max(...line.map((b) => b.right)),
      top: Math.min(...line.map((b) => b.top)),
      bottom: Math.max(...line.map((b) => b.bottom)),
    },
  ];
}

export function appendDestinationHighlights(container: HTMLElement, boxes: Box[], frame: Box, transient = false): void {
  for (const box of boxes) {
    const left = Math.max(frame.left, box.left - 2);
    const right = Math.min(frame.right, box.right + 2);
    const top = Math.max(frame.top, box.top - 1);
    const bottom = Math.min(frame.bottom, box.bottom + 1);
    if (right <= left || bottom <= top) continue;
    const highlight = document.createElement("div");
    highlight.className = `pdf-destination-highlight${transient ? " is-transient" : ""}`;
    highlight.setAttribute("aria-hidden", "true");
    highlight.style.left = `${((left - frame.left) / (frame.right - frame.left)) * 100}%`;
    highlight.style.top = `${((top - frame.top) / (frame.bottom - frame.top)) * 100}%`;
    highlight.style.width = `${((right - left) / (frame.right - frame.left)) * 100}%`;
    highlight.style.height = `${((bottom - top) / (frame.bottom - frame.top)) * 100}%`;
    container.append(highlight);
    if (transient) setTimeout(() => highlight.remove(), 1800);
  }
}

export async function flashPdfDestination(
  page: any,
  destination: any[],
  name: string | undefined,
  element: HTMLElement,
  crop: { x0: number; x1: number } | null,
  current: () => boolean,
  painted: () => boolean,
): Promise<void> {
  const boxes = await destinationHighlightBoxes(page, destination, name);
  // Start the brief cue only after a lazily rendered page becomes readable.
  const deadline = performance.now() + 5000;
  while (current() && !painted() && performance.now() < deadline)
    await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()));
  if (!current() || !painted() || !element.isConnected) return;
  for (const previous of element.parentElement?.querySelectorAll(".pdf-destination-highlight") ?? []) previous.remove();
  const viewport = page.getViewport({ scale: 1 });
  appendDestinationHighlights(
    element,
    boxes,
    {
      left: crop?.x0 ?? 0,
      right: crop?.x1 ?? viewport.width,
      top: 0,
      bottom: viewport.height,
    },
    true,
  );
}
