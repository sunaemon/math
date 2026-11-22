// Fixed-height window with one viewport of overscan on either side.
export const MARKER_ROW_HEIGHT = 52;
export function listWindow(count: number, scrollTop: number, height: number, rowHeight = MARKER_ROW_HEIGHT) {
  const viewport = Math.max(rowHeight, height);
  const top = Math.max(0, Math.min(scrollTop, Math.max(0, count * rowHeight - viewport)));
  const page = Math.ceil(viewport / rowHeight);
  const first = Math.floor(top / rowHeight);
  const start = Math.max(0, first - page);
  const end = Math.min(count, Math.ceil((top + viewport) / rowHeight) + page);
  return { start, end, top, before: start * rowHeight, after: (count - end) * rowHeight };
}
