export interface FormulaRect {
  left: number;
  top: number;
  right: number;
  bottom: number;
}
// PDF marked-content tags originate from the source parser and travel on TeX
// math nodes through layout. The text is never compared with a guessed formula.
export function taggedFormulaRects(content: any, transform: number[]): Map<string, FormulaRect[]> {
  const stack: Array<string | null> = [];
  const boxes = new Map<string, FormulaRect[]>();
  const point = (x: number, y: number) => ({
    x: transform[0] * x + transform[2] * y + transform[4],
    y: transform[1] * x + transform[3] * y + transform[5],
  });
  for (const item of content.items ?? []) {
    if (item.type === "beginMarkedContent" || item.type === "beginMarkedContentProps") {
      stack.push(typeof item.tag === "string" && item.tag.startsWith("BookFormula-") ? item.tag : null);
      continue;
    }
    if (item.type === "endMarkedContent") {
      stack.pop();
      continue;
    }
    const tag = stack.findLast((value) => value !== null);
    if (!tag || !item.str || !item.transform || !(item.width > 0)) continue;
    const [a, b, c, d, x, y] = item.transform;
    const horizontal = Math.hypot(a, b) || 1;
    const style = content.styles?.[item.fontName] ?? {};
    const ascent = style.ascent ?? 0.85,
      descent = style.descent ?? -0.2;
    const points = [0, item.width].flatMap((width) =>
      [ascent, descent].map((height) =>
        point(x + (width * a) / horizontal + height * c, y + (width * b) / horizontal + height * d),
      ),
    );
    const rect = {
      left: Math.min(...points.map((p) => p.x)),
      right: Math.max(...points.map((p) => p.x)),
      top: Math.min(...points.map((p) => p.y)),
      bottom: Math.max(...points.map((p) => p.y)),
    };
    if (!(rect.bottom > rect.top)) continue;
    const existing = boxes.get(tag) ?? [];
    let merged = rect;
    for (let i = existing.length - 1; i >= 0; i--) {
      const previous = existing[i];
      if (
        previous.top <= merged.bottom &&
        merged.top <= previous.bottom &&
        previous.left <= merged.right + 4 &&
        merged.left <= previous.right + 4
      ) {
        merged = {
          left: Math.min(previous.left, merged.left),
          right: Math.max(previous.right, merged.right),
          top: Math.min(previous.top, merged.top),
          bottom: Math.max(previous.bottom, merged.bottom),
        };
        existing.splice(i, 1);
      }
    }
    existing.push(merged);
    boxes.set(tag, existing);
  }
  return boxes;
}
