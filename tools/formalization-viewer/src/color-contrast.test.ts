import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";

const rgb = (hex: string) => [1, 3, 5].map((i) => parseInt(hex.slice(i, i + 2), 16));
const luminance = (color: number[]) => {
  const linear = color.map((value) => {
    const v = value / 255;
    return v <= 0.04045 ? v / 12.92 : ((v + 0.055) / 1.055) ** 2.4;
  });
  return linear.reduce((sum, value, i) => sum + value * [0.2126, 0.7152, 0.0722][i], 0);
};

test("light source text meets WCAG AA against plain and active marker backgrounds", () => {
  const css = fs.readFileSync(new URL("../styles.css", import.meta.url), "utf8").split(':root[data-theme="dark"]')[0];
  const palette = new Map(
    Array.from(css.matchAll(/--([\w-]+): (#[0-9a-f]{6})/g), (match) => [match[1], rgb(match[2])]),
  );
  const marks = fs.readFileSync(new URL("./source-render.ts", import.meta.url), "utf8");
  const colors = Array.from(marks.matchAll(/"(\d+), (\d+), (\d+)"/g), (m) => m.slice(1).map(Number));
  colors.push([120, 124, 134]);
  const backgrounds = [palette.get("code-bg")!, palette.get("code-panel")!];
  backgrounds.push(
    ...backgrounds.flatMap((bg) => colors.map((color) => bg.map((v, i) => Math.round(v * 0.8 + color[i] * 0.2)))),
  );
  for (const [name, fg] of palette) {
    if (!/^(code-(fg|muted|log-fg)|syntax-)/.test(name)) continue;
    for (const bg of backgrounds) {
      const ratio = (luminance(bg) + 0.05) / (luminance(fg) + 0.05);
      assert.ok(ratio >= 4.5, `${name} contrast ${ratio.toFixed(2)} must be at least 4.5:1`);
    }
  }
});
