// Shared by the browser and build scheduler. Keep the choices in sync with
// tools/viewer_layout_tex.py and VIEWER_LAYOUT_* in the Makefile.
export const PAPER_SIZES = ["default", "a4", "a5", "b5", "b6"] as const;
export const FONT_SIZES = ["default", "10", "11", "12"] as const;
const PROFILE = /-layout-(default|a4|a5|b5|b6)-(default|10|11|12)pt(?=-(?:debug|preview-))/;

export function pdfLayout(path: string): { paper: string; font: string } {
  const match = PROFILE.exec(path);
  return { paper: match?.[1] ?? "default", font: match?.[2] ?? "default" };
}

export function canonicalPdfPath(path: string): string {
  return path.replace(PROFILE, "");
}

export function layoutPdfPath(path: string, paper: string, font: string): string {
  const canonical = canonicalPdfPath(path);
  if (!PAPER_SIZES.includes(paper as (typeof PAPER_SIZES)[number])) paper = "default";
  if (!FONT_SIZES.includes(font as (typeof FONT_SIZES)[number])) font = "default";
  if (paper === "default" && font === "default") return canonical;
  return canonical.replace(
    /(-debug(?:-dark)?|-preview-[A-Za-z0-9_-]+)(?=\.pdf(?:[?#]|$))/,
    `-layout-${paper}-${font}pt$1`,
  );
}
