import fs from "node:fs";
import path from "node:path";

// Discover only static imports emitted by esbuild. Dynamic features stay lazy;
// hash-named shared modules can be fetched with the document, without waiting
// for each parent module to download and be parsed first.
export function preloadViewerModules(html: string, viewerDir: string): string {
  // Keep the authored HTML readable while eliminating two render-blocking
  // round trips in both the live response and the static export.
  for (const [file, pattern, wrap] of [
    ["view-bootstrap.js", /<script src="\.\/build\/view-bootstrap\.js"><\/script>/, "script"],
    ["styles.css", /<link rel="stylesheet" href="\.\/build\/styles\.css"\s*\/>/, "style"],
  ] as const) {
    try {
      const source = fs
        .readFileSync(path.join(viewerDir, "build", file), "utf8")
        .replace(/\/\/[#@] sourceMappingURL=.*$/gm, "")
        .replace(/\/\*[#@] sourceMappingURL=[\s\S]*?\*\//g, "");
      const safe =
        wrap === "script" ? source.replace(/<\/script/gi, "<\\/script") : source.replace(/<\/style/gi, "\\3c /style");
      html = html.replace(pattern, () => `<${wrap}>${safe}</${wrap}>`);
    } catch {
      // Development fixtures or an incomplete first build keep external URLs.
    }
  }
  const seen = new Set<string>();
  function visit(name: string): void {
    if (!/^[\w.-]+\.js$/.test(name) || seen.has(name)) return;
    let source: string;
    try {
      source = fs.readFileSync(path.join(viewerDir, "build", name), "utf8");
    } catch {
      return;
    }
    seen.add(name);
    for (const match of source.matchAll(/(?:\bfrom\s*|\bimport\s*)["']\.\/([\w.-]+\.js)["']/g)) visit(match[1]);
  }
  visit("app.js");
  const links = [...seen].map((name) => `<link rel="modulepreload" href="./build/${name}">`).join("\n");
  return html.replace("</head>", `${links}\n</head>`);
}
