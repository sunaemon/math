import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { preloadViewerModules } from "./module-preload.ts";

test("preload follows the static graph once and preserves lazy feature imports", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-preload-"));
  try {
    fs.mkdirSync(path.join(root, "build"));
    for (const [name, source] of Object.entries({
      "view-bootstrap.js":
        "document.documentElement.dataset.viewStarting=1;\n//# sourceMappingURL=view-bootstrap.js.map",
      "styles.css": "body{color:red}/*# sourceMappingURL=styles.css.map */",
      "app.js": 'import{a}from"./shared.js";import "./side.js";import("./lazy.js");',
      "shared.js": 'export{b}from"./nested.js";',
      "side.js": 'import{a}from"./shared.js";',
      "nested.js": 'import "./app.js";',
      "lazy.js": "export const lazy=true;",
    }))
      fs.writeFileSync(path.join(root, "build", name), source);
    const html = preloadViewerModules(
      '<head><script src="./build/view-bootstrap.js"></script><link rel="stylesheet" href="./build/styles.css" /></head><body></body>',
      root,
    );
    assert.ok(html.includes("<script>document.documentElement.dataset.viewStarting=1;"));
    assert.ok(html.includes("<style>body{color:red}</style>"));
    assert.ok(!html.includes("sourceMappingURL"));
    assert.ok(!html.includes('src="./build/view-bootstrap.js"'));
    assert.equal((html.match(/rel="modulepreload"/g) ?? []).length, 4);
    assert.ok(html.includes("./build/nested.js"));
    assert.ok(!html.includes("lazy.js"));
    assert.ok(html.indexOf("nested.js") < html.indexOf("</head>"));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
