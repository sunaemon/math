import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";

import { Projects, walkFiles } from "./projects.ts";

test("a translated project can share another project's Lean root", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-projects-"));
  try {
    for (const dir of ["english", "japanese"]) fs.mkdirSync(path.join(root, dir));
    fs.writeFileSync(
      path.join(root, "english", "manifest.json"),
      JSON.stringify({ mount: "/english", dir: "english" }),
    );
    fs.writeFileSync(
      path.join(root, "japanese", "manifest.json"),
      JSON.stringify({ mount: "/japanese", dir: "japanese", lspDir: "english" }),
    );

    const projects = new Projects(root, "japanese");
    assert.equal(projects.lspRoots.get("japanese"), path.join(root, "english"));
    assert.equal(projects.defaultLspRoot, path.join(root, "english"));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

function fixture(run: (projects: Projects, root: string) => void): void {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-path-boundary-"));
  try {
    fs.mkdirSync(path.join(root, "book"));
    fs.mkdirSync(path.join(root, "tools/formalization-viewer"), { recursive: true });
    fs.writeFileSync(path.join(root, "tools/formalization-viewer/index.html"), "viewer");
    fs.writeFileSync(
      path.join(root, "book/manifest.json"),
      JSON.stringify({
        mount: "/site",
        served: { src: ["md", "json"], build: ["pdf", "json"] },
        flat: ["build"],
      }),
    );
    run(new Projects(root), root);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
}

test("allowlist normalization stays inside declared source and flat build paths", () => {
  fixture((projects) => {
    for (const [url, allowed] of [
      ["/book/src/chapter.md", true],
      ["/book/src/sub/chapter.md", true],
      ["/book/build/book.pdf", true],
      ["/book/build/nested/book.pdf", false],
      ["/book/src/../../private.md", false],
      ["/book/src/%2e%2e/%2e%2e/private.md", false],
      ["/book/src/..%2f..%2fprivate.md", false],
      ["/book/src/chapter.MD", false],
      ["/book/src/chapter.md?version=1#section", true],
      ["/book//src/chapter.md", true],
      ["//book/src/chapter.md", false],
      ["/book/src/chapter.md/private.txt", false],
      ["/other/src/chapter.md", false],
      ["/book/manifest.json", true],
    ] as const) {
      assert.equal(projects.isAllowedPath(url), allowed, url);
    }
  });
});

test("mount routing distinguishes viewer assets, project sources and escaping paths", () => {
  fixture((projects) => {
    for (const [url, expected] of [
      ["/site/", "/tools/formalization-viewer/"],
      ["/site/index.html", "/tools/formalization-viewer/index.html"],
      ["/site/manifest.json", "/book/manifest.json"],
      ["/site/src/chapter.md", "/book/src/chapter.md"],
      ["/site-other/src/chapter.md", "/site-other/src/chapter.md"],
      ["/site/../../private.md", "/site/../../private.md"],
      ["/site/%2e%2e/%2e%2e/private.md", "/site/%2e%2e/%2e%2e/private.md"],
      ["/site/%2fprivate.md", "/site/%2fprivate.md"],
    ]) {
      assert.equal(projects.applyMount(url), expected, url);
    }
  });
});

test("both project directory fields reject traversal and non-string values", () => {
  fixture((_projects, root) => {
    for (const field of ["dir", "lspDir"]) {
      for (const value of ["..", ".", "../other", "a/b", "/absolute", "", null, 42, ["book"]]) {
        fs.writeFileSync(path.join(root, "book/manifest.json"), JSON.stringify({ mount: "/site", [field]: value }));
        assert.throws(() => new Projects(root), /top-level project directory/, `${field}=${JSON.stringify(value)}`);
      }
    }
  });
});

test("manifest paths cannot route or copy files outside their project", () => {
  fixture((_projects, root) => {
    for (const invalid of [
      { mount: "/../outside" },
      { mount: "/site/../../outside" },
      { mount: "//site" },
      { mount: "/site/" },
      { served: { "../outside": ["md"] } },
      { served: { src: "md" } },
      { served: { src: [42] } },
      { flat: ["../outside"] },
      { dir: "other-project" },
    ]) {
      fs.writeFileSync(path.join(root, "book/manifest.json"), JSON.stringify({ mount: "/site", ...invalid }));
      assert.throws(() => new Projects(root), /mount|served|flat|dir/, JSON.stringify(invalid));
    }
  });
});

test("shared file walking handles directory cycles, hidden trees and broken links", () => {
  fixture((_projects, root) => {
    const tree = path.join(root, "tree");
    fs.mkdirSync(path.join(tree, "sub"), { recursive: true });
    fs.mkdirSync(path.join(tree, ".cache"));
    fs.writeFileSync(path.join(tree, "sub/file.lean"), "source");
    fs.writeFileSync(path.join(tree, ".cache/hidden.lean"), "cache");
    fs.symlinkSync(tree, path.join(tree, "sub/loop"), "dir");
    fs.symlinkSync(path.join(tree, "missing"), path.join(tree, "broken.lean"));
    const relative = (files: Iterable<string>): string[] => [...files].map((file) => path.relative(tree, file)).sort();
    assert.deepEqual(relative(walkFiles(tree)), [".cache/hidden.lean", "sub/file.lean"]);
    assert.deepEqual(relative(walkFiles(tree, (name) => !name.startsWith("."))), ["sub/file.lean"]);
  });
});
