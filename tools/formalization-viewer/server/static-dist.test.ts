import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";
import { assertDistDestination, parseArgs } from "./static-dist.ts";

const SCRIPT = fileURLToPath(new URL("./static-dist.ts", import.meta.url));

function project(root: string): void {
  for (const name of ["book", "other"]) {
    fs.mkdirSync(path.join(root, name, "src"), { recursive: true });
    fs.writeFileSync(
      path.join(root, name, "manifest.json"),
      JSON.stringify({ mount: `/${name}`, dir: name, served: { src: ["md"] } }),
    );
    fs.writeFileSync(path.join(root, name, "src/chapter.md"), "source");
  }
  const viewer = path.join(root, "tools/formalization-viewer");
  for (const dir of ["build", "src", "server", "fixtures", "e2e", "vendor"]) {
    fs.mkdirSync(path.join(viewer, dir), { recursive: true });
    fs.writeFileSync(path.join(viewer, dir, "file.txt"), dir);
  }
  fs.mkdirSync(path.join(viewer, "vendor/treesitter"), { recursive: true });
  fs.writeFileSync(path.join(viewer, "vendor/treesitter/runtime.wasm"), "build-only");
  fs.writeFileSync(path.join(viewer, "index.html"), "<head></head>");
  fs.copyFileSync(new URL("../ai-catalog.json", import.meta.url), path.join(viewer, "ai-catalog.json"));
  fs.writeFileSync(
    path.join(viewer, "build/app.js"),
    'import { value } from "./chunk-EXAMPLE.js"; console.log(value);',
  );
  fs.writeFileSync(path.join(viewer, "build/chunk-EXAMPLE.js"), "export const value = 42;");
  fs.writeFileSync(path.join(viewer, "build/chat-client.js"), "// browser-only client");
  fs.writeFileSync(path.join(viewer, "build/chat-jwks.js"), "// public verification keys");
  fs.mkdirSync(path.join(root, "build/viewer-private-chat"), { recursive: true });
  fs.writeFileSync(path.join(root, "build/viewer-private-chat/legacy.json"), "test-secret-not-for-export");
}

function build(root: string, dist: string) {
  return spawnSync(process.execPath, [SCRIPT, "--root", root, "--dist", dist, "--skip-lsp-cache"], {
    env: { ...process.env, BOOKLINK_PROJECT: "book" },
    encoding: "utf-8",
  });
}

test("dist rejects absent values and never replaces sources, metadata or external paths", () => {
  for (const option of ["--root", "--dist"]) assert.throws(() => parseArgs([option]), /requires a value/);
  assert.throws(() => parseArgs(["--unknown"]), /Unknown option/);
  const base = fs.mkdtempSync(path.join(os.tmpdir(), "dist-guard-"));
  const root = path.join(base, "repo");
  fs.mkdirSync(root);
  project(root);
  fs.mkdirSync(path.join(root, ".git"));
  fs.mkdirSync(path.join(base, "external"));
  fs.symlinkSync(path.join(base, "external"), path.join(root, "external-link"), "dir");
  try {
    for (const target of [
      root,
      base,
      path.join(root, ".git"),
      path.join(root, "book"),
      path.join(root, "external-link/out"),
    ]) {
      assert.throws(() => assertDistDestination(root, target), /repository|non-viewer/, target);
    }
    const result = build(root, root);
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /strictly inside/);
    assert.equal(fs.readFileSync(path.join(root, "book/src/chapter.md"), "utf-8"), "source");
  } finally {
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("a single-project dist excludes test assets and can be safely rebuilt", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "dist-build-"));
  try {
    project(root);
    const output = path.join(root, "dist");
    for (let i = 0; i < 2; i += 1) {
      const result = build(root, output);
      assert.equal(result.status, 0, result.stderr);
      assert.match(result.stdout, /book \(single-project export\)/);
      assert.equal(fs.readFileSync(path.join(output, "book/src/chapter.md"), "utf-8"), "source");
      assert.equal(fs.existsSync(path.join(output, "other")), false);
      for (const name of ["server", "fixtures", "e2e"])
        assert.equal(fs.existsSync(path.join(output, "book", name)), false);
      assert.equal(fs.existsSync(path.join(output, "book/vendor/file.txt")), true);
      assert.equal(fs.existsSync(path.join(output, "book/vendor/treesitter")), false);
      const catalog = JSON.parse(fs.readFileSync(path.join(output, "book/ai-catalog.json"), "utf8"));
      assert.equal(catalog.specVersion, "1.0");
      assert.deepEqual(JSON.parse(fs.readFileSync(path.join(output, ".well-known/ai-catalog.json"), "utf8")), catalog);
      assert.match(fs.readFileSync(path.join(output, "book/build/app.js"), "utf8"), /chunk-EXAMPLE\.js/);
      assert.equal(
        fs.readFileSync(path.join(output, "book/build/chunk-EXAMPLE.js"), "utf8"),
        "export const value = 42;",
      );
      assert.equal(fs.existsSync(path.join(output, "book/build/chat-client.js")), true);
      assert.equal(fs.existsSync(path.join(output, "book/build/chat-jwks.js")), true);
      assert.equal(fs.existsSync(path.join(output, "build/viewer-private-chat")), false);
      assert.equal(JSON.parse(fs.readFileSync(path.join(output, "book/manifest.json"), "utf-8")).static, true);
    }
    // The previous tool emitted .nojekyll + static manifest but no marker.
    fs.rmSync(path.join(output, ".formalization-viewer-dist.json"));
    assert.equal(build(root, output).status, 0);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("static export cannot copy a served symlink outside the repository", () => {
  const base = fs.mkdtempSync(path.join(os.tmpdir(), "dist-source-"));
  const root = path.join(base, "repo");
  fs.mkdirSync(root);
  project(root);
  const secret = path.join(base, "external.md");
  fs.writeFileSync(secret, "private external content");
  fs.symlinkSync(secret, path.join(root, "book/src/leak.md"));
  try {
    const output = path.join(root, "dist");
    const result = build(root, output);
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /escapes the repository/);
    assert.equal(fs.existsSync(path.join(output, "book/src/leak.md")), false);
    assert.equal(fs.readFileSync(secret, "utf-8"), "private external content");
  } finally {
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("static export bundles precomputed Japanese search with a Trusted Types worker adapter", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "dist-search-"));
  try {
    project(root);
    const manifestPath = path.join(root, "book/manifest.json");
    const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
    manifest.bookManifest = "src/book.json";
    fs.writeFileSync(manifestPath, JSON.stringify(manifest));
    fs.writeFileSync(
      path.join(root, "book/src/book.json"),
      JSON.stringify({ source: "book/src/master.md", chapters: ["book/src/chapter.md"] }),
    );
    fs.writeFileSync(path.join(root, "book/src/master.md"), "---\nlang: ja-JP\n---\n");
    fs.writeFileSync(path.join(root, "book/src/chapter.md"), "# 日本語の章\n\n可算稠密集合を取る。\n");
    const output = path.join(root, "dist");
    const result = build(root, output);
    assert.equal(result.status, 0, result.stderr);
    const search = path.join(output, "book/pagefind");
    const engine = fs.readFileSync(path.join(search, "pagefind.js"), "utf8");
    assert.match(engine, /trustedScriptURL\(workerUrl\)/);
    assert.match(engine, /\.\.\/build\/safe-script-url\.js/);
    assert.ok(fs.readdirSync(search).some((file) => file.startsWith("wasm.") && file.endsWith(".pagefind")));
    const entry = JSON.parse(fs.readFileSync(path.join(search, "pagefind-entry.json"), "utf8"));
    assert.ok(entry.languages.ja);
    assert.equal(fs.existsSync(path.join(output, "book/server")), false);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
