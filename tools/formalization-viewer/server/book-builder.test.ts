import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawn } from "node:child_process";

import { BookBuilder } from "./book-builder.ts";
import type { Manifest } from "./projects.ts";

const MANIFEST: Manifest = {
  mount: "/bk",
  dir: "bk",
  served: { src: ["md", "json"], build: ["pdf", "json"] },
  pdf: "build/bk-debug.pdf",
  sourceMap: "build/bk-sourcemap.json",
};

// Drive BookBuilder against a harmless build command so notify() spawns `true`
// (exit 0, args ignored) instead of a real `make`. env is read in the
// constructor, so set/restore it around each builder.
function withBuilder(
  env: Record<string, string | undefined>,
  body: (builder: BookBuilder, logs: string[]) => Promise<void>,
  manifests: Manifest[] = [MANIFEST],
  root?: string,
): Promise<void> {
  const saved = { ...process.env };
  Object.assign(process.env, { BOOKLINK_MAKE: "true", BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "5", ...env });
  const logs: string[] = [];
  const buildRoot = root ?? fs.mkdtempSync(path.join(os.tmpdir(), "book-builder-test-"));
  const builder = new BookBuilder(buildRoot, manifests, (m) => logs.push(m));
  return body(builder, logs).finally(async () => {
    await builder.shutdown();
    if (!root) fs.rmSync(buildRoot, { recursive: true, force: true });
    process.env = saved;
  });
}

async function waitFor(predicate: () => boolean, timeoutMs = 1000): Promise<void> {
  const start = Date.now();
  while (!predicate()) {
    if (Date.now() - start > timeoutMs) throw new Error("timed out waiting for condition");
    await new Promise((r) => setTimeout(r, 5));
  }
}

const spawned = (logs: string[]): string[] => logs.filter((m) => m.startsWith("book-builder: true "));
const finished = (logs: string[]): string[] => logs.filter((m) => m.includes("build finished"));

test("generated excerpt Markdown does not recursively trigger builds", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.notify("bk/build/source/chapter.md");
      await new Promise((r) => setTimeout(r, 30));
      assert.equal(spawned(logs).length, 0);
      builder.notify("bk/src/original/chapter.md");
      await waitFor(() => finished(logs).length === 1);
    },
    [{ ...MANIFEST, served: { ...MANIFEST.served, "build/source": ["md"] } }],
  ));

test("startup waits for a selection, then builds only the opened book and ignores repeated reports", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      await new Promise((r) => setTimeout(r, 30));
      assert.equal(spawned(logs).length, 0);
      builder.setSelection("s1", "bk/build/bk-debug.pdf");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
      builder.setSelection("s1", "bk/build/bk-debug.pdf");
      await new Promise((r) => setTimeout(r, 30));
      assert.equal(spawned(logs).length, 1);
    },
    [MANIFEST, { ...MANIFEST, dir: "unopened", mount: "/unopened" }],
  ));

test("auto-build disabled also suppresses initial selection builds", () =>
  withBuilder({ BOOKLINK_AUTOBUILD: "0" }, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-debug.pdf");
    builder.notify("bk/src/a.md");
    await new Promise((r) => setTimeout(r, 30));
    assert.equal(spawned(logs).length, 0);
  }));

test("with no selection, a Markdown change builds the debug PDF + source map", () =>
  withBuilder({}, async (builder, logs) => {
    builder.notify("bk/src/polish-space-book/x.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
  }));

test("a release selection builds only the source map (release is never auto-built)", () =>
  withBuilder({}, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-book.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-sourcemap.json"]);
  }));

test("a chapter-preview selection builds that one preview PDF + source map", () =>
  withBuilder({}, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-preview-polish-spaces.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), [
      "book-builder: true bk/build/bk-preview-polish-spaces.pdf bk/build/bk-sourcemap.json",
    ]);
  }));

test("a dark debug selection builds its separate dark PDF and the shared map", () =>
  withBuilder({}, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-debug-dark.pdf");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug-dark.pdf bk/build/bk-sourcemap.json"]);
  }));

test("switching selection to a different PDF rebuilds that target", () =>
  withBuilder({ BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "10" }, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-debug.pdf"); // initial: schedules a build
    builder.setSelection("s1", "bk/build/bk-preview-cantor-baire-space.pdf"); // change: rebuilds the preview
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), [
      "book-builder: true bk/build/bk-preview-cantor-baire-space.pdf bk/build/bk-sourcemap.json",
    ]);
  }));

test("a preview selection whose chapter is not a plain identifier is dropped (no make-target injection)", () =>
  withBuilder({}, async (builder, logs) => {
    // The chapter component becomes the make stem ($*), which the preview recipe
    // interpolates into a shell-evaluated LuaLaTeX command. A selection carrying
    // shell metacharacters must never reach `make`; it is dropped, leaving only
    // the fixed source-map target.
    builder.setSelection("s1", "bk/build/bk-preview-$(touch pwned).pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-sourcemap.json"]);
  }));

test("a project-relative selection (missing the dir prefix) is ignored, falling back to debug", () =>
  withBuilder({}, async (builder, logs) => {
    // The client must report a repo-relative path ("bk/build/..."). A
    // project-relative one ("build/...") matches no job prefix, so the selection
    // is dropped and the build resolves to the debug-PDF default, not the diff.
    builder.setSelection("s1", "build/bk-diff.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
  }));

test("non-source and out-of-tree changes do not build", () =>
  withBuilder({}, async (builder, logs) => {
    builder.notify("bk/build/bk-debug.tex"); // build output, not a source
    builder.notify("bk/lean/Foo.lean"); // Lean tree not served by this manifest
    builder.notify("other/src/x.md"); // a different project's source
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 0);
  }));

const LEAN_MANIFEST: Manifest = {
  mount: "/bk",
  dir: "bk",
  served: { src: ["md", "json"], lean: ["lean"], build: ["pdf", "json"] },
  pdf: "build/bk-debug.pdf",
  sourceMap: "build/bk-sourcemap.json",
};

test("a Lean change in a served lean tree builds the debug PDF + source map", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.notify("bk/lean/PolishSpaceBook/Foo.lean");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
    },
    [LEAN_MANIFEST],
  ));

test("a change to the real file behind a symlinked served tree rebuilds every linking project", async () => {
  // bk/lean is the canonical tree; bkja/lean symlinks the whole dir and
  // bkch/lean/Foo.lean symlinks the single file, mirroring how the translated
  // book and the chapter excerpt share the canonical book's sources.
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "book-builder-test-"));
  try {
    fs.mkdirSync(path.join(root, "bk/lean"), { recursive: true });
    fs.writeFileSync(path.join(root, "bk/lean/Foo.lean"), "");
    fs.mkdirSync(path.join(root, "bkja"));
    fs.symlinkSync(path.join(root, "bk/lean"), path.join(root, "bkja/lean"));
    fs.mkdirSync(path.join(root, "bkch/lean"), { recursive: true });
    fs.symlinkSync(path.join(root, "bk/lean/Foo.lean"), path.join(root, "bkch/lean/Foo.lean"));
    const manifests: Manifest[] = ["bk", "bkja", "bkch"].map((dir) => ({
      mount: `/${dir}`,
      dir,
      served: { lean: ["lean"] },
      pdf: `build/${dir}-debug.pdf`,
      sourceMap: `build/${dir}-sourcemap.json`,
    }));
    await withBuilder(
      {},
      async (builder, logs) => {
        builder.notify("bk/lean/Foo.lean"); // the real path, as watch events report it
        await waitFor(() => finished(logs).length === 1);
        // One merged make: concurrent per-project makes would race on
        // overlapping targets (e.g. a peer-pane PDF).
        assert.deepEqual(spawned(logs), [
          "book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json " +
            "bkja/build/bkja-debug.pdf bkja/build/bkja-sourcemap.json " +
            "bkch/build/bkch-debug.pdf bkch/build/bkch-sourcemap.json",
        ]);
      },
      manifests,
      root,
    );
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("rapid saves within the debounce window coalesce into one build", () =>
  withBuilder({ BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "30" }, async (builder, logs) => {
    builder.notify("bk/src/a.md");
    builder.notify("bk/src/b.md");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 1);
  }));

const TRANSLATED_MANIFEST: Manifest = {
  mount: "/bk-ja",
  dir: "bk-ja",
  served: { src: ["md", "json"], build: ["pdf", "json"] },
  pdf: "build/bk-ja-debug.pdf",
  sourceMap: "build/bk-ja-sourcemap.json",
  parallelPdf: { label: "English PDF", dir: "bk", mount: "/bk", path: "build/bk-debug.pdf" },
};

test("layout choices build isolated variants for both languages and coexist across sessions", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.setSelection("phone", "bk-ja/build/bk-ja-layout-b6-12pt-preview-polish-spaces-dark.pdf");
      builder.setSelection("desktop", "bk-ja/build/bk-ja-layout-a4-10pt-debug.pdf");
      await waitFor(() => finished(logs).length === 1);
      const command = spawned(logs)[0];
      for (const target of [
        "bk-ja/build/bk-ja-layout-b6-12pt-preview-polish-spaces-dark.pdf",
        "bk-ja/build/bk-ja-layout-a4-10pt-debug.pdf",
        "bk/build/bk-layout-b6-12pt-preview-polish-spaces-dark.pdf",
        "bk/build/bk-layout-a4-10pt-debug.pdf",
      ])
        assert.ok(command.includes(target), command);
      assert.ok(!command.includes(" bk/build/bk-debug.pdf"));
      assert.ok(!command.includes(" bk-ja/build/bk-ja-debug.pdf"));
    },
    [TRANSLATED_MANIFEST, MANIFEST],
  ));

test("restoring a translated chapter preview builds it and its peer without whole-book PDFs", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.setSelection("s1", "bk-ja/build/bk-ja-preview-polish-spaces.pdf");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), [
        "book-builder: true bk-ja/build/bk-ja-preview-polish-spaces.pdf bk-ja/build/bk-ja-sourcemap.json " +
          "bk/build/bk-preview-polish-spaces.pdf bk/build/bk-sourcemap.json",
      ]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("a dark translated chapter builds the matching dark peer chapter", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.setSelection("s1", "bk-ja/build/bk-ja-preview-polish-spaces-dark.pdf");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), [
        "book-builder: true bk-ja/build/bk-ja-preview-polish-spaces-dark.pdf bk-ja/build/bk-ja-sourcemap.json " +
          "bk/build/bk-preview-polish-spaces-dark.pdf bk/build/bk-sourcemap.json",
      ]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("a session on the translated book keeps the peer project's debug PDF fresh", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      // The session views the translated book; its release-PDF selection in the
      // canonical project would otherwise suppress the debug-PDF default there.
      builder.setSelection("s1", "bk-ja/build/bk-ja-debug.pdf");
      builder.setSelection("s2", "bk/build/bk-book.pdf");
      await waitFor(() => finished(logs).length === 1);
      logs.length = 0;
      builder.notify("bk/src/polish-space-book/x.md");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("a translated-book preview selection implies the peer book's preview of that chapter, not its debug", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.setSelection("s1", "bk-ja/build/bk-ja-preview-polish-spaces.pdf");
      await waitFor(() => finished(logs).length === 1);
      logs.length = 0;
      builder.notify("bk/src/polish-space-book/x.md");
      await waitFor(() => finished(logs).length === 1);
      // The implied preview stands in for the no-selection debug default.
      assert.deepEqual(spawned(logs), [
        "book-builder: true bk/build/bk-preview-polish-spaces.pdf bk/build/bk-sourcemap.json",
      ]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("switching the translated book to a chapter preview also builds the peer book's preview", () =>
  withBuilder(
    { BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "10" },
    async (builder, logs) => {
      builder.setSelection("s1", "bk-ja/build/bk-ja-debug.pdf"); // initial: schedules a build
      builder.setSelection("s1", "bk-ja/build/bk-ja-preview-polish-spaces.pdf");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), [
        "book-builder: true bk-ja/build/bk-ja-preview-polish-spaces.pdf bk-ja/build/bk-ja-sourcemap.json " +
          "bk/build/bk-preview-polish-spaces.pdf bk/build/bk-sourcemap.json",
      ]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("a peer-implied preview whose chapter is not a plain identifier falls back to the peer debug PDF", () =>
  withBuilder(
    {},
    async (builder, logs) => {
      builder.setSelection("s1", "bk-ja/build/bk-ja-preview-$(touch pwned).pdf");
      await waitFor(() => finished(logs).length === 1);
      assert.ok(spawned(logs).every((line) => !line.includes("$(touch")));
      logs.length = 0;
      builder.notify("bk/src/polish-space-book/x.md");
      await waitFor(() => finished(logs).length === 1);
      assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
    },
    [MANIFEST, TRANSLATED_MANIFEST],
  ));

test("BOOKLINK_AUTOBUILD=0 disables auto-building", () =>
  withBuilder({ BOOKLINK_AUTOBUILD: "0" }, async (builder, logs) => {
    builder.notify("bk/src/a.md");
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 0);
  }));

test("a failed build preserves stdout, stderr and exit status in each project's log", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "book-builder-test-"));
  try {
    const command = path.join(root, "fail-build");
    fs.writeFileSync(command, "#!/bin/sh\necho build-output\necho build-diagnostic >&2\nexit 1\n", { mode: 0o755 });
    await withBuilder(
      { BOOKLINK_MAKE: command },
      async (builder, logs) => {
        builder.setSelection("s1", "bk-ja/build/bk-ja-debug.pdf");
        builder.setSelection("s1", "bk-ja/build/bk-ja-preview-concrete-cantor-baire-models.pdf");
        await waitFor(() => finished(logs).length === 1);
        for (const dir of ["bk", "bk-ja"]) {
          const saved = fs.readFileSync(path.join(root, dir, "build/viewer-build.log"), "utf8");
          assert.match(saved, /build-output/);
          assert.match(saved, /build-diagnostic/);
          assert.match(saved, /finished \(exit 1\)/);
        }
      },
      [MANIFEST, TRANSLATED_MANIFEST],
      root,
    );
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("a detached viewer builds successfully after its terminal output pipes close", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "book-builder-test-"));
  try {
    const command = path.join(root, "build");
    fs.writeFileSync(command, "#!/bin/sh\nset -e\necho build-output\necho build-diagnostic >&2\n", { mode: 0o755 });
    const script = path.join(root, "viewer.mjs");
    fs.writeFileSync(
      script,
      `import fs from 'node:fs';
import { BookBuilder } from ${JSON.stringify(new URL("./book-builder.ts", import.meta.url).href)};
// The live server ignores broken terminal pipes while continuing to serve.
process.on('uncaughtException', error => {
  if (error.code !== 'EPIPE') process.exit(2);
});
const builder = new BookBuilder(${JSON.stringify(root)}, [${JSON.stringify(MANIFEST)}], () => {}, status => {
  if (status.state === 'building') return;
  fs.writeFileSync(${JSON.stringify(path.join(root, "status"))}, status.state);
  void builder.shutdown().then(() => process.exit(0));
});
builder.notify('bk/src/chapter.md');
setTimeout(() => process.exit(3), 5000).unref();
`,
    );
    const proc = spawn(process.execPath, [script], {
      env: { ...process.env, BOOKLINK_MAKE: command, BOOKLINK_AUTOBUILD: "1", BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "5" },
      stdio: ["ignore", "pipe", "pipe"],
    });
    proc.stdout.destroy();
    proc.stderr.destroy();
    const code = await new Promise<number | null>((resolve, reject) => {
      proc.on("error", reject);
      proc.on("close", resolve);
    });
    assert.equal(code, 0);
    assert.equal(fs.readFileSync(path.join(root, "status"), "utf8"), "done");
    const saved = fs.readFileSync(path.join(root, "bk/build/viewer-build.log"), "utf8");
    assert.match(saved, /build-output/);
    assert.match(saved, /build-diagnostic/);
    assert.match(saved, /finished \(exit 0\)/);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("continuous changes cannot postpone a build past the maximum wait", () =>
  withBuilder(
    { BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "1000", BOOKLINK_AUTOBUILD_MAX_WAIT_MS: "60" },
    async (builder, logs) => {
      builder.setSelection("editing", "bk/build/bk-debug.pdf");
      let changes = 0;
      const timer = setInterval(() => {
        changes++;
        builder.notify("bk/src/chapter.md");
      }, 5);
      try {
        await waitFor(() => finished(logs).length >= 1, 800);
        assert.ok(changes >= 2);
      } finally {
        clearInterval(timer);
      }
    },
  ));
