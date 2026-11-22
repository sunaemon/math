import assert from "node:assert/strict";
import test from "node:test";
import { projectRelativePath } from "./repo-path.ts";

test("hosted chapter URLs match manifest paths under a GitHub Pages prefix", () => {
  const relative = "build/polish-space-book-preview-polish-spaces.pdf";
  const hosted = "/math/polish-space/" + relative;
  const normalized = projectRelativePath(hosted, "polish-space", "/Users/author/math-private", "/math/polish-space");
  assert.equal(normalized, relative);
  assert.equal([relative].includes(normalized), true, "the Chapter control must remain enabled");
  assert.equal("/math/polish-space/" + normalized, hosted, "normalization must not duplicate the site prefix");
});

test("live URLs, source paths and project-relative paths retain their meaning", () => {
  const rel = "src/chapter.md";
  for (const value of [rel, "polish-space/" + rel, "/polish-space/" + rel, "/repo/polish-space/" + rel])
    assert.equal(projectRelativePath(value, "polish-space", "/repo", "/polish-space"), rel);
  assert.equal(projectRelativePath("/math/polish-space", "polish-space", "/repo", "/math/polish-space"), "");
  assert.equal(projectRelativePath(null, "polish-space", "/repo", "/math/polish-space"), "");
  assert.equal(
    projectRelativePath("/math/polish-space-other/file", "polish-space", "/repo", "/math/polish-space"),
    "math/polish-space-other/file",
  );
});
