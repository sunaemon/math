import assert from "node:assert/strict";
import test from "node:test";
import path from "node:path";
import { bookReferences } from "./references.ts";
import { readProject } from "./projects.ts";
import { referenceKey, referenceUrl, resolveReference } from "../src/link-preview.ts";

test("citation destinations and DOI links resolve to the book bibliography", () => {
  const root = path.resolve(import.meta.dirname, "../../..");
  const registry = bookReferences(root, readProject(root, "polish-space"));
  const reference = resolveReference(registry, "cite.0@ref-Kechris1995");
  assert.ok(reference, "Pandoc bibliography extraction must produce real entries");
  assert.match(reference.source, /Classical descriptive set theory/);
  assert.ok(reference.html);
  assert.equal(bookReferences(root, readProject(root, "polish-space")), registry);
  assert.equal(referenceKey("ref-Kechris1995"), "Kechris1995");
  assert.equal(referenceKey([1]), null);
  assert.equal(referenceUrl("https://dx.doi.org/10.1000/ABC#section"), "https://doi.org/10.1000/abc");
  assert.equal(referenceUrl("javascript:alert(1)"), "");
});
