import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import type { Manifest } from "./projects.ts";

// Cheap fingerprints of the files a derived result is built from, used to
// memoize results that would otherwise be rebuilt identically on every
// manifest request (the definition registry, the chapter titles). Each
// input contributes its path, size and mtime; a missing file contributes a
// marker, so an input appearing or disappearing also changes the stamp.
export function inputStamp(files: readonly string[]): string {
  const hash = createHash("sha256");
  for (const file of files) {
    hash.update(file);
    try {
      const stat = fs.statSync(file);
      hash.update(`\0${stat.size}:${stat.mtimeMs}\0`);
    } catch {
      hash.update("\0missing\0");
    }
  }
  return hash.digest("hex");
}

// The files a project's book manifest declares: the manifest itself and its
// chapter sources, resolved against the repository root. Null when the
// project has no readable book manifest with a chapter list.
export function bookInputFiles(root: string, project: Manifest): { manifest: string; chapters: string[] } | null {
  if (typeof project.bookManifest !== "string" || !project.bookManifest) return null;
  const manifest = path.resolve(root, project.dir, project.bookManifest);
  let chapters: unknown;
  try {
    chapters = JSON.parse(fs.readFileSync(manifest, "utf8")).chapters;
  } catch {
    return null;
  }
  if (!Array.isArray(chapters)) return null;
  const files: string[] = [];
  for (const chapter of chapters) {
    if (typeof chapter === "string" && chapter.endsWith(".md")) files.push(path.resolve(root, chapter));
  }
  return { manifest, chapters: files };
}
