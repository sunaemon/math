import fs from "node:fs";
import path from "node:path";
import type { Manifest } from "./projects.ts";
import { bookInputFiles, inputStamp } from "./input-stamp.ts";

// Read only chapter headers; the selector must not fetch entire books or wait
// for a PDF/source-map build just to display their titles.
// Memoized on the same input stamp as the definition registry: a manifest
// request otherwise re-reads the head of every chapter on every tab load
// and reconnect.
const titlesCache = new Map<string, { stamp: string; titles: Record<string, string> }>();

export function chapterTitles(root: string, project: Manifest): Record<string, string> {
  const inputs = bookInputFiles(root, project);
  let stamp: string | null = null;
  const key = `${root}\0${project.dir}\0${String(project.bookManifest ?? "")}`;
  if (inputs) {
    stamp = inputStamp([inputs.manifest, ...inputs.chapters]);
    const cached = titlesCache.get(key);
    if (cached && cached.stamp === stamp) return cached.titles;
  }
  const titles = readChapterTitles(root, project);
  if (stamp !== null) titlesCache.set(key, { stamp, titles });
  return titles;
}

function readChapterTitles(root: string, project: Manifest): Record<string, string> {
  const titles: Record<string, string> = {};
  const withinRoot = (file: string): string => {
    const real = fs.realpathSync(file);
    const relative = path.relative(root, real);
    if (relative.startsWith("..") || path.isAbsolute(relative)) throw new Error("Source outside repository");
    return real;
  };
  let chapters: unknown;
  try {
    const manifest = withinRoot(path.join(root, project.dir, String(project.bookManifest ?? "")));
    chapters = JSON.parse(fs.readFileSync(manifest, "utf8")).chapters;
  } catch {
    return titles;
  }
  if (!Array.isArray(chapters)) return titles;
  for (const chapter of chapters) {
    if (typeof chapter !== "string" || !chapter.endsWith(".md")) continue;
    try {
      const file = withinRoot(path.resolve(root, chapter));
      const fd = fs.openSync(file, "r");
      let header: string;
      try {
        const buffer = Buffer.alloc(8192);
        header = buffer.subarray(0, fs.readSync(fd, buffer, 0, buffer.length, 0)).toString("utf8");
      } finally {
        fs.closeSync(fd);
      }
      const title = /^#\s+(.+)$/m
        .exec(header)?.[1]
        .replace(/\s+\{[^{}]*\}\s*$/, "")
        .replace(/\s+#+\s*$/, "")
        .replace(/--/g, "–")
        .trim();
      if (title) titles[path.basename(chapter, ".md")] = title;
    } catch {
      // Missing chapters retain the filename fallback in the viewer.
    }
  }
  return titles;
}
