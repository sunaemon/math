import { randomBytes } from "node:crypto";
import fs from "node:fs";
import path from "node:path";

// Publish complete files in one rename, leaving the previous version intact if
// generation fails. A unique sibling keeps concurrent writers independent.
export function atomicWrite(file: string, text: string): void {
  const temporary = `${file}.${process.pid}.${randomBytes(6).toString("hex")}.tmp`;
  const descriptor = fs.openSync(temporary, "wx");
  try {
    try {
      fs.writeFileSync(descriptor, text);
    } finally {
      fs.closeSync(descriptor);
    }
    fs.renameSync(temporary, file);
  } finally {
    fs.rmSync(temporary, { force: true });
  }
}

export function resolvedDestination(destination: string): string {
  let ancestor = path.resolve(destination);
  const missing: string[] = [];
  while (!fs.existsSync(ancestor)) {
    const parent = path.dirname(ancestor);
    if (parent === ancestor) throw new Error(`Cannot resolve destination: ${destination}`);
    missing.unshift(path.basename(ancestor));
    ancestor = parent;
  }
  return path.join(fs.realpathSync(ancestor), ...missing);
}

export function assertSourceWithinRoot(root: string, file: string): void {
  const relative = path.relative(fs.realpathSync(root), fs.realpathSync(file));
  if (relative === ".." || relative.startsWith(`..${path.sep}`) || path.isAbsolute(relative)) {
    throw new Error(`Served file escapes the repository: ${file}`);
  }
}
