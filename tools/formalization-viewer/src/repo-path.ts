// Normalize source paths and hosted viewer URLs to project-relative paths.
export function projectRelativePath(
  path: string | null | undefined,
  dir: string,
  root: string,
  publicMount: string,
): string {
  if (!path) return "";
  if (publicMount && (path === publicMount || path.startsWith(publicMount + "/")))
    return path.slice(publicMount.length).replace(/^\/+/, "");
  let rel = root && path.startsWith(root + "/") ? path.slice(root.length + 1) : path.replace(/^\/+/, "");
  if (dir && rel === dir) return "";
  if (dir && rel.startsWith(dir + "/")) rel = rel.slice(dir.length + 1);
  return rel;
}
