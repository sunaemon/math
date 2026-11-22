// Pure decision logic for the Ctrl/Cmd+C copy-TeX shortcut, split out of
// app.ts / parallel-pdf.ts (which touch the DOM at import) so it can be unit
// tested directly with `node --test` (copy-tex.test.ts).

// Which document the shortcut copies from: the pane the reader last selected a
// marker in. Selecting a marker in the peer PDF pane (e.g. the English PDF
// beside a translated book) chooses the peer document; selecting anywhere else
// — the project's own PDF, the md/lean/tex panes — chooses the project's own
// tex. The peer choice additionally requires a peer sourcemap and the peer
// pane still being displayed, so hiding the pane reverts to the project.
export function copyTexSource(
  hasPeerMap: boolean,
  origin: "project" | "peer",
  visiblePanes: string[],
): "peer" | "project" {
  return hasPeerMap && origin === "peer" && visiblePanes.includes("pdf-peer") ? "peer" : "project";
}

// The path of a peer texMatch.source relative to the peer project's mount:
// strip the peer map's root prefix (the sourcemap records absolute paths),
// then the peer project's directory. The caller prefixes the peer mount.
export function peerTexRelativePath(source: string, mapRoot: string, peerDir: string): string {
  let rel = source;
  if (mapRoot && rel.startsWith(mapRoot + "/")) rel = rel.slice(mapRoot.length + 1);
  const dir = peerDir.replace(/\/$/, "");
  if (dir && rel.startsWith(dir + "/")) rel = rel.slice(dir.length + 1);
  return rel.replace(/^\/+/, "");
}
