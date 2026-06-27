// Pure parsing/validation of the SSE frame payloads (watch + build channels) and
// the build-select request body. Extracted from file-watch.ts / build-status.ts
// so this logic is dependency-free and unit testable: those modules import the
// event stream, whose own `./event-stream.js` specifier `node --test` cannot
// resolve to the .ts source, so they cannot be loaded directly under the runner.

export interface BuildStatus {
  dir: string;
  state: "building" | "done" | "failed";
}

// A "watch" frame is `{ path }` with a repository-relative path. Returns the
// path, or null for a malformed frame or a missing/blank/non-string path.
export function parseWatchPath(data: string): string | null {
  try {
    const { path } = JSON.parse(data);
    return typeof path === "string" && path ? path : null;
  } catch {
    return null;
  }
}

// A "build" frame is `{ dir, state }`. Returns the validated status object (extra
// fields preserved), or null for a malformed frame or a missing/wrong-typed field.
export function parseBuildStatus(data: string): BuildStatus | null {
  try {
    const status = JSON.parse(data);
    if (status && typeof status.dir === "string" && typeof status.state === "string") {
      return status as BuildStatus;
    }
    return null;
  } catch {
    return null;
  }
}

// The POST /build/select request that tells the server which rendered PDF a tab
// is showing. Returns null for a blank path (nothing to report).
export function selectPdfRequest(sessionQuery: string, repoRelPath: string): { url: string; body: string } | null {
  if (!repoRelPath) return null;
  return { url: "/build/select" + sessionQuery, body: JSON.stringify({ pdf: repoRelPath }) };
}
