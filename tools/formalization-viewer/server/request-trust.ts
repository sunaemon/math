// Request provenance checks for the formalization viewer's bridge.
//
// The server binds 127.0.0.1 only, but a malicious web page can still aim a
// cross-origin request at it (and DNS-rebinding can make a hostile name resolve
// to loopback). So every request is accepted only when its Host is a loopback
// name and its Origin (when present) matches that Host exactly. This mirrors the
// SimpleHTTPRequestHandler-based Python server's is_trusted_request.

import { isIP } from "node:net";

function splitHostPort(value: string | undefined): [string | null, string | null] {
  const host = (value ?? "").trim();
  if (!host) return [null, null];
  if (host.startsWith("[")) {
    const end = host.indexOf("]");
    if (end < 0) return [null, null];
    const rest = host.slice(end + 1);
    let port: string | null = null;
    if (rest.startsWith(":")) {
      port = rest.slice(1);
      if (!/^\d+$/.test(port)) return [null, null];
    } else if (rest) {
      return [null, null];
    }
    return [host.slice(1, end).toLowerCase(), port];
  }
  const colons = (host.match(/:/g) ?? []).length;
  if (colons === 1) {
    const idx = host.lastIndexOf(":");
    const name = host.slice(0, idx);
    const port = host.slice(idx + 1);
    if (!/^\d+$/.test(port)) return [null, null];
    return [name.replace(/\.+$/, "").toLowerCase(), port];
  }
  if (host.includes(":")) {
    // Raw IPv6 literals are not valid HTTP Host syntax with a port, but
    // accepting loopback-only raw literals keeps the helper conservative.
    return [host.toLowerCase(), null];
  }
  return [host.replace(/\.+$/, "").toLowerCase(), null];
}

function hostWithoutPort(value: string | undefined): string | null {
  return splitHostPort(value)[0];
}

function isLoopbackAddress(host: string): boolean {
  const kind = isIP(host);
  if (kind === 4) return host.split(".")[0] === "127";
  if (kind === 6) {
    const normalized = host.toLowerCase();
    return normalized === "::1" || normalized === "0:0:0:0:0:0:0:1";
  }
  return false;
}

// A bare hostname (no port) is loopback when it is "localhost" or a loopback IP.
function isLoopbackName(name: string): boolean {
  return name === "localhost" || isLoopbackAddress(name);
}

function isLoopbackHost(value: string | undefined): boolean {
  const host = hostWithoutPort(value);
  return host !== null && isLoopbackName(host);
}

function originMatchesHost(origin: string, host: string): boolean {
  if (!origin) return true;
  let parsed: URL;
  try {
    parsed = new URL(origin);
  } catch {
    return false;
  }
  const scheme = parsed.protocol.replace(/:$/, "");
  if ((scheme !== "http" && scheme !== "https") || !parsed.hostname) return false;
  const originHost = parsed.hostname.replace(/\.+$/, "").toLowerCase();
  const [hostName, hostPort] = splitHostPort(host);
  if (hostName === null || !isLoopbackName(originHost)) return false;
  // URL.port is "" when absent or default; Python's urlparse(...).port is None.
  const originPort = parsed.port === "" ? null : parsed.port;
  return (
    originHost === hostName &&
    ((originPort === null && hostPort === null) || (originPort !== null && originPort === hostPort))
  );
}

export function isTrustedRequest(host: string | undefined, origin: string | undefined): boolean {
  return isLoopbackHost(host) && originMatchesHost(origin ?? "", host ?? "");
}
