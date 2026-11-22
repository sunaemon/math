#!/usr/bin/env python3
"""Refresh public OpenAI signing keys bundled for browser-only ID-token checks.

The published JWKS endpoint has no browser CORS headers. This downloads public
keys only; it never reads credentials. Run this when signing keys rotate, then
run make viewer-build and rebuild the static distribution.
"""

import json
from pathlib import Path
from urllib.request import urlopen

url = "https://auth.openai.com/.well-known/jwks.json"
with urlopen(url, timeout=30) as response:
    document = json.load(response)
keys = [
    {field: key[field] for field in ("kty", "kid", "use", "alg", "n", "e")}
    for key in document["keys"]
    if key.get("kty") == "RSA" and key.get("use") == "sig" and key.get("alg") == "RS256"
]
if not keys or any("d" in key or "p" in key for key in keys):
    raise SystemExit("Expected public RS256 signing keys")
target = Path(__file__).parent / "formalization-viewer/src/chat-jwks.ts"
target.write_text(
    "// Public verification keys from "
    + url
    + "\n// Refresh with python3 tools/update_viewer_chat_jwks.py.\nexport const OPENAI_JWKS = "
    + json.dumps(keys, indent=2)
    + ";\n"
)
print(f"Updated {target} with {len(keys)} public signing keys")
