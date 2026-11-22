"""Shared Lean marker grammar for tests; passages/declarations stay case-specific."""


def lean_booklink(target: str, *, excerpt: str | None = None, source: str = "chap.md", title: str | None = None) -> str:
    body = f"/-@ booklink:\n  source: {source}\n  target: {target}\n"
    if title is not None:
        body += f"  title: {title}\n"
    if excerpt is not None:
        body += "  excerpt: |\n" + "".join(f"    {line}\n" for line in excerpt.splitlines())
    return body + "-/"
