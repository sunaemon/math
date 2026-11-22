"""Explicit chapter selection; unregistered chapters are never silently checked."""

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = Path(__file__).with_name("chapters")


@dataclass(frozen=True)
class Chapter:
    name: str
    source: Path
    project: str
    modules: tuple[str, ...]
    namespaces: tuple[str, ...]
    profiles: tuple[str, ...]
    review: Path
    fingerprint: str

    def imports(self):
        return "".join(f"import {module}\n" for module in (*self.modules, "Lean"))

    def opens(self):
        return "open " + " ".join(self.namespaces) + "\n" if self.namespaces else ""


def load_chapter(name="polish-spaces"):
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name):
        raise ValueError("Invalid chapter identifier")
    path = REGISTRY / (name + ".json")
    if not path.is_file():
        raise ValueError(f"Unregistered chapter: {name}; add and review its configuration before migration")
    data = json.loads(path.read_text())
    if data["schemaVersion"] != 1 or data["chapter"] != name:
        raise ValueError("Invalid chapter configuration version or identity")
    for field in ("source", "leanProject", "review"):
        candidate = ROOT / data[field]
        if Path(data[field]).is_absolute() or not candidate.resolve().is_relative_to(ROOT):
            raise ValueError(f"Chapter {field} must be inside the repository")
        if not candidate.exists():
            raise ValueError(f"Missing chapter {field}: {candidate}")
    for field in ("leanModules", "openNamespaces"):
        if not isinstance(data[field], list) or any(
            not isinstance(value, str)
            or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", value)
            for value in data[field]
        ):
            raise ValueError(f"Invalid Lean names in {field}")
    if not data["leanModules"]:
        raise ValueError("Chapter must select at least one Lean module")
    # The current daemon serves the book's one shared Lake project. Reject an
    # unsupported project instead of inspecting declarations in the wrong one.
    if data["leanProject"] != "polish-space":
        raise ValueError("The Lean export transport currently serves the polish-space project only")
    from notation_rules import select_profiles

    profiles = data.get("notationProfiles", ["core"])
    if not isinstance(profiles, list) or not all(isinstance(name, str) for name in profiles):
        raise ValueError("notationProfiles must be a list of shared profile names")
    select_profiles(profiles)
    return Chapter(
        name,
        ROOT / data["source"],
        data["leanProject"],
        tuple(data["leanModules"]),
        tuple(data["openNamespaces"]),
        tuple(profiles),
        ROOT / data["review"],
        hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest(),
    )
