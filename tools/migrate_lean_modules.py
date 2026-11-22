#!/usr/bin/env python3
"""Migrate the book's legacy Lean headers while retaining public APIs.

Inputs are the book's own Lean sources. Outputs add module/public import/expose
headers and rename the moved Denumerable import. Run Lean validation afterward;
This is an explicit legacy migration/recovery utility, never a build step;
this script does not claim that mathematical or metaprogram migrations succeed.
"""

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def atom_end(source: str, start: int) -> tuple[int, int]:
    while source[start].isspace():
        start += 1
    stack = []
    end = start
    while end < len(source):
        char = source[end]
        if not stack and (char.isspace() or char in "]},"):
            break
        if char in "([{":
            stack.append(char)
        elif char in ")]}":
            if not stack:
                break
            stack.pop()
        end += 1
    return start, end


def migrate_well_founded(source: str) -> str:
    # The old wrapper's only field was the WellFounded proof itself.
    for match in reversed(list(re.finditer(r"\bIsWellFounded\.wf\s*", source))):
        start, end = atom_end(source, match.end())
        argument = re.fullmatch(r"\(r\s*:=\s*(.*)\)", source[start:end], re.DOTALL)
        if not argument:
            raise ValueError("Review an unrecognized IsWellFounded.wf application")
        source = source[: match.start()] + f"(inferInstance : WellFounded {argument[1]})" + source[end:]
    for match in reversed(list(re.finditer(r"\bIsWellFounded\b(?!\.)", source))):
        _, first = atom_end(source, match.end())
        start, end = atom_end(source, first)
        source = source[: match.start()] + "WellFounded " + source[start:end] + source[end:]
    source = source.replace("IsWellFounded.rank", "WellFounded.rank")
    source = source.replace("IsWellFounded.mem_range_rank", "WellFounded.mem_range_rank")
    source = source.replace("IsWellFounded.induction r", "(inferInstance : WellFounded r).induction")
    source = re.sub(r"((?:letI|haveI|let|have)\s*:\s*WellFounded\b[^:]*:=\s*)⟨([^⟨⟩\n,]+)⟩", r"\1\2", source)
    return source


def migrate_zf_class(source: str) -> str:
    """Use the canonical ZFClass type and coercion for the old class API."""
    source = re.sub(r"\bClass\.\{([^}]+)\}", r"ZFClass.{\1}", source)
    source = re.sub(
        r"\((?:Class|ZFClass)\.ofSet ([A-Za-z_][A-Za-z_0-9']*)\)",
        r"(\1 : ZFClass)",
        source,
    )
    return source


def migrate(source: str) -> str:
    source = source.replace("Mathlib.Logic.Denumerable", "Mathlib.Basic.Denumerable")
    if re.search(r"^module\s*$", source, re.MULTILINE):
        return source
    imports = list(re.finditer(r"^import [^\n]+\n", source, re.MULTILINE))
    if not imports:
        return "module\n\n@[expose] public section\n\n" + source
    last = imports[-1].end()
    header = source[:last]
    if re.search(r"^(?:namespace|theorem|def|structure|inductive|example)\b", header, re.MULTILINE):
        raise ValueError("Import-like text occurs after declarations; review manually")
    header = re.sub(r"^import ", "public import ", header, flags=re.MULTILINE)
    return "module\n\n" + header + "\n@[expose] public section\n" + source[last:]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--well-founded", action="store_true")
    parser.add_argument("--zf-class", action="store_true")
    parser.add_argument(
        "--diagnostics",
        type=Path,
        help="Fresh Lean log matching current line numbers; never use a stale log after edits",
    )
    args = parser.parse_args()
    alias_lines = {}
    exports = {}
    instance_lines = {}
    redundant_rfl = {}
    if args.diagnostics:
        diagnostics = args.diagnostics.read_text(encoding="utf-8")
        excluded = {
            "IsWellFounded",
            "HasSmallInductiveDimensionLT_one_iff",
            "totallySeparatedSpace_of_t0_of_basis_clopen",
            "SimpleGraph.IsAcyclic.path_unique",
        }
        blocks = re.split(r"(?=^(?:warning|error): )", diagnostics, flags=re.MULTILINE)
        for block in blocks:
            deprecated = re.match(
                r"warning: (lean/[^:]+):(\d+):\d+: `([^`]+)` has been deprecated: Use `([^`]+)` instead", block
            )
            if deprecated and deprecated[3] not in excluded:
                alias_lines.setdefault(ROOT / "polish-space" / deprecated[1], []).append(
                    (int(deprecated[2]), deprecated[3], deprecated[4])
                )
            origin = re.match(r"(?:warning|error): (lean/[^:]+):", block)
            if origin:
                names = re.findall(r"A private declaration `([^`]+)`.*would need to be public", block)
                exports.setdefault(ROOT / "polish-space" / origin[1], set()).update(names)
            found = re.match(r"warning: (lean/[^:]+):(\d+):\d+: Try this:", block)
            if found and "The goal is a proposition" in block:
                instance_lines.setdefault(ROOT / "polish-space" / found[1], set()).add(int(found[2]))
            unused = re.match(r"warning: (lean/[^:]+):(\d+):\d+: Unused tactic linter: `rfl` does nothing", block)
            if unused:
                redundant_rfl.setdefault(ROOT / "polish-space" / unused[1], set()).add(int(unused[2]))
    changed = 0
    updates = []
    sources = list((ROOT / "polish-space/lean").rglob("*.lean"))
    sources.append(ROOT / "polish-space-ch1/lean/PolishSpaceBook.lean")
    for path in sorted(sources):
        original = path.read_text(encoding="utf-8")
        updated = migrate(original)
        for name in exports.get(path, set()):
            updated = re.sub(
                r"^private ((?:noncomputable )?(?:def|theorem|lemma)) " + re.escape(name) + r"\b",
                r"\1 " + name,
                updated,
                flags=re.MULTILINE,
            )
        if args.well_founded:
            updated = migrate_well_founded(updated)
        if args.zf_class:
            updated = migrate_zf_class(updated)
        lines = updated.splitlines(keepends=True)
        diagnostic_lines = [number for number, _, _ in alias_lines.get(path, [])]
        diagnostic_lines += list(instance_lines.get(path, set()) | redundant_rfl.get(path, set()))
        if any(number < 1 or number > len(lines) for number in diagnostic_lines):
            parser.error(f"stale diagnostics for {path}: line outside the current source; regenerate the log")
        for number, old, new in alias_lines.get(path, []):
            line = lines[number - 1]
            line = re.sub(r"(?<![\w.])" + re.escape(old) + r"(?!\w)", new, line)
            old_prefix, _, old_name = old.rpartition(".")
            new_prefix, _, new_name = new.rpartition(".")
            replacement = new_name if old_prefix == new_prefix else new
            lines[number - 1] = re.sub(r"\b" + re.escape(old_name) + r"\b", replacement, line)
        for number in instance_lines.get(path, set()):
            line = lines[number - 1]
            lines[number - 1] = re.sub(r"\b(letI|haveI)\b", lambda m: m[1][:-1], line, count=1)
        for number in redundant_rfl.get(path, set()):
            line = lines[number - 1]
            if re.fullmatch(r"\s*(?:try )?rfl\s*", line):
                lines[number - 1] = "\n"
            else:
                lines[number - 1] = re.sub(r"\s*(?:<;>|;)\s*try rfl(?=\s*$)", "", line)
        updated = "".join(lines)
        if original != updated:
            updates.append((path, updated))
    for path, updated in updates:
        path.write_text(updated, encoding="utf-8")
        changed += 1
    print(f"Updated {changed} Lean sources; run make validate-lean next.")


if __name__ == "__main__":
    main()
