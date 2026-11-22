"""Parse the book's explicit formalization-scope comments in one place.

A region has both its content bounds (for semantic coverage) and its enclosing
comment bounds (for stable TeX injection keys and viewer navigation). These are
intentional views of the same parsed region, not different annotation grammars.
"""

import re
from dataclasses import dataclass

DIRECTIVES = frozenset({"skip", "skip-begin", "skip-end", "require", "structural"})
_ANNOTATION = re.compile(r"<!--\s*formalization:\s*([A-Za-z-]+)\b\s*(.*?)-->", re.DOTALL)


@dataclass(frozen=True)
class FormalizationAnnotation:
    start_offset: int
    end_offset: int
    directive: str
    reason: str | None


@dataclass(frozen=True)
class SkipRegion:
    opening: FormalizationAnnotation
    closing: FormalizationAnnotation

    @property
    def reason(self) -> str | None:
        return self.opening.reason or self.closing.reason


@dataclass(frozen=True)
class FormalizationScope:
    annotations: tuple[FormalizationAnnotation, ...]
    regions: tuple[SkipRegion, ...]

    @property
    def has_skips(self) -> bool:
        return any(annotation.directive.startswith("skip") for annotation in self.annotations)


def parse_formalization_scope(text: str, source: str) -> FormalizationScope:
    annotations = []
    regions = []
    stack = []
    for match in _ANNOTATION.finditer(text):
        directive = match[1].lower()
        if directive not in DIRECTIVES:
            raise ValueError(
                f"{source}: unknown formalization directive '{directive}' "
                f"(expected one of {', '.join(sorted(DIRECTIVES))})"
            )
        reason = match[2].strip()
        if reason.startswith("(") and reason.endswith(")"):
            reason = reason[1:-1].strip()
        reason = re.sub(r"\s+", " ", reason) or None
        annotation = FormalizationAnnotation(match.start(), match.end(), directive, reason)
        annotations.append(annotation)
        if directive == "skip-begin":
            stack.append(annotation)
        elif directive == "skip-end":
            if not stack:
                raise ValueError(f"{source}: 'formalization: skip-end' without a matching skip-begin")
            regions.append(SkipRegion(stack.pop(), annotation))
    if stack:
        raise ValueError(f"{source}: unclosed 'formalization: skip-begin' region")
    return FormalizationScope(tuple(annotations), tuple(regions))
