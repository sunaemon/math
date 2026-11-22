"""An explicitly frozen Python oracle, accessible only to migration tests."""

import re
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

SOURCE = Path(__file__).with_name("fixtures") / "correspondence-legacy-translate.txt"


@contextmanager
def legacy_oracle(chapter):
    namespace = {
        **vars(chapter),
        "MACROS": dict(chapter.MACROS),
        "VARIABLE_COMMANDS": {"phi", "epsilon", "varepsilon", "rho", "delta", "iota"},
        "re": re,
    }
    # Execute only the checked-in, trusted test fixture; never caller-supplied code.
    exec(compile(SOURCE.read_text(), str(SOURCE), "exec"), namespace)  # noqa: S102
    with patch.object(chapter, "translate", namespace["translate"]):
        yield


@contextmanager
def corrupt_native_terms(chapter, change):
    """Alter candidate code while keeping independent source expectations intact."""
    original = chapter.semantic_translation

    def corrupt(*args, **kwargs):
        result = original(*args, **kwargs)
        if result["supported"]:
            rendering = result["rendering"]
            for field in ("ordinary", "instrumented"):
                rendering[field] = change(rendering[field])
            for mapping in rendering["mappings"]:
                mapping["candidate"] = change(mapping["candidate"])
        return result

    with patch.object(chapter, "semantic_translation", side_effect=corrupt):
        yield
