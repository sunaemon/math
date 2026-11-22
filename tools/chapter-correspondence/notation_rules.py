"""Shared notation interpretations, independent of a chapter's source location.

Profiles select named conventions; they never change parser coverage or grant
review. Structural operators and Lean adapter helpers remain in the shared
engine. Add a rule here once, with independent operand/instance regressions.
"""

EXPECTED_HEADS = {
    "sum:finite": "Finset.sum",
    "sum:infinite": "tsum",
    "sum:tail": "tsum",
    "binder:predicate-set": "Set.ofPred",
    "set:generated-union": "Set.sUnion",
    "power:real-integer": "HPow.hPow",
    "unary:-": "Neg.neg",
    "infix:implicit-multiply": "HMul.hMul",
    "operation:restrict": "Set.domRestrict",
    "set:product": "Set.prod",
    "set:empty": "EmptyCollection.emptyCollection",
    "relation:metric-le": "LE.le",
    "definition:=": "Eq",
    "operation:infimum": "InfSet.sInf",
    "binder:image-set": "Set.image",
    "relation:sequence-limit": "Filter.Tendsto",
    "set:IncludedIn": "LE.le",
    "set:=": "Eq",
    "set:≠": "Ne",
    "set:in": "Membership.mem",
    "set:cap": "Inter.inter",
    "set:cup": "Union.union",
    "macro:SetDifference": "SDiff.sdiff",
    "infix:+": "HAdd.hAdd",
    "infix:-": "HSub.hSub",
    "infix:*": "HMul.hMul",
    "infix:/": "HDiv.hDiv",
    "infix:≤": "LE.le",
    "infix:≥": "GE.ge",
    "infix:<": "LT.lt",
    "infix:>": "GT.gt",
    "infix:=": "Eq",
    "infix:≠": "Ne",
    "application:metric": "Dist.dist",
    "application:distance-to-set": "Metric.infDist",
    "macro:frac": "HDiv.hDiv",
    "macro:Abs": "abs",
    "macro:Closure": "closure",
    "macro:AmbientClosure": "closure",
    "macro:Ball": "Metric.ball",
    "macro:MetricBall": "Metric.ball",
    "macro:MetricDiameter": "Metric.diam",
    "macro:ClosedInterval": "Set.Icc",
    "macro:OpenInterval": "Set.Ioo",
    "macro:LeftClosedInterval": "Set.Ico",
}

from native import NativeMacros

MACROS = NativeMacros()

CORE_DECLARATIONS = {
    "tsum",
    "Summable",
    "InfSet.sInf",
    "Metric.infDist",
    "nhds",
    "Filter.Tendsto",
    "HPow.hPow",
    "Finset.range",
    "Neg.neg",
    "Set.prod",
    "Function.uncurry",
    "SeqContinuous",
    "Finset.sum",
    "Metric.infDist_eq_iInf",
    "Set.domRestrict",
    "Filter.atTop",
    "sInf_image'",
    "Set.image",
    "Set.ofPred",
    "IsGδ",
    "Int.ofNat",
}

PROFILES = {
    "core": {
        "constants": {"R": "ℝ", "QQ": "ℚ", "Gdelta": "(@IsGδ)", "omega": "ℕ", "TwoPointSpace": "Bool"},
        "declarations": [],
        "conventions": {},
    },
    "polish-spaces": {
        "constants": {
            "Fsigma": "(@PolishSpaceBook.IsFsigma)",
            "BaireSpace": "baire_space",
            "CantorSpace": "cantor_space",
            "HilbertCube": "hilbert_cube",
            "RealSequenceSpace": "real_sequence_space",
        },
        "declarations": ["PolishSpaceBook.IsFsigma"],
        "conventions": {"realSequenceEmbedding": "PolishSpaceBook.bounded_binary_sequence"},
    },
}


def select_profiles(names):
    constants, conventions = {}, {}
    declarations = set(CORE_DECLARATIONS)
    if len(set(names)) != len(names):
        raise ValueError("Duplicate notation profiles")
    for name in names:
        if name not in PROFILES:
            raise ValueError(f"Unknown notation profile: {name}")
        profile = PROFILES[name]
        for destination, field in ((constants, "constants"), (conventions, "conventions")):
            for key, value in profile[field].items():
                if key in destination:
                    raise ValueError(f"Conflicting notation convention: {key}")
                destination[key] = value
        declarations.update(profile["declarations"])
    return constants, declarations, conventions
