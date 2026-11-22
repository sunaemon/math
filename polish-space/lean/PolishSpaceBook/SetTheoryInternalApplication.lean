module

public import PolishSpaceBook.SetTheoryBasicAbbreviations
public import PolishSpaceBook.SetTheoryRelationFormulas

@[expose] public section

/-! # Bounded application abbreviations in arbitrary membership structures -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {S : Type u} [membershipLanguage.Structure S]

lemma realize_internalBoundedAll {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → S) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : S, member y (xs i) → φ.Realize Empty.elim (Fin.snoc xs y) := by
  simp only [boundedAll, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt, Fin.snoc_last, Fin.snoc_castSucc]

lemma realize_internalBoundedExists {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → S) :
    (boundedExists i φ).Realize Empty.elim xs ↔
      ∃ y : S, member y (xs i) ∧ φ.Realize Empty.elim (Fin.snoc xs y) := by
  classical
  simp only [boundedExists, BoundedFormula.realize_not, realize_internalBoundedAll,
    not_forall, not_not, exists_prop]

lemma realize_internalSingleton {n : ℕ} (s a : Fin n) (xs : Fin n → S) :
    (singletonFormula s a).Realize Empty.elim xs ↔ IsUnorderedPair (xs s) (xs a) (xs a) := by
  simp only [singletonFormula, BoundedFormula.realize_inf, realize_memberAt,
    realize_internalBoundedAll, realize_equalAt, Fin.snoc_last, Fin.snoc_castSucc,
    IsUnorderedPair, or_self]
  constructor
  · rintro ⟨ha, h⟩ z
    exact ⟨h z, fun hz => hz ▸ ha⟩
  · intro h
    exact ⟨(h _).mpr rfl, fun z hz => (h z).mp hz⟩

lemma realize_internalUnorderedPair {n : ℕ} (p a b : Fin n) (xs : Fin n → S) :
    (unorderedPairFormula p a b).Realize Empty.elim xs ↔ IsUnorderedPair (xs p) (xs a) (xs b) := by
  simp only [unorderedPairFormula, BoundedFormula.realize_inf, realize_memberAt,
    realize_internalBoundedAll, BoundedFormula.realize_sup, realize_equalAt,
    Fin.snoc_last, Fin.snoc_castSucc, IsUnorderedPair]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩ z
    exact ⟨h z, fun hz => hz.elim (fun e => e ▸ ha) (fun e => e ▸ hb)⟩
  · intro h
    exact ⟨⟨(h _).mpr (Or.inl rfl), (h _).mpr (Or.inr rfl)⟩,
      fun z hz => (h z).mp hz⟩

lemma realize_internalOrderedPair {n : ℕ} (q a b : Fin n) (xs : Fin n → S) :
    (orderedPairFormula q a b).Realize Empty.elim xs ↔ IsKuratowskiPair (xs q) (xs a) (xs b) := by
  simp only [orderedPairFormula, realize_internalBoundedExists, BoundedFormula.realize_inf,
    realize_internalSingleton, realize_internalUnorderedPair, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨s, _, p, _, ⟨hs, hp⟩, hq⟩
    exact ⟨s, p, hs, hp, hq⟩
  · rintro ⟨s, p, hs, hp, hq⟩
    exact ⟨s, (hq s).mpr (Or.inl rfl), p, (hq p).mpr (Or.inr rfl), ⟨hs, hp⟩, hq⟩

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Second, application is not treated as a total function symbol. The expression $f(a)=c$ abbreviates the atomic graph
    relation
    $$
    f(a)=c \;:\equiv\; \langle a,c\rangle \in f,
    $$
    and therefore unfolds by the bounded ordered-pair clause above. This is the systematic reason that the map predicates
    below are genuinely $\Delta_0$.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$
    and
    $$
    \langle a,b\rangle \in f
    $$
-/
lemma realize_internalPairMember {n : ℕ} (f a b : Fin n) (xs : Fin n → S) :
    (pairMemberFormula f a b).Realize Empty.elim xs ↔ GraphApplication (xs f) (xs a) (xs b) := by
  simp only [pairMemberFormula, realize_internalBoundedExists, realize_internalOrderedPair,
    Fin.snoc_last, Fin.snoc_castSucc, GraphApplication]
  exact exists_congr (fun _ => and_comm)

/-- The contextual atom f(a) ∈ y, with the double union available as a bound. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
def internalValueMemberFormula {n : ℕ} (f a y v : Fin n) : ForcingFormulas.Formula n :=
  boundedExists v (pairMemberFormula f.castSucc a.castSucc (Fin.last n) ⊓
    memberAt (Fin.last n) y.castSucc)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
lemma internalValueMemberFormula_deltaZero {n : ℕ} (f a y v : Fin n) :
    IsDeltaZero (internalValueMemberFormula f a y v) :=
  .exists v ((pairMemberFormula_deltaZero _ _ _).and (memberAt_deltaZero _ _))

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
lemma realize_internalValueMemberFormula {n : ℕ} (f a y v : Fin n) (xs : Fin n → S)
    (u : S)
    (hu : ∀ z : S, member z u ↔ ∃ w : S, member z w ∧ member w (xs f))
    (hv : ∀ z : S, member z (xs v) ↔ ∃ w : S, member z w ∧ member w u) :
    (internalValueMemberFormula f a y v).Realize Empty.elim xs ↔
      ∃ b : S, GraphApplication (xs f) (xs a) b ∧ member b (xs y) := by
  simp only [internalValueMemberFormula, realize_internalBoundedExists,
    BoundedFormula.realize_inf, realize_internalPairMember, realize_memberAt,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact (graphApplication_member_bounded hu hv).symm

end PolishSpaceBook.SetTheoryModels.AbstractMembership
