module

public import PolishSpaceBook.SetTheoryPairFormulas

@[expose] public section

/-! # Bounded membership in coded binary relations and ambient realization rules -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Membership of an ordered pair in a relation is a bounded formula. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    means that some $q\in f$ is the Kuratowski pair of $a$ and $b$, with all witnesses bounded by $q$. Written out, this
    says:
    $$
    \exists q\in f\,\bigl(q=\langle a,b\rangle\bigr),
    $$
    where $q=\langle a,b\rangle$ itself is expanded by quantifying only over $q$ and its elements. Thus atomic formulas
    involving ordered pairs introduce bounded quantifiers only.
-/
def pairMemberFormula {n : ℕ} (R a b : Fin n) : ForcingFormulas.Formula n :=
  boundedExists R (orderedPairFormula (Fin.last n) a.castSucc b.castSucc)

lemma pairMemberFormula_deltaZero {n : ℕ} (R a b : Fin n) : IsDeltaZero (pairMemberFormula R a b) :=
  .exists R (orderedPairFormula_deltaZero _ _ _)

lemma realize_pairMemberFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (R a b : Fin n) (xs : Fin n → ClassDomain C) :
    (pairMemberFormula R a b).Realize Empty.elim xs ↔
      ZFSet.pair (xs a).val (xs b).val ∈ (xs R).val := by
  simp only [pairMemberFormula, realize_boundedExists, realize_orderedPairFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨z, hz, he⟩
    exact he ▸ hz
  · intro h
    exact ⟨⟨_, hC _ (xs R).property _ h⟩, h, rfl⟩

lemma externalRealize_inf {n : ℕ} (φ ψ : ForcingFormulas.Formula n) (xs : Fin n → ZFSet.{u}) :
    externalRealize (φ ⊓ ψ) xs ↔ externalRealize φ xs ∧ externalRealize ψ xs := by
  simp only [externalRealize, BoundedFormula.realize_inf]

lemma externalRealize_boundedExists {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → ZFSet.{u}) :
    externalRealize (boundedExists i φ) xs ↔ ∃ z ∈ xs i, externalRealize φ (Fin.snoc xs z) := by
  simp only [externalRealize, realize_boundedExists]
  have he (z : ClassDomain (⊤ : ZFClass.{u})) :
      (fun i => (⟨Fin.snoc (α := fun _ => ZFSet.{u}) xs z.val i, trivial⟩ : ClassDomain (⊤ : ZFClass.{u}))) =
        Fin.snoc (fun i => ⟨xs i, trivial⟩) z :=
    apply_snoc (fun a : ZFSet.{u} => (⟨a, trivial⟩ : ClassDomain (⊤ : ZFClass.{u}))) xs z.val
  constructor
  · rintro ⟨z, hz, hφ⟩
    refine ⟨z.val, hz, ?_⟩
    rw [he z]
    exact hφ
  · rintro ⟨z, hz, hφ⟩
    refine ⟨⟨z, trivial⟩, hz, ?_⟩
    rw [he ⟨z, trivial⟩] at hφ
    exact hφ

lemma externalRealize_orderedPair {n : ℕ} (q a b : Fin n) (xs : Fin n → ZFSet.{u}) :
    externalRealize (orderedPairFormula q a b) xs ↔ xs q = ZFSet.pair (xs a) (xs b) :=
  realize_orderedPairFormula (⊤ : ZFClass.{u}) (fun _ _ _ _ => trivial) q a b _

lemma externalRealize_pairMember {n : ℕ} (R a b : Fin n) (xs : Fin n → ZFSet.{u}) :
    externalRealize (pairMemberFormula R a b) xs ↔ ZFSet.pair (xs a) (xs b) ∈ xs R :=
  realize_pairMemberFormula (⊤ : ZFClass.{u}) (fun _ _ _ _ => trivial) R a b _

end PolishSpaceBook.SetTheoryModels
