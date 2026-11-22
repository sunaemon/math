module

public import PolishSpaceBook.SetTheoryRecursiveClosure

@[expose] public section

/-! # Internal rank recursion using the union of predecessor ranks and their union -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def binaryUnionFormula {n : ℕ} (x y z : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) z.castSucc).iff
    (memberAt (Fin.last n) x.castSucc ⊔ memberAt (Fin.last n) y.castSucc)).all

lemma realize_binaryUnionFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y z : Fin n) (xs : Fin n → M) :
    (binaryUnionFormula x y z).Realize Empty.elim xs ↔ (xs z).val = (xs x).val ∪ (xs y).val := by
  simp only [binaryUnionFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_sup, realize_memberAt_model, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_union]
    constructor
    · intro hq; exact (h ⟨q, hM.mem_trans hq (xs z).property⟩).mp hq
    · rintro (hq | hq)
      · exact (h ⟨q, hM.mem_trans hq (xs x).property⟩).mpr (Or.inl hq)
      · exact (h ⟨q, hM.mem_trans hq (xs y).property⟩).mpr (Or.inr hq)
  · intro he q; rw [he, ZFSet.mem_union]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Put $\rho(a):=\mathrm{rank}(a)$ and use the step rule
    $$H(a,g):=R\cup\bigcup R,\qquad R:=\GraphRange{g}.$$
-/
def rankStep (_a g : ZFSet.{u}) : ZFSet.{u} := graphRange g ∪ ZFSet.sUnion (graphRange g)

/-- Input a, preceding graph g, output b; there are no parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    An internal defining formula is
    $$\begin{aligned}
    \psi(a,g,b)\;:\equiv\;\exists r\,\exists u\,\bigl(
     r=\GraphRange{g}\\
    {}\land u=\bigcup r\land b=r\cup u\bigr).
    \end{aligned}$$
-/
def rankStepFormula : ForcingFormulas.Formula 3 :=
  (rangeFormula (1 : Fin 5) 3 ⊓ unionFormula 3 4 ⊓ binaryUnionFormula 3 4 2).ex.ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Expand the last equality as $\forall z\,(z\in b\leftrightarrow z\in r\lor z\in u)$.
    The range and union predicates have already been verified, and transitivity identifies the internal
    binary-union clause with the actual union. This defines the step even when the proposed preceding values
    are not ordinals.
-/
lemma realize_rankStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1)) (a g b : M) :
    rankStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b) ↔
      b.val = rankStep a.val g.val := by
  simp only [rankStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rangeFormula hM hunion, realize_unionFormula hM, realize_binaryUnionFormula hM, Fin.snoc]
  constructor
  · rintro ⟨r, v, ⟨hr, hv⟩, hb⟩
    exact hb.trans (by rw [hv, hr]; rfl)
  · intro hb
    let r : M := ⟨graphRange g.val, graphRange_mem hM hunion hsep g.property⟩
    let v : M := ⟨ZFSet.sUnion r.val, union_mem hM hunion r.property⟩
    exact ⟨r, v, ⟨rfl, rfl⟩, hb⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Range closure, Union, and binary-union closure put this value in the model.
-/
lemma rankStep_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1)) (a g : M) :
    rankStep a.val g.val ∈ M := by
  have hr := graphRange_mem hM hunion hsep g.property
  exact binaryUnion_mem hM hpair hunion hr (union_mem hM hunion hr)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For the actual rank function, $R=\{\rho(y):y\in a\}$ consists of ordinals.
    Every member of $R\cup\bigcup R$ is an ordinal, and for an ordinal $\beta$,
    $$\begin{aligned}
    \beta\in R\cup\bigcup R
    &\Longleftrightarrow\exists y\in a\,(\beta\le\rho(y))\\
    &\Longleftrightarrow\beta<\rho(a).
    \end{aligned}$$
    The last equivalence is the defining supremum property of rank.
    Extensionality gives $\rho(a)=R\cup\bigcup R$, which is the required step equation.
-/
lemma rank_step_equation (a : ZFSet.{u}) :
    a.rank.toZFSet = rankStep a (functionGraph (fun y : a => y.val.rank.toZFSet)) := by
  apply ZFSet.ext
  intro z
  rw [rankStep, graphRange_functionGraph (fun y => y.rank.toZFSet), ZFSet.mem_union]
  constructor
  · intro hz
    obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    obtain ⟨y, hy, hβy⟩ := ZFSet.lt_rank_iff.mp hβ
    rcases lt_or_eq_of_le hβy with hlt | rfl
    · right
      exact ZFSet.mem_sUnion.mpr ⟨y.rank.toZFSet, ZFSet.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt⟩
    · exact Or.inl (ZFSet.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩)
  · rintro (hz | hz)
    · obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hz
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (ZFSet.rank_lt_of_mem y.property)
    · obtain ⟨v, hv, hzv⟩ := ZFSet.mem_sUnion.mp hz
      obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hv
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hzv
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hβ.trans (ZFSet.rank_lt_of_mem y.property))

/-- Actual rank ordinals belong to the model by the internally defined rank step. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Rank ordinals in the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The internal recursion and comparison lemmas therefore give $\rho(a)\in M$.
-/
theorem rank_mem_of_axioms {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (a : M) : a.val.rank.toZFSet ∈ M :=
  external_recursive_value_mem hM hinf hpair hunion hpower hsep hrep rankStepFormula Fin.elim0
    rankStep (fun a g b => realize_rankStepFormula hM hunion (hsep _) a g b)
    (fun a g => rankStep_mem hM hpair hunion (hsep _) a g)
    (fun a => a.rank.toZFSet) rank_step_equation a

end PolishSpaceBook.SetTheoryModels
