module

public import PolishSpaceBook.SetTheoryRecursiveClosure

@[expose] public section

/-! # Check-name closure from actual ground-model axiom instances -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames
universe u

def productEqFormula {n : ℕ} (x y z : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) z.castSucc).iff
    (productFormula x.castSucc y.castSucc (Fin.last n))).all

lemma realize_productFormula_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y q : Fin n) (xs : Fin n → M) :
    (productFormula x y q).Realize Empty.elim xs ↔ (xs q).val ∈ ZFSet.prod (xs x).val (xs y).val :=
  realize_productFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) x y q xs

lemma realize_productEqFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (hpair : M ⊨ pairingSentence)
    {n : ℕ} (x y z : Fin n) (xs : Fin n → M) :
    (productEqFormula x y z).Realize Empty.elim xs ↔ (xs z).val = ZFSet.prod (xs x).val (xs y).val := by
  simp only [productEqFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    realize_memberAt_model, realize_productFormula_model hM, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro q
    constructor
    · intro hq; exact (h ⟨q, hM.mem_trans hq (xs z).property⟩).mp hq
    · intro hq
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hq
      have hqM := orderedPair_mem hM hpair (hM.mem_trans ha (xs x).property) (hM.mem_trans hb (xs y).property)
      exact (h ⟨_, hqM⟩).mpr hq
  · intro he q; rw [he]

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    With parameter $P$, use the step rule
    $$C_P(a,g):=\GraphRange{g}\times P.$$
-/
def checkStep (P _a g : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod (graphRange g) P

/-- Parameters P, input a, preceding graph g, and output b. -/

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    An internal defining formula is
    $$\psi_P(a,g,b)\;:\equiv\;\exists r\,(r=\GraphRange{g}\land b=r\times P).$$
    Use the range equality already displayed and expand the product equality as
    $$\forall q\,\bigl(q\in b\leftrightarrow
     \exists v\in r\,\exists p\in P\,(q=\langle v,p\rangle)\bigr).$$
-/
def checkStepFormula : ForcingFormulas.Formula 4 :=
  (rangeFormula (2 : Fin 5) 4 ⊓ productEqFormula 4 0 3).ex

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    All actual pairs from the two factors belong to the model by Pairing, so this internal formula recognizes
    the actual product, not merely its intersection with the model.
-/
lemma realize_checkStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1)) (P a g b : M) :
    checkStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ![P] a) g) b) ↔
      b.val = checkStep P.val a.val g.val := by
  simp only [checkStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rangeFormula hM hunion, realize_productEqFormula hM hpair, Fin.snoc]
  constructor
  · rintro ⟨r, hr, hb⟩; exact hb.trans (by rw [hr]; rfl)
  · intro hb
    exact ⟨⟨graphRange g.val, graphRange_mem hM hunion hsep g.property⟩, rfl, hb⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The range and product constructions above put its value in the model whenever its arguments belong to the
    model.
-/
lemma checkStep_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P a g : M) : checkStep P.val a.val g.val ∈ M :=
  prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (graphRange_mem hM hunion (hsep _) g.property) P.property


/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For the external check-name function, the range of its graph on $a$ is
    $\{\check{y}:y\in a\}$. Its product with the condition set is precisely the defining set of pairs for
    $\check{a}$. Thus the check-name function satisfies this step equation.
-/
lemma check_step_equation (P a : ZFSet.{u}) :
    check P a = checkStep P a (functionGraph (fun y : a => check P y.val)) := by
  apply ZFSet.ext
  intro q
  rw [mem_check, checkStep, graphRange_functionGraph, ZFSet.mem_prod]
  constructor
  · rintro ⟨y, hy, p, hp, he⟩
    exact ⟨check P y, ZFSet.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩, p, hp, he⟩
  · rintro ⟨v, hv, p, hp, he⟩
    obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hv
    exact ⟨y.val, y.property, p, hp, he⟩

/-- Check names belong to the model by internal recursion, with no check-closure hypothesis. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Internal membership recursion and the comparison lemma now give $\check{a}\in M$.
    No Choice axiom or generic filter is needed for this closure statement.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Check names in the ground model
-/
theorem check_mem_of_axioms {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P a : M) : check P.val a.val ∈ M :=
  external_recursive_value_mem hM hinf hpair hunion hpower hsep hrep checkStepFormula ![P]
    (checkStep P.val) (fun a g b => realize_checkStepFormula hM hpair hunion (hsep _) P a g b)
    (fun a g => checkStep_mem hM hpair hunion hpower hsep P a g)
    (check P.val) (check_step_equation P.val) a

/-- The ground model is contained in the extension once its elementary axiom schemes are available. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For a transitive ground model satisfying the axioms in the check-name lemma, the closure hypothesis is
    now established. Hence $M\IncludedIn M[G]$ whenever $P\in M$ and $\varnothing\ne G\IncludedIn P$.
    This inclusion uses the concrete internal step rule and the comparison with external check names;
    transitivity alone would not supply it.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Forcing extensions $M[G]$ are transitive and contain $M$, so these tests explain which low-complexity assertions are
    preserved by forcing and which can change.
-/
theorem ground_subset_extension_of_axioms {M P : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hP : P ∈ M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) : M ⊆ extension P M G :=
  ground_subset_extension P M G hG
    (fun a ha => check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨P, hP⟩ ⟨a, ha⟩)

end PolishSpaceBook.SetTheoryModels
