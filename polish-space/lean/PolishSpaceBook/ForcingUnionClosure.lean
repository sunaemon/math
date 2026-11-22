module

public import PolishSpaceBook.ForcingUnionNames
public import PolishSpaceBook.SetTheoryProducts
public import PolishSpaceBook.SetTheoryRelationFormulas
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section


/-! # Internal construction of a union name and preservation of Union -/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open FirstOrder Language ZFSet ForcingAtomic SetTheoryModels
universe u

/-- Parameters are τ, P, R, A, D; the tested member is z. Bound variables are σ, q, π, p, r. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $\rho$ be the subset of $D\times P$ consisting of the pairs $\langle\sigma,q\rangle$ for which
    $$\begin{aligned}
    \exists\pi\in A\,\exists p\in P\,\exists r\in P\,\bigl(
    &\langle\pi,p\rangle\in\tau\land\langle\sigma,r\rangle\in\pi\\
    &{}\land\langle q,p\rangle\in R\land\langle q,r\rangle\in R\bigr).
    \end{aligned}$$
    Thus $q$ simultaneously strengthens the two labels $p,r$.
-/
def unionClosurePredicate : BoundedSetPredicate 6 :=
  .ex 4 (.ex 1 (.ex 3 (.ex 1 (.ex 1
    (.conj (.orderedPair 5 6 7) (.conj (.pairMember 0 8 9) (.conj (.pairMember 8 6 10)
      (.conj (.pairMember 2 7 9) (.pairMember 2 7 10)))))))))

def unionClosureFormula : ForcingFormulas.Formula 6 := unionClosurePredicate.compile

lemma unionClosureFormula_deltaZero : IsDeltaZero unionClosureFormula :=
  unionClosurePredicate.compile_deltaZero

lemma external_unionClosureFormula (τ P R A D z : ZFSet.{u}) :
    externalRealize unionClosureFormula (Fin.snoc ![τ, P, R, A, D] z) ↔ unionPredicate τ P R A D z := by
  simp only [unionClosureFormula, unionClosurePredicate, BoundedSetPredicate.compile,
    externalRealize_boundedExists, externalRealize_inf,
    externalRealize_orderedPair, externalRealize_pairMember]
  simp [unionPredicate, Fin.snoc, Fin.castPred, Fin.castLT]

/-- Products and one bounded Separation instance suffice to construct the union name. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Every quantifier is bounded by a set in $M$, and ordered-pair membership has the bounded expansion from
    §{sec:zfc-absoluteness}. The product construction and bounded Separation give $\rho\in M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Both sets belong to $M$ by repeated applications of its Union axiom.
-/
lemma unionOfName_mem_ground_of_separation {M P R τ : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hprod : M ⊨ separationSentence productSeparationFormula)
    (hsep : M ⊨ separationSentence unionClosureFormula)
    (hP : P ∈ M) (hR : R ∈ M) (hτ : τ ∈ M) : unionOfName P R τ ∈ M := by
  have hA : childBound τ ∈ M := union_mem hM hunion (union_mem hM hunion hτ)
  have hD : grandchildBound τ ∈ M := union_mem hM hunion (union_mem hM hunion (union_mem hM hunion hA))
  have hB := prod_mem_of_separation hM hpair hunion hpower hprod hD hP
  let ps : Fin 5 → M := ![⟨τ, hτ⟩, ⟨P, hP⟩, ⟨R, hR⟩, ⟨childBound τ, hA⟩, ⟨grandchildBound τ, hD⟩]
  have h := unionClosurePredicate.separation_mem hM hsep ps hB
  unfold unionOfName unionPredicate
  simpa [unionClosurePredicate, BoundedSetPredicate.eval,
    ps, Fin.snoc, Fin.castPred, Fin.castLT, Function.comp_def] using h

/-- Compatibility with callers that derive Separation from Replacement. -/
lemma unionOfName_mem_ground {M P R τ : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hprod : M ⊨ replacementSentence (singletonSelector productSeparationFormula))
    (hsep : M ⊨ replacementSentence (singletonSelector unionClosureFormula))
    (hP : P ∈ M) (hR : R ∈ M) (hτ : τ ∈ M) : unionOfName P R τ ∈ M :=
  unionOfName_mem_ground_of_separation hM hpair hunion hpower
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion _ hprod)
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion _ hsep)
    hP hR hτ

/-- The name in the ground model witnesses the actual union in the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Every set in $M[G]$ is some $\tau^G$, and the constructed name $\rho$ belongs to $M$.
    Hence $\bigcup\tau^G=\rho^G\in M[G]$. Transitivity ensures that every member used in the union's defining
    condition belongs to the extension, so this actual union witnesses the internal Union axiom.
    The argument uses only the ground-model axioms needed for iterated unions, products, and the indicated bounded
    Separation instances.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: proposition
  title: Union in the extension
-/
theorem extension_models_union_of_separation {M P R : ZFSet.{u}} [Preorder (Condition P)] (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hprod : M ⊨ separationSentence productSeparationFormula)
    (hsep : M ⊨ separationSentence unionClosureFormula)
    (hP : P ∈ M) (hRM : R ∈ M)
    (hR : ∀ p q : Condition P, ZFSet.pair p.val q.val ∈ R ↔ p ≤ q)
    (G : Order.PFilter (Condition P)) : extension P M (chosen P G) ⊨ unionSentence := by
  apply (models_union_iff (extension P M (chosen P G))).mpr
  intro x
  obtain ⟨τ, hτM, hτ, hτx⟩ := (mem_extension P M (chosen P G) x.val).mp x.property
  change value P G τ = x.val at hτx
  have hu : ZFSet.sUnion x.val ∈ extension P M (chosen P G) := by
    apply (mem_extension P M (chosen P G) _).mpr
    refine ⟨unionOfName P R τ,
      unionOfName_mem_ground_of_separation hM hpair hunion hpower hprod hsep hP hRM hτM,
      unionOfName_isName hτ, ?_⟩
    change value P G (unionOfName P R τ) = ZFSet.sUnion x.val
    rw [value_unionOfName P R τ hR G hτ, hτx]
  refine ⟨⟨ZFSet.sUnion x.val, hu⟩, ?_⟩
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨⟨y, (extension_isTransitive P M (chosen P G) hM).mem_trans hyx x.property⟩, hzy, hyx⟩
  · rintro ⟨y, hzy, hyx⟩
    exact ⟨y.val, hyx, hzy⟩

/-- The same result for callers whose ground-model assumptions provide Replacement. -/
theorem extension_models_union {M P R : ZFSet.{u}} [Preorder (Condition P)] (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hprod : M ⊨ replacementSentence (singletonSelector productSeparationFormula))
    (hsep : M ⊨ replacementSentence (singletonSelector unionClosureFormula))
    (hP : P ∈ M) (hRM : R ∈ M)
    (hR : ∀ p q : Condition P, ZFSet.pair p.val q.val ∈ R ↔ p ≤ q)
    (G : Order.PFilter (Condition P)) : extension P M (chosen P G) ⊨ unionSentence :=
  extension_models_union_of_separation hM hpair hunion hpower
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion _ hprod)
    (models_separation_of_replacement M (models_extensionality hM) hinf hpair hunion _ hsep)
    hP hRM hR G

end PolishSpaceBook.ForcingNames
