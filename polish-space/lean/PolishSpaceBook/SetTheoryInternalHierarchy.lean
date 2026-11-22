module

public import PolishSpaceBook.SetTheoryPowerImage
public import PolishSpaceBook.ForcingNames
public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

/-! # Internal cumulative stages and their exact external rank bounds -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma powerImage_range {ι : Type*} [Small.{u} ι] (M : ZFSet.{u}) (f : ι → ZFSet.{u}) :
    powerImage M (ZFSet.range f) = ZFSet.range (fun i => internalPowerSet M (f i)) := by
  apply ZFSet.ext
  intro p
  rw [powerImage, ZFSet.mem_range, ZFSet.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨i, hi⟩ := ZFSet.mem_range.mp r.property
    exact ⟨i, by rw [hi]; exact hr⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨f i, ZFSet.mem_range.mpr ⟨i, rfl⟩⟩, hi⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    In the ambient universe, membership recursion with parameter $M$ defines
    $$K_M(a):=\bigcup_{z\in a}\InternalPowerSet{M}{K_M(z)}.$$
-/
def internalHierarchy (M a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun b : a => internalPowerSet M (internalHierarchy M b.val)))
termination_by a.rank
 decreasing_by exact ZFSet.rank_lt_of_mem b.property

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Use the step rule
    $$H_M(a,g):=\bigcup\{\InternalPowerSet{M}{r}:r\in\GraphRange{g}\}.$$
-/
def hierarchyStep (M _a g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (powerImage M (graphRange g))

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    An internal defining formula is
    $$\begin{aligned}
    \psi(a,g,b)\;:\equiv\;\exists R\,\exists S\,\bigl(
     R=\GraphRange{g}\\
    {}\land\chi(R,S)\land b=\bigcup S\bigr).
    \end{aligned}$$
-/
def hierarchyStepFormula : ForcingFormulas.Formula 3 :=
  (rangeFormula (1 : Fin 5) 3 ⊓ powerImageFormula 3 4 ⊓ unionFormula 4 2).ex.ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    This is precisely the equation $K_M(a)=H_M(a,\Gamma_{K_M,a})$.
-/
lemma hierarchy_step_equation (M a : ZFSet.{u}) :
    internalHierarchy M a = hierarchyStep M a (functionGraph (fun b : a => internalHierarchy M b.val)) := by
  rw [internalHierarchy, hierarchyStep, graphRange_functionGraph (internalHierarchy M), powerImage_range]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Expand the range equality as before and the union equality by its membership clause.
    The intermediate sets belong to the model, and each clause has the required interpretation.
    Thus this formula defines the step on all internal inputs, without assuming that $a$ is an ordinal or
    that $g$ is a function.
-/
lemma realize_hierarchyStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1))
    (hrep : M ⊨ replacementSentence (powerEqFormula (0 : Fin 2) 1)) (a g b : M) :
    hierarchyStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 a) g) b) ↔
      b.val = hierarchyStep M a.val g.val := by
  simp only [hierarchyStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rangeFormula hM hunion, realize_powerImageFormula hM hpower, realize_unionFormula hM, Fin.snoc]
  constructor
  · rintro ⟨r, S, ⟨hr, hS⟩, hb⟩
    exact hb.trans (by rw [hS, hr]; rfl)
  · intro hb
    let r : M := ⟨graphRange g.val, graphRange_mem hM hunion hsep g.property⟩
    let S : M := ⟨powerImage M r.val, powerImage_mem hM hpower hrep r.property⟩
    exact ⟨r, S, ⟨rfl, rfl⟩, hb⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Range closure, the preceding image construction, and Union show that $H_M(a,g)\in M$ whenever $a,g\in M$.
-/
lemma hierarchyStep_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1))
    (hrep : M ⊨ replacementSentence (powerEqFormula (0 : Fin 2) 1)) (a g : M) :
    hierarchyStep M a.val g.val ∈ M :=
  union_mem hM hunion (powerImage_mem hM hpower hrep (graphRange_mem hM hunion hsep g.property))

/-- Every value of this internal-power-set recursion belongs to M. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Internal recursion and comparison give $K_M(a)\in M$ for $a\in M$, and their value formula satisfies
    $$M\models\nu(a,b)\quad\Longleftrightarrow\quad b=K_M(a)\qquad(a,b\in M).$$
-/
theorem internalHierarchy_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (a : M) : internalHierarchy M a.val ∈ M :=
  external_recursive_value_mem hM hinf hpair hunion hpower hsep hrep hierarchyStepFormula Fin.elim0
    (hierarchyStep M) (fun a g b => realize_hierarchyStepFormula hM hunion hpower (hsep _) (hrep _) a g b)
    (fun a g => hierarchyStep_mem hM hunion hpower (hsep _) (hrep _) a g)
    (internalHierarchy M) (hierarchy_step_equation M) a

/-- On an ordinal input, the external recursion selects exactly the model elements of lower rank. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    We prove by induction on all ordinals $\alpha$ that
    $$x\in K_M(\alpha)
    \quad\Longleftrightarrow\quad x\in M\ \land\ \mathrm{rank}(x)<\alpha.$$
    If $x\in K_M(\alpha)$, choose $\beta<\alpha$ such that $x\in\InternalPowerSet{M}{K_M(\beta)}$.
    Then $x\in M$ and $x\IncludedIn K_M(\beta)$. By induction every $z\in x$ has rank less than $\beta$, so
    $$\mathrm{rank}(x)\le\beta<\alpha.$$
    Conversely, if $x\in M$ and $\mathrm{rank}(x)<\alpha$, put $\beta:=\mathrm{rank}(x)$.
    For $z\in x$, transitivity gives $z\in M$, and $\mathrm{rank}(z)<\beta$ gives $z\in K_M(\beta)$ by induction.
    Thus $x\in\InternalPowerSet{M}{K_M(\beta)}\IncludedIn K_M(\alpha)$.
-/
theorem mem_internalHierarchy_ordinal {M : ZFSet.{u}} (hM : M.IsTransitive) (α : Ordinal.{u})
    (x : ZFSet.{u}) : x ∈ internalHierarchy M α.toZFSet ↔ x ∈ M ∧ x.rank < α := by
  rw [internalHierarchy, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨S, hS, hxS⟩
    obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hS
    obtain ⟨β, hβα, hβ⟩ := Ordinal.mem_toZFSet_iff.mp b.property
    obtain ⟨hxM, hsub⟩ := ZFSet.mem_sep.mp hxS
    have hr : x.rank ≤ β := ZFSet.rank_le_iff.mpr (by
      intro z hz
      have hzH := hsub hz
      rw [← hβ] at hzH
      exact ((mem_internalHierarchy_ordinal hM β z).mp hzH).2)
    exact ⟨hxM, hr.trans_lt hβα⟩
  · rintro ⟨hxM, hxα⟩
    refine ⟨internalPowerSet M (internalHierarchy M x.rank.toZFSet),
      ZFSet.mem_range.mpr ⟨⟨x.rank.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr hxα⟩, rfl⟩, ?_⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨hxM, ?_⟩
    intro z hz
    exact (mem_internalHierarchy_ordinal hM x.rank z).mpr ⟨hM.mem_trans hz hxM, ZFSet.rank_lt_of_mem hz⟩
termination_by α
 decreasing_by all_goals assumption

lemma internalHierarchy_eq_vonNeumann_inter {M : ZFSet.{u}} (hM : M.IsTransitive) (α : Ordinal.{u}) :
    internalHierarchy M α.toZFSet = ZFSet.vonNeumann α ∩ M := by
  apply ZFSet.ext
  intro x
  rw [mem_internalHierarchy_ordinal hM, ZFSet.mem_inter, ZFSet.mem_vonNeumann]
  exact and_comm

/-- A rank-bounded part of the model is an element of the model whenever the ordinal bound is. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal cumulative stages
-/
theorem internal_rank_segment_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {α : Ordinal.{u}} (hα : α.toZFSet ∈ M) : ZFSet.vonNeumann α ∩ M ∈ M := by
  rw [← internalHierarchy_eq_vonNeumann_inter hM]
  exact internalHierarchy_mem hM hinf hpair hunion hpower hsep hrep ⟨α.toZFSet, hα⟩

/-- Every ground set fits inside an internal cumulative stage. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Internal bounds for sets and forcing tables
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The rank-ordinal lemma gives $\mathrm{rank}(x)\in M$. Every $z\in x$ belongs to $M$ and has rank less
    than $\mathrm{rank}(x)$, proving the inclusion.
-/
theorem internal_rank_bound {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (x : M) : ∃ α : Ordinal.{u}, α.toZFSet ∈ M ∧ ZFSet.vonNeumann α ∩ M ∈ M ∧
      x.val ⊆ ZFSet.vonNeumann α ∩ M := by
  have hα := rank_mem_of_axioms hM hinf hpair hunion hpower hsep hrep x
  refine ⟨x.val.rank, hα, internal_rank_segment_mem hM hinf hpair hunion hpower hsep hrep hα, ?_⟩
  intro z hz
  exact ZFSet.mem_inter.mpr ⟨ZFSet.mem_vonNeumann.mpr (ZFSet.rank_lt_of_mem hz), hM.mem_trans hz x.property⟩

/-- A first-order value formula with no parameter naming the ambient model. -/
def internalHierarchyFormula : ForcingFormulas.Formula 2 :=
  recursiveValueFormula hierarchyStepFormula

/-- The value formula represents the recursion on every internal input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Internal recursion and comparison give $K_M(a)\in M$ for $a\in M$, and their value formula satisfies
    $$M\models\nu(a,b)\quad\Longleftrightarrow\quad b=K_M(a)\qquad(a,b\in M).$$
-/
theorem realize_internalHierarchyFormula_value {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (a b : M) :
    internalHierarchyFormula.Realize Empty.elim (Fin.snoc (Fin.snoc Fin.elim0 a) b) ↔
      b.val = internalHierarchy M a.val :=
  realize_recursiveValueFormula_external hM hinf hpair hunion hpower hsep hrep
    hierarchyStepFormula Fin.elim0 (hierarchyStep M)
    (fun a g b => realize_hierarchyStepFormula hM hunion hpower (hsep _) (hrep _) a g b)
    (fun a g => hierarchyStep_mem hM hunion hpower (hsep _) (hrep _) a g)
    (internalHierarchy M) (hierarchy_step_equation M) a b

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal cumulative stages
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The equivalence identifies $K_M(\alpha)$ with $\InternalHierarchy{M}{\alpha}$.
    For $\alpha\in M$, the preceding closure and value formula give the theorem, with $\theta:=\nu$.
-/
theorem realize_internalHierarchyFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (a b : M) (ha : a.val.IsOrdinal) :
    internalHierarchyFormula.Realize Empty.elim (Fin.snoc (Fin.snoc Fin.elim0 a) b) ↔
      b.val = ZFSet.vonNeumann a.val.rank ∩ M := by
  have he : internalHierarchy M a.val = ZFSet.vonNeumann a.val.rank ∩ M := by
    conv_lhs => rw [← ha.toZFSet_rank_eq]
    exact internalHierarchy_eq_vonNeumann_inter hM a.val.rank
  exact (realize_internalHierarchyFormula_value hM hinf hpair hunion hpower hsep hrep a b).trans
    (by rw [he])

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If $z\in y\in\InternalHierarchy{M}{\alpha}$,
    then $z\in M$ and $\mathrm{rank}(z)<\mathrm{rank}(y)<\alpha$, proving transitivity.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Internal bounds for sets and forcing tables
-/
lemma internal_rank_segment_transitive {M : ZFSet.{u}} (hM : M.IsTransitive) (α : Ordinal.{u}) :
    (ZFSet.vonNeumann α ∩ M).IsTransitive := by
  intro x hx z hz
  obtain ⟨hxα, hxM⟩ := ZFSet.mem_inter.mp hx
  exact ZFSet.mem_inter.mpr
    ⟨ZFSet.mem_vonNeumann.mpr ((ZFSet.rank_lt_of_mem hz).trans (ZFSet.mem_vonNeumann.mp hxα)),
      hM.mem_trans hz hxM⟩

/-- Name recursion stays in the same internal stage when it descends to a child name. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For a child name, the earlier pair-coordinate lemmas give $\sigma\in M$ and
    $\mathrm{rank}(\sigma)<\mathrm{rank}(\tau)<\alpha$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Internal bounds for sets and forcing tables
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    These sets bound tables of conditions and pairs of names from one internal stage, including all recursive
    calls to child names. The internal power set collects only those subsets of $B$ that belong to $M$.
-/
lemma child_mem_internal_rank_segment {M τ σ p : ZFSet.{u}} (hM : M.IsTransitive) {α : Ordinal.{u}}
    (hτ : τ ∈ ZFSet.vonNeumann α ∩ M) (hστ : pair σ p ∈ τ) :
    σ ∈ ZFSet.vonNeumann α ∩ M := by
  obtain ⟨hτα, hτM⟩ := ZFSet.mem_inter.mp hτ
  exact ZFSet.mem_inter.mpr
    ⟨ZFSet.mem_vonNeumann.mpr ((ForcingNames.child_rank_lt hστ).trans (ZFSet.mem_vonNeumann.mp hτα)),
      ForcingNames.child_mem_ground hM hτM hστ⟩

/-- Internal sets bounding the condition/name-pair tables and all their internal subsets. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Finally, apply internal product closure twice to obtain $B\in M$, then apply Power Set internally.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Internal bounds for sets and forcing tables
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    These sets bound tables of conditions and pairs of names from one internal stage, including all recursive
    calls to child names. The internal power set collects only those subsets of $B$ that belong to $M$.
-/
theorem internal_forcing_table_bounds {M P : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {α : Ordinal.{u}} (hα : α.toZFSet ∈ M) (hP : P ∈ M) :
    let W := ZFSet.vonNeumann α ∩ M
    prod P (prod W W) ∈ M ∧ internalPowerSet M (prod P (prod W W)) ∈ M := by
  dsimp only
  have hW := internal_rank_segment_mem hM hinf hpair hunion hpower hsep hrep hα
  have hWW := prod_mem_of_separation hM hpair hunion hpower (hsep _) hW hW
  have hB := prod_mem_of_separation hM hpair hunion hpower (hsep _) hP hWW
  exact ⟨hB, internalPowerSet_mem hM hpower hB⟩

end PolishSpaceBook.SetTheoryModels
