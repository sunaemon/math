module

public import PolishSpaceBook.ForcingEvaluationGraphs
public import PolishSpaceBook.ForcingReplacement
public import PolishSpaceBook.ForcingUnionClosure

@[expose] public section

/-! # Every extension set is an internal quotient of a subset of a ground set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingNames ForcingAtomic ForcingFormulas
universe u

/-- Select actual names from a specified ground set. -/
def namesIn (P A : ZFSet.{u}) : ZFSet.{u} := A.sep (IsName P)

/-- An input has an output in x under a set-coded graph e. -/
def graphPreimageFormula : ForcingFormulas.Formula 3 :=
  boundedExists (1 : Fin 3) (pairMemberFormula (0 : Fin 4) 2 3)

lemma realize_graphPreimageFormula {S : ZFSet.{u}} (hS : S.IsTransitive) (e x a : S) :
    graphPreimageFormula.Realize Empty.elim (Fin.snoc ![e, x] a) ↔
      ∃ b : S, b.val ∈ x.val ∧ pair a.val b.val ∈ e.val := by
  simp only [graphPreimageFormula, realize_boundedExists_model, realize_pairMemberFormula_model hS]
  rfl

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
include hM hinf hpair hunion hpower hsep hrep

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Here $\eta$ is the defining formula for names from §{sec:internal-forcing-formulas};
    Separation in $M$ constructs $D$. Thus its elements are exactly the names in $A$.
-/
lemma namesIn_mem (P A : M) : namesIn P.val A.val ∈ M := by
  apply separation_mem_of_absolute hM nameFormula (hsep _) ![P] A.property
  intro σ _
  have he : Fin.snoc ![P] σ = ![P, σ] := by ext i; fin_cases i <;> rfl
  rw [he]
  exact name_definable hM hinf hpair hunion hpower hsep hrep P σ

variable (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
include hR

/-- The domain may be new, but it is a subset of a ground set; the function itself is in the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The preceding theorem gives $e_D\in M[G]$, and check-name closure gives $D\in M[G]$.
    Apply Separation in the extension to obtain
    $$\begin{aligned}
    U&:=\{\sigma\in D:\exists b\in x\ \langle\sigma,b\rangle\in e_D\}\\
     &=\{\sigma\in D:\sigma^G\in x\}\in M[G].
    \end{aligned}$$
    The first line uses an actual first-order formula with parameters $e_D,x$.
    Transitivity and the graph identity justify the second line.
    Restrict the graph to these inputs:
    $$F:=e_D\cap\bigl(U\times\bigcup\bigcup e_D\bigr)\in M[G].$$
    This graph restriction belongs to the extension by Union and Separation, as proved in
    §{sec:internal-model-closure}. For each $\sigma\in U$, its unique output is $\sigma^G\in x$.
    Conversely, each $b\in x$ has a name $\sigma\in D$ found above; this name belongs to $U$ and is mapped to $b$.
    Thus $F:U\twoheadrightarrow x$. No selection of one name for each $b$ was needed.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Write $x=\tau^G$ with $\tau\in M^P$ and put
    $$\begin{aligned}
    A&:=\bigcup\bigcup\tau\in M,\\
    D&:=\{\sigma\in A:M\models\eta(P,\sigma)\}\in M.
    \end{aligned}$$
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For every $b\in x$, the valuation equation supplies $\langle\sigma,r\rangle\in\tau$ with
    $r\in G$ and $\sigma^G=b$. The child-name lemma gives $\sigma\in A\cap M^P=D$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Ground-set covers of generic extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To use the evaluation of names in an internal construction, its graph must belong to the extension.
    We first construct this graph on any ground-model set of names, then restrict it to obtain a surjection
    onto a given extension set. Neither construction uses Choice.
-/
theorem extension_ground_cover (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (x : Extension P.val M G) :
    ∃ D : M, ∃ U F : Extension P.val M G, U.val ⊆ D.val ∧ ZFSet.IsFunc U.val x.val F.val ∧
      ∀ b ∈ x.val, ∃ a ∈ U.val, pair a b ∈ F.val := by
  have hg : ∃ p ∈ chosen P.val G, p ∈ P.val := by
    obtain ⟨q, hq⟩ := G.nonempty
    exact ⟨q.val, ⟨q, hq, rfl⟩, q.property⟩
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  have hME := ground_subset_extension_of_axioms hM hinf hpair hunion hpower hsep hrep P.property
    (chosen P.val G) hg
  obtain ⟨τ, hτ⟩ := evalName_surjective P.val M G x
  have hx : value P.val G τ.val = x.val := congrArg Subtype.val hτ
  let A : M := ⟨childBound τ.val, union_mem hM hunion (union_mem hM hunion τ.property.1)⟩
  let D : M := ⟨namesIn P.val A.val, namesIn_mem hM hinf hpair hunion hpower hsep hrep P A⟩
  have hDN : ∀ σ ∈ D.val, IsName P.val σ := fun _ h => (ZFSet.mem_sep.mp h).2
  let eVal := functionGraph (fun σ : D.val => valuation (chosen P.val G) σ.val)
  have heM : eVal ∈ Extension P.val M G :=
    evaluationGraph_mem_extension hM hinf hpair hunion hpower hsep hrep P D hDN (chosen P.val G) hg
  let e : Extension P.val M G := ⟨eVal, heM⟩
  have hePair (a b : ZFSet.{u}) : pair a b ∈ eVal ↔ a ∈ D.val ∧ value P.val G a = b :=
    pair_mem_evaluationGraph D.val (chosen P.val G) a b
  have hcover (b : ZFSet.{u}) (hb : b ∈ x.val) : ∃ a ∈ D.val, value P.val G a = b := by
    rw [← hx] at hb
    obtain ⟨σ, _, _, hστ, he⟩ := (mem_value P.val G τ.val b).mp hb
    exact ⟨σ, ZFSet.mem_sep.mpr ⟨child_mem_doubleUnion hστ, τ.property.2.child hστ⟩, he⟩
  have hsepE : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)),
      Extension P.val M G ⊨ separationSentence φ :=
    fun φ => extension_models_separation hM hinf hpair hunion hpower hsep hrep P R hR G hG φ
  obtain ⟨U, hU⟩ := (realize_separation _ graphPreimageFormula).mp (hsepE _) ![e, x] ⟨D.val, hME D.property⟩
  have hu (a : ZFSet.{u}) : a ∈ U.val ↔ a ∈ D.val ∧ value P.val G a ∈ x.val := by
    constructor
    · intro ha
      let aE : Extension P.val M G := ⟨a, hE.mem_trans ha U.property⟩
      obtain ⟨haD, hpre⟩ := (hU aE).mp ha
      obtain ⟨b, hbx, hab⟩ := (realize_graphPreimageFormula hE e x aE).mp hpre
      have he := ((hePair a b.val).mp hab).2
      exact ⟨haD, he.symm ▸ hbx⟩
    · rintro ⟨haD, hax⟩
      let aE : Extension P.val M G := ⟨a, hME (hM.mem_trans haD D.property)⟩
      let bE : Extension P.val M G := ⟨value P.val G a, hE.mem_trans hax x.property⟩
      apply (hU aE).mpr
      exact ⟨haD, (realize_graphPreimageFormula hE e x aE).mpr
        ⟨bE, hax, (hePair a (value P.val G a)).mpr ⟨haD, rfl⟩⟩⟩
  have hUE := extension_models_union hM hinf hpair hunion hpower (hrep _) (hrep _)
    P.property R.property hR G
  let F : Extension P.val M G := ⟨restrictGraph eVal U.val,
    restrictGraph_mem hE hUE (hsepE _) heM U.property⟩
  refine ⟨D, U, F, fun _ ha => ((hu _).mp ha).1, ?_, ?_⟩
  · change ZFSet.IsFunc U.val x.val (restrictGraph eVal U.val)
    constructor
    · intro z hz
      obtain ⟨a, ha, b, rfl, hab⟩ := mem_restrictGraph.mp hz
      have hb := ((hePair a b).mp hab).2 ▸ ((hu a).mp ha).2
      exact ZFSet.pair_mem_prod.mpr ⟨ha, hb⟩
    · intro a ha
      refine ⟨value P.val G a, pair_mem_restrictGraph.mpr
        ⟨(hePair a (value P.val G a)).mpr ⟨((hu a).mp ha).1, rfl⟩, ha⟩, ?_⟩
      intro b hb
      exact ((hePair a b).mp (pair_mem_restrictGraph.mp hb).1).2.symm
  · change ∀ b ∈ x.val, ∃ a ∈ U.val, pair a b ∈ restrictGraph eVal U.val
    intro b hb
    obtain ⟨a, haD, he⟩ := hcover b hb
    have haU := (hu a).mpr ⟨haD, he.symm ▸ hb⟩
    exact ⟨a, haU, pair_mem_restrictGraph.mpr ⟨(hePair a b).mpr ⟨haD, he⟩, haU⟩⟩

end Model
end PolishSpaceBook.SetTheoryModels
