module

public import PolishSpaceBook.SetTheoryLeastChoice

@[expose] public section

/-! # Choice graphs collected by Replacement from ordinally indexed covers -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Both graphs and all three bounds are sets of the model; U may be a proper subset of D. -/
def HasOrdinalCover (N X : ZFSet.{u}) : Prop :=
  ∃ γ D U e F : N, γ.val.IsOrdinal ∧ ZFSet.IsFunc γ.val D.val e.val ∧
    (∀ d ∈ D.val, ∃ a ∈ γ.val, pair a d ∈ e.val) ∧ U.val ⊆ D.val ∧
    ZFSet.IsFunc U.val X F.val ∧ (∀ x ∈ X, ∃ d ∈ U.val, pair d x ∈ F.val)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply the definable-graph construction in §{sec:internal-model-closure} inside $N$ to the selector
    $$\rho(y,q)\;:\equiv\;\exists x\,
     (\psi(y,x)\land q=\langle y,x\rangle).$$
    Pairing supplies its ordered-pair witnesses, and the Replacement instance for $\rho$ collects the whole graph
    $$c:=\{\langle y,x\rangle:y\in A\land N\models\psi(y,x)\}\in N.$$
    The uniqueness just proved makes $c$ a function on $A$, and each value belongs to its input set.
    Consequently
    $$c:A\to\bigcup A,\qquad c(y)\in y\quad(y\in A).$$
    This is the Choice sentence in $N$. The same construction covers the empty family, when the graph is empty.
    The only choice graph assumed at the outset was in the ground model, used to enumerate $D$.
    No Choice axiom in the extension or ordering of the proper class of all names was used.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Fix $y\in A$. There is some $x\in y$, and surjectivity of $F$ gives $d\in U$ with $F(d)=x$.
    Since $U\IncludedIn D$, surjectivity of $e$ gives $\alpha\in\gamma$ with $e(\alpha)=d$.
    Hence $C(y,\alpha)$ holds for some $\alpha\in\gamma$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Since $x\in y\in N$, transitivity puts this unique output in $N$.
-/
theorem internal_choice_graph_of_cover {N : ZFSet.{u}} (hN : N.IsTransitive)
    (hpair : N ⊨ pairingSentence) (hunion : N ⊨ unionSentence)
    (hrep : N ⊨ replacementSentence (graphSelector leastOrdinalChoiceFormula))
    (A γ D U e F : N) (hA : ∀ y ∈ A.val, ∃ x, x ∈ y) (hγ : γ.val.IsOrdinal)
    (he : ZFSet.IsFunc γ.val D.val e.val) (heonto : ∀ d ∈ D.val, ∃ a ∈ γ.val, pair a d ∈ e.val)
    (hUD : U.val ⊆ D.val) (hF : ZFSet.IsFunc U.val (ZFSet.sUnion A.val) F.val)
    (hFonto : ∀ x ∈ ZFSet.sUnion A.val, ∃ d ∈ U.val, pair d x ∈ F.val) :
    ∃ c : N, ZFSet.IsFunc A.val (ZFSet.sUnion A.val) c.val ∧
      ∀ y ∈ A.val, ∃ x ∈ y, pair y x ∈ c.val := by
  classical
  have hex (y : A.val) : ∃ x, LeastOrdinalChoice γ.val e.val F.val y.val x := by
    obtain ⟨x, hx⟩ := hA y.val y.property
    obtain ⟨d, hd, hdx⟩ := hFonto x (ZFSet.mem_sUnion.mpr ⟨y.val, y.property, hx⟩)
    obtain ⟨a, ha, had⟩ := heonto d (hUD hd)
    exact leastOrdinalChoice_exists hγ ⟨a, ha, x, hx, d, had, hdx⟩
  let pick (y : A.val) : ZFSet.{u} := (hex y).choose
  have hpick (y : A.val) : LeastOrdinalChoice γ.val e.val F.val y.val (pick y) := (hex y).choose_spec
  have hxy (y : A.val) : pick y ∈ y.val := by
    obtain ⟨_, _, hx, _⟩ := hpick y
    exact hx.1
  let value (y : A.val) : N := ⟨pick y, hN.mem_trans (hxy y) (hN.mem_trans y.property A.property)⟩
  have hc : functionGraph (fun y : A.val => (value y).val) ∈ N := by
    apply replacement_graph_mem hN hpair leastOrdinalChoiceFormula hrep ![γ, e, F] A.property value
    intro y x
    rw [realize_leastOrdinalChoiceFormula hN hunion]
    constructor
    · intro hx
      exact Subtype.ext (leastOrdinalChoice_unique hγ he hF hx (hpick y))
    · intro hx
      have hval := congrArg Subtype.val hx
      rw [hval]
      exact hpick y
  refine ⟨⟨_, hc⟩, ?_, ?_⟩
  · refine ⟨?_, (functionGraph_isFunc (fun y : A.val => (value y).val)).2⟩
    intro p hp
    obtain ⟨y, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨y.property, ZFSet.mem_sUnion.mpr ⟨y.val, y.property, hxy y⟩⟩
  · intro y hy
    exact ⟨pick ⟨y, hy⟩, hxy ⟨y, hy⟩, ZFSet.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩⟩

theorem models_choice_of_ordinal_covers {N : ZFSet.{u}} (hN : N.IsTransitive)
    (hpair : N ⊨ pairingSentence) (hunion : N ⊨ unionSentence)
    (hrep : N ⊨ replacementSentence (graphSelector leastOrdinalChoiceFormula))
    (hcover : ∀ X : N, HasOrdinalCover N X.val) : N ⊨ choiceSentence := by
  apply (models_choice_iff hN hunion).mpr
  intro A hA
  let X : N := ⟨ZFSet.sUnion A.val, union_mem hN hunion A.property⟩
  obtain ⟨γ, D, U, e, F, hγ, he, heonto, hUD, hF, hFonto⟩ := hcover X
  exact internal_choice_graph_of_cover hN hpair hunion hrep A γ D U e F hA hγ he heonto hUD hF hFonto

end PolishSpaceBook.SetTheoryModels
