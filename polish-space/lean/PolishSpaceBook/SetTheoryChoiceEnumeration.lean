module

public import PolishSpaceBook.SetTheoryInternalHartogs
public import PolishSpaceBook.SetTheoryFreshChoice

@[expose] public section

/-! # Internal ordinal enumerations obtained from Choice and the Hartogs bound -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma selection_value_fresh {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (W c A f : M)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val)
    (hf : IsRecursiveSolution (freshStep W.val c.val) A.val f.val)
    {a b : ZFSet.{u}} (ha : a ∈ A.val) (hab : pair a b ∈ f.val)
    (hne : ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a)) :
    b ∈ W.val ∧ b ∉ graphRange (restrictGraph f.val a) := by
  have haM := hM.mem_trans ha A.property
  have hgM := restrictGraph_mem hM hunion (hsep _) f.property haM
  have hb : b = freshStep W.val c.val a (restrictGraph f.val a) :=
    (hf.function_graph.2 a ha).unique hab (hf.equation a ha)
  rw [hb]
  exact freshStep_fresh hM hunion (hsep _) W c ⟨a, haM⟩ ⟨_, hgM⟩ hc hs hne

lemma selection_injective_on {A D f : ZFSet.{u}} (hA : A.IsOrdinal) (hDA : D ⊆ A)
    (hnew : ∀ a ∈ D, ∀ b, pair a b ∈ f → b ∉ graphRange (restrictGraph f a))
    {a b x : ZFSet.{u}} (ha : a ∈ D) (hb : b ∈ D) (hax : pair a x ∈ f) (hbx : pair b x ∈ f) :
    a = b := by
  rcases (hA.mem (hDA ha)).mem_trichotomous (hA.mem (hDA hb)) with hab | he | hba
  · exact False.elim (hnew b hb x hbx (mem_graphRange.mpr ⟨a, pair_mem_restrictGraph.mpr ⟨hax, hab⟩⟩))
  · exact he
  · exact False.elim (hnew a ha x hax (mem_graphRange.mpr ⟨b, pair_mem_restrictGraph.mpr ⟨hbx, hba⟩⟩))

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take the choice graph $c$ from §{sec:internal-choice-recursion} and the internal Hartogs bound $H$ for $W$.
    Internal selection recursion on $H$ gives a function graph $f\in M$.
    Suppose the remaining set
    $$r_\beta:=\{z\in W:z\notin\GraphRange{\restrict{f}{\beta}}\}$$
    is nonempty for every $\beta\in H$. Then $f(\beta)\in W$ at every stage.
    If $\alpha\in\beta\in H$, the earlier value $f(\alpha)$ belongs to
    $\GraphRange{\restrict{f}{\beta}}$, whereas $f(\beta)$ does not.
    The linearity of membership on ordinals therefore makes $f:H\to W$ injective.
    Its graph belongs to $M$, contradicting the defining property of $H$.
-/
lemma selection_exhausts {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (W c H f : M) (hH : H.val.IsOrdinal)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val)
    (hf : IsRecursiveSolution (freshStep W.val c.val) H.val f.val)
    (hbound : ∀ g : M, ZFSet.IsFunc H.val W.val g.val →
      ¬ (∀ a b x, pair a x ∈ g.val → pair b x ∈ g.val → a = b)) :
    ∃ a ∈ H.val, ¬ ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a) := by
  classical
  by_contra! hne
  have hnew : ∀ a ∈ H.val, ∀ b, pair a b ∈ f.val →
      b ∈ W.val ∧ b ∉ graphRange (restrictGraph f.val a) := by
    intro a ha b hb
    exact selection_value_fresh hM hunion hsep W c H f hc hs hf ha hb (hne a ha)
  have hfunc : ZFSet.IsFunc H.val W.val f.val := by
    refine ⟨?_, hf.function_graph.2⟩
    intro p hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.function_graph.1 hp)
    exact ZFSet.pair_mem_prod.mpr ⟨ha, (hnew a ha b hp).1⟩
  apply hbound f hfunc
  intro a b x hax hbx
  exact selection_injective_on hH (fun _ h => h) (fun a ha b hb => (hnew a ha b hb).2)
    (ZFSet.pair_mem_prod.mp (hfunc.1 hax)).1 (ZFSet.pair_mem_prod.mp (hfunc.1 hbx)).1 hax hbx

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    There is consequently a least $\gamma\in H$ with $r_\gamma=\emptyset$.
    Transitivity gives $\gamma\in M$, and graph restriction gives
    $$e:=\restrict{f}{\gamma}\in M.$$
    Every earlier remainder is nonempty. Thus all values of $e$ lie in $W$, and the same comparison of stages
    shows that $e$ is injective. The equality $r_\gamma=\emptyset$ says that every element of $W$ already occurs
    in this graph, so $e$ is onto $W$.
    This proves the asserted internal ordinal enumeration, including the case of an empty set.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A choice graph supplies the step rule for selecting successive elements of a set. An internal Hartogs bound,
    which does not require Choice, bounds the length of an injective selection. Combining the two gives an ordinal
    enumeration whose entire graph belongs to the model.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When $A$ is an ordinal, this recursion selects a new element at every stage with a nonempty remainder.
    The bound constructed in §{sec:internal-hartogs-bound} forces a remainder to become empty.
    §{sec:internal-choice-enumerations} then cuts the graph at the first such stage to obtain an enumeration
    of all of $W$.
-/
theorem internal_choice_enumeration {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W : M) :
    ∃ γ e : M, γ.val.IsOrdinal ∧ ZFSet.IsFunc γ.val W.val e.val ∧
      (∀ x ∈ W.val, ∃ a ∈ γ.val, pair a x ∈ e.val) ∧
      (∀ a b x, pair a x ∈ e.val → pair b x ∈ e.val → a = b) := by
  classical
  obtain ⟨c, hc, hs⟩ := internal_subset_choice hM hunion hpower (hsep _) hchoice W.property
  obtain ⟨H, hH, hbound⟩ := internal_hartogs_bound hM hpair hunion hpower hsep (hrep _) W
  obtain ⟨f, hf, _⟩ := internal_fresh_recursion hM (empty_mem_of_infinity hM hinf)
    hpair hunion hpower hsep hrep W c H hH.isTransitive hc hs
  have hex := selection_exhausts hM hunion hsep W c H f hH hc hs hf hbound
  let S : Set ZFSet.{u} := {a | a ∈ H.val ∧ ¬ ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a)}
  obtain ⟨γ, hγ, hmin⟩ := ZFSet.mem_wf.has_min S hex
  have hγH : γ ∈ H.val := hγ.1
  have hγM := hM.mem_trans hγH H.property
  have hγord := hH.mem hγH
  have hγsub : γ ⊆ H.val := hH.subset_of_mem hγH
  have hne (a : ZFSet.{u}) (ha : a ∈ γ) : ∃ z, z ∈ remainingSet W.val (restrictGraph f.val a) := by
    by_contra hnot
    exact hmin a ⟨hγsub ha, hnot⟩ ha
  have hnew : ∀ a ∈ γ, ∀ b, pair a b ∈ f.val →
      b ∈ W.val ∧ b ∉ graphRange (restrictGraph f.val a) := by
    intro a ha b hb
    exact selection_value_fresh hM hunion hsep W c H f hc hs hf (hγsub ha) hb (hne a ha)
  let e : M := ⟨restrictGraph f.val γ, restrictGraph_mem hM hunion (hsep _) f.property hγM⟩
  have he : ZFSet.IsFunc γ W.val e.val := by
    refine ⟨?_, (isFunc_restrictGraph hf.function_graph hγsub).2⟩
    intro p hp
    obtain ⟨a, ha, b, rfl, hab⟩ := mem_restrictGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨ha, (hnew a ha b hab).1⟩
  refine ⟨⟨γ, hγM⟩, e, hγord, he, ?_, ?_⟩
  · intro x hx
    by_contra hnot
    apply hγ.2
    refine ⟨x, mem_remainingSet.mpr ⟨hx, ?_⟩⟩
    intro hxrange
    obtain ⟨a, ha⟩ := mem_graphRange.mp hxrange
    exact hnot ⟨a, (pair_mem_restrictGraph.mp ha).2, ha⟩
  · intro a b x hax hbx
    obtain ⟨hax', ha⟩ := pair_mem_restrictGraph.mp hax
    obtain ⟨hbx', hb⟩ := pair_mem_restrictGraph.mp hbx
    exact selection_injective_on hH hγsub (fun a ha b hb => (hnew a ha b hb).2) ha hb hax' hbx'

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Finally, repeat the transported-relation and inverse-graph construction from the Hartogs proof with $j=e$.
    Its range is now all of $W$, and its domain is $\gamma$.
    It gives $R\IncludedIn W\times W$ and $g=e^{-1}$, both belonging to $M$.
    The graph $g$ is an order-isomorphism from $(W,R)$ onto $\gamma$; internal recognition gives the displayed
    assertion. This connects the enumeration directly to the ordinal-representation predicate used in
    §{sec:internal-ordinal-representations}.
    \end{proof}
-/
/-- The inverse of a specified internal enumeration represents its transported order. -/
theorem ordinal_representation_of_internal_enumeration {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (W γ e : M) (hγ : γ.val.IsOrdinal) (he : ZFSet.IsFunc γ.val W.val e.val)
    (honto : ∀ x ∈ W.val, ∃ a ∈ γ.val, pair a x ∈ e.val)
    (hinj : ∀ a b x, pair a x ∈ e.val → pair b x ∈ e.val → a = b) :
    ∃ R g : M, R.val ⊆ ZFSet.prod W.val W.val ∧
      g.val = inverseGraph e.val γ.val W.val ∧
      ordinalIsoFormula.Realize Empty.elim ![W, R, γ, g] := by
  have hrange : graphRange e.val = W.val := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := mem_graphRange.mp hx
      exact (ZFSet.pair_mem_prod.mp (he.1 ha)).2
    · intro hx
      obtain ⟨a, _, ha⟩ := honto x hx
      exact mem_graphRange.mpr ⟨a, ha⟩
  let R : M := ⟨transportedMembership e.val W.val,
    transportedMembership_mem hM hpair hunion hpower hsep e.property W.property⟩
  let g : M := ⟨inverseGraph e.val γ.val W.val,
    inverseGraph_mem hM hpair hunion hpower hsep e.property γ.property W.property⟩
  refine ⟨R, g, ?_, rfl, ?_⟩
  · intro p hp
    dsimp only [R, transportedMembership] at hp
    exact (ZFSet.mem_sep.mp hp).1
  · have hi := injection_ordinalIso he hinj
    rw [hrange] at hi
    exact (realize_ordinalIsoFormula hM W R γ g).mpr ⟨hγ, hi⟩

/-- Enumeration and ordinal representation use the same ordinal and mutually inverse graphs. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal ordinal enumeration from Choice
-/
theorem internal_choice_enumeration_and_representation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W : M) :
    ∃ γ e R g : M, γ.val.IsOrdinal ∧ ZFSet.IsFunc γ.val W.val e.val ∧
      (∀ x ∈ W.val, ∃ a ∈ γ.val, pair a x ∈ e.val) ∧
      (∀ a b x, pair a x ∈ e.val → pair b x ∈ e.val → a = b) ∧
      R.val ⊆ ZFSet.prod W.val W.val ∧ g.val = inverseGraph e.val γ.val W.val ∧
      ordinalIsoFormula.Realize Empty.elim ![W, R, γ, g] := by
  obtain ⟨γ, e, hγ, he, honto, hinj⟩ :=
    internal_choice_enumeration hM hinf hpair hunion hpower hsep hrep hchoice W
  obtain ⟨R, g, hR, hg, hi⟩ :=
    ordinal_representation_of_internal_enumeration hM hpair hunion hpower hsep W γ e hγ he honto hinj
  exact ⟨γ, e, R, g, hγ, he, honto, hinj, hR, hg, hi⟩

/-- The representation part of the combined construction. -/
theorem internal_choice_ordinal_representation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (W : M) :
    ∃ R γ g : M, R.val ⊆ ZFSet.prod W.val W.val ∧
      ordinalIsoFormula.Realize Empty.elim ![W, R, γ, g] := by
  obtain ⟨γ, _, R, g, _, _, _, _, hR, _, hi⟩ :=
    internal_choice_enumeration_and_representation hM hinf hpair hunion hpower hsep hrep hchoice W
  exact ⟨R, γ, g, hR, hi⟩

end PolishSpaceBook.SetTheoryModels
