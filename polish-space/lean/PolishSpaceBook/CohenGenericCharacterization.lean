module

public import PolishSpaceBook.InternalCohenMeagerness

@[expose] public section

/-! # Cohen genericity and avoidance of internally meager Borel sets

The filter is the actual order filter of finite binary function graphs. Meagerness
is witnessed by an internal sequence of closed nowhere-dense sets, equivalently
by satisfaction of the explicit first-order cover formula.
-/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure ForcingAtomic
universe u

local instance : Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

/-- The prefix filter on the actual graph-coded forcing order. -/
def cohenPointFilter (x : ℕ → Bool) : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)) := by
  let G : Set (Condition (cohenConditionSet.{u} Set.univ)) := {p | p.val ⊆ cantorPointGraph x}
  have hpref := (isCohenFilter_iff _).mp (cohen_prefixes_isFilter x)
  have hG : Order.IsPFilter G := by
    apply Order.IsPFilter.of_def
    · exact ⟨cohenCodedCondition [], (binaryWordGraph_subset_pointGraph [] x).mpr (prefixOfSeq_nil x)⟩
    · intro p hp q hq
      obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective p
      obtain ⟨t, rfl⟩ := cohenCodedCondition_surjective q
      have hs := (binaryWordGraph_subset_pointGraph s x).mp hp
      have ht := (binaryWordGraph_subset_pointGraph t x).mp hq
      obtain ⟨r, hr, hrs, hrt⟩ := hpref.2.2 s hs t ht
      exact ⟨cohenCodedCondition r, (binaryWordGraph_subset_pointGraph r x).mpr hr,
        (cohenCodedCondition_le_iff s r).mpr hrs, (cohenCodedCondition_le_iff t r).mpr hrt⟩
    · intro p q hpq hp
      exact fun a ha => hp (hpq ha)
  exact hG.toPFilter

lemma cohenCodedCondition_mem_pointFilter (s : CohenCondition) (x : ℕ → Bool) :
    cohenCodedCondition.{u} s ∈ cohenPointFilter x ↔ x ∈ cyl s :=
  binaryWordGraph_subset_pointGraph s x

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The real $c$ is Cohen-generic over $M$ exactly when its prefix filter meets every dense subset of $\finseq{2}$
    belonging to $M$, by the ground-model condition correspondence above.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termuse{Cohen forcing} $P = \finseq{2}$ (finite binary sequences ordered by extension) adds a *Cohen real* $c \in
        \CantorSpace$. Each dense open subset $D \IncludedIn P$ determines the dense open set $\bigcup_{s \in D} \cyl{s}
        \IncludedIn \CantorSpace$, and a Cohen real is precisely a point lying in every such dense open set coded in the
        ground model — equivalently, a real avoiding every meager Borel set coded in the ground model. This is a
        *Baire-generic* point of $\CantorSpace$.
-/
lemma modelGeneric_cohenPointFilter_iff (M : ZFSet.{u}) (x : ℕ → Bool) :
    ModelGeneric (cohenConditionSet Set.univ) M (cohenPointFilter x) ↔
      ∀ D : Set CohenCondition, cohenConditionSet D ∈ M → CohenDense D →
        ∃ s ∈ D, x ∈ cyl s := by
  rw [modelGeneric_iff_cohenDense]
  simp only [cohenCodedCondition_mem_pointFilter]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

include hM hinf hpair hunion hpower hsep hrep hchoice

/-- A single internally coded closed nowhere-dense set is its own constant cover. -/
theorem internalMeagerWitness_of_closed_nowhereDense (c : Code) (hc : c.val.labelGraph ∈ M)
    (hclosed : IsClosed c.cantor) (hnd : IsNowhereDense c.cantor) :
    InternalMeagerWitness M (internalBorelCantorSet M c.val c.property.2.2.2.2.2) := by
  let A : M := ⟨_, internalBorelCantorSet_mem hM hinf hpair hunion hpower hsep c.val c.property.2.2.2.2.2 hc⟩
  refine ⟨fun _ => A.val, constantSequenceGraph_mem hM hinf hpair hsep hrep A,
    fun _ => cohenClosedPredicate_of_closed M c hclosed, ?_, ?_⟩
  · intro _
    exact (eval_cohenNowhereDensePredicate M c).mpr
      (cohenAvoidanceFamily_dense hM hinf hpair hunion hpower hsep hrep hchoice c hc hclosed hnd)
  · intro g hg
    exact (mem_sequenceUnion (fun _ => A.val) g).mpr ⟨0, hg⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Conversely, let $D\in M$ be dense in $P$. The earlier construction supplies an internal code for the closed
    nowhere-dense set $\SetDifference{\CantorSpace}{U_D}$. Its internal interpretation satisfies $C$ and $N$:
    external closedness supplies the required finite neighborhoods, and density supplies the avoiding extensions.
    Repeating this internal set gives an internal constant sequence witnessing its meagerness.
    Avoidance therefore gives $c\in U_D$, so a finite prefix of $c$ belongs to $D$.
    Since this holds for every such $D$, the prefix filter is $M$-generic.
-/
/-- Forward: choose the internal cover's codes; reverse: use the complement of each dense cylinder union. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termuse{Cohen forcing} $P = \finseq{2}$ (finite binary sequences ordered by extension) adds a *Cohen real* $c \in
        \CantorSpace$. Each dense open subset $D \IncludedIn P$ determines the dense open set $\bigcup_{s \in D} \cyl{s}
        \IncludedIn \CantorSpace$, and a Cohen real is precisely a point lying in every such dense open set coded in the
        ground model — equivalently, a real avoiding every meager Borel set coded in the ground model. This is a
        *Baire-generic* point of $\CantorSpace$.
-/
theorem cohenGeneric_iff_avoids_meager_witness (x : ℕ → Bool) :
    ModelGeneric (cohenConditionSet Set.univ) M (cohenPointFilter x) ↔
      ∀ c : Code, c.val.labelGraph ∈ M →
        InternalMeagerWitness M (internalBorelCantorSet M c.val c.property.2.2.2.2.2) →
        x ∉ c.cantor := by
  rw [modelGeneric_cohenPointFilter_iff]
  constructor
  · intro hg c hc hw
    obtain ⟨V, hV, hclosed, hnd, hcover⟩ := hw
    exact cohenGeneric_avoids_meager_witness hM hinf hpair hunion hpower hsep hrep hchoice x hg c hc
      V hV hclosed hnd hcover
  · intro ha D hDM hd
    obtain ⟨c, hcM, hcD, hcclosed, hcnd⟩ := exists_internal_closedCode_of_cohenDense
      hM hinf hpair hunion hpower hsep hrep D hDM hd
    have hxc := ha c hcM (internalMeagerWitness_of_closed_nowhereDense
      hM hinf hpair hunion hpower hsep hrep hchoice c hcM hcclosed hcnd)
    have hxD : x ∈ cylinderCode D := by
      by_contra hx
      exact hxc (hcD.symm ▸ hx)
    exact mem_cylinderCode.mp hxD

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: proposition
  title: Cohen genericity and Baire category
-/
/-- The endpoint uses the model's actual meagerness assertion, not external meagerness of old points. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termuse{Cohen forcing} $P = \finseq{2}$ (finite binary sequences ordered by extension) adds a *Cohen real* $c \in
        \CantorSpace$. Each dense open subset $D \IncludedIn P$ determines the dense open set $\bigcup_{s \in D} \cyl{s}
        \IncludedIn \CantorSpace$, and a Cohen real is precisely a point lying in every such dense open set coded in the
        ground model — equivalently, a real avoiding every meager Borel set coded in the ground model. This is a
        *Baire-generic* point of $\CantorSpace$.
-/
theorem cohenGeneric_iff_models_meager (Ω P Y : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hP : P.val = cohenConditionSet Set.univ)
    (hY : Y.val = internalCantor M) (x : ℕ → Bool) :
    ModelGeneric (cohenConditionSet Set.univ) M (cohenPointFilter x) ↔
      ∀ (c : Code) (A : M), c.val.labelGraph ∈ M →
        A.val = internalBorelCantorSet M c.val c.property.2.2.2.2.2 →
        cohenMeagerFormula.Realize Empty.elim ![Ω, P, Y, A] → x ∉ c.cantor := by
  rw [cohenGeneric_iff_avoids_meager_witness hM hinf hpair hunion hpower hsep hrep hchoice]
  constructor
  · intro h c A hc hA hm
    apply h c hc
    rw [← hA]
    exact (realize_cohenMeagerFormula hM hunion hsep Ω P Y A hΩ hP hY).mp hm
  · intro h c hc hm
    let A : M := ⟨_, internalBorelCantorSet_mem hM hinf hpair hunion hpower hsep c.val c.property.2.2.2.2.2 hc⟩
    exact h c A hc rfl ((realize_cohenMeagerFormula hM hunion hsep Ω P Y A hΩ hP hY).mpr hm)

end PolishSpaceBook
