module

public import PolishSpaceBook.ForcingPolishSpaces
public import PolishSpaceBook.CantorInternalWords
public import PolishSpaceBook.ForcingGenericTruth

@[expose] public section

/-! # Absolute density tests for ground-model Cohen conditions

Finite binary words are represented by their finite function graphs. The bounded
formula for density and the bounded separation constructing all extensions use
the same graph-inclusion relation, hence the same forcing order as the chapter.
-/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure
open ForcingAtomic
universe u

/-- A condition family as a set of finite binary function graphs. -/
def cohenConditionSet (D : Set CohenCondition) : ZFSet.{u} :=
  wordTreeSet (binaryLift D)

lemma mem_cohenConditionSet {D : Set CohenCondition} {g : ZFSet.{u}} :
    g ∈ cohenConditionSet D ↔ ∃ s ∈ D, wordGraph (s.map Bool.toNat) = g := by
  constructor
  · intro hg
    obtain ⟨_, ⟨s, hs, rfl⟩, he⟩ := mem_wordTreeSet.mp hg
    exact ⟨s, hs, he⟩
  · rintro ⟨s, hs, rfl⟩
    exact wordGraph_mem_wordTreeSet.mpr ⟨s, hs, rfl⟩

lemma binaryWordGraph_subset_iff (s t : CohenCondition) :
    wordGraph.{u} (s.map Bool.toNat) ⊆ wordGraph (t.map Bool.toNat) ↔ CohenStronger t s := by
  rw [wordGraph_subset_iff, List.prefix_map_iff_of_injective bool_toNat_injective]
  rfl

/-- Parameters are the full condition set and the candidate dense subset. -/
def cohenDensityPredicate : BoundedSetPredicate 2 :=
  .all 0 (.ex 1 (.subset 2 3))

lemma eval_cohenDensityPredicate (D : Set CohenCondition) :
    cohenDensityPredicate.eval ![cohenConditionSet.{u} Set.univ, cohenConditionSet D] ↔
      CohenDense D := by
  change (∀ s ∈ cohenConditionSet Set.univ, ∃ t ∈ cohenConditionSet D, s ⊆ t) ↔ _
  constructor
  · intro h s
    obtain ⟨t, ht, hst⟩ := h (wordGraph (s.map Bool.toNat))
      (mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩)
    obtain ⟨t, htD, rfl⟩ := mem_cohenConditionSet.mp ht
    exact ⟨t, htD, (binaryWordGraph_subset_iff s t).mp hst⟩
  · intro h s hs
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hs
    obtain ⟨t, ht, hts⟩ := h s
    exact ⟨wordGraph (t.map Bool.toNat), mem_cohenConditionSet.mpr ⟨t, ht, rfl⟩,
      (binaryWordGraph_subset_iff s t).mpr hts⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Ground-model Cohen conditions
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The model contains $\omega$, all finite binary function graphs, and their set $P$. For these graphs,
    $s\prefixOf t$ means $s\IncludedIn t$. Thus density is expressed by the bounded formula
    $$\forall s\in P\ \exists t\in D\ (s\IncludedIn t).$$
    Transitivity makes this formula absolute. Bounded separation inside $P$ constructs $E$ in $M$.
    Since $D\IncludedIn E$, we have $U_D\IncludedIn U_E$. Conversely, if $t\in E$, choose $s\in D$ with
    $s\prefixOf t$. Then $\cyl{t}\IncludedIn\cyl{s}\IncludedIn U_D$, proving the reverse inclusion.
    Every element of the internal set $P$ is the graph of a unique finite binary word. Thus every internal
    subset of $P$ corresponds to a family of words, with the same extension order and density test.
    Applying this correspondence to all dense subsets belonging to $M$ gives the assertion about genericity.
-/
/-- Transitivity transfers the actual bounded density assertion, not a separate
external density hypothesis. The condition and family sets are parameters in M. -/
theorem realize_cohenDensityPredicate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (P W : M) (D : Set CohenCondition)
    (hP : P.val = cohenConditionSet Set.univ) (hW : W.val = cohenConditionSet D) :
    cohenDensityPredicate.compile.Realize Empty.elim ![P, W] ↔ CohenDense D := by
  rw [cohenDensityPredicate.realize_compile hM]
  change cohenDensityPredicate.eval ![P.val, W.val] ↔ _
  rw [hP, hW, eval_cohenDensityPredicate]

/-- All extensions of members of a family, allowing the member itself. -/
def cohenExtensionClosure (D : Set CohenCondition) : Set CohenCondition :=
  {t | ∃ s ∈ D, CohenStronger t s}

/-- Parameters are the original family and a candidate finite function graph. -/
def cohenExtensionPredicate : BoundedSetPredicate 2 := .ex 0 (.subset 2 1)

lemma eval_cohenExtensionPredicate (D : Set CohenCondition) (t : CohenCondition) :
    cohenExtensionPredicate.eval ![cohenConditionSet.{u} D, wordGraph (t.map Bool.toNat)] ↔
      t ∈ cohenExtensionClosure D := by
  change (∃ s ∈ cohenConditionSet D, s ⊆ wordGraph (t.map Bool.toNat)) ↔ _
  constructor
  · rintro ⟨s, hs, hst⟩
    obtain ⟨s, hsD, rfl⟩ := mem_cohenConditionSet.mp hs
    exact ⟨s, hsD, (binaryWordGraph_subset_iff s t).mp hst⟩
  · rintro ⟨s, hs, hts⟩
    exact ⟨wordGraph (s.map Bool.toNat), mem_cohenConditionSet.mpr ⟨s, hs, rfl⟩,
      (binaryWordGraph_subset_iff s t).mpr hts⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Ground-model Cohen conditions
-/
theorem cohenExtensionClosure_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (D : Set CohenCondition) (hD : cohenConditionSet D ∈ M) :
    cohenConditionSet (cohenExtensionClosure D) ∈ M := by
  let W : M := ⟨cohenConditionSet D, hD⟩
  apply cohenExtensionPredicate.subset_mem hM (hsep _) ![W]
    (binaryWords_mem hM hinf hpair hunion hpower hsep)
  · intro g hg
    obtain ⟨t, _, rfl⟩ := mem_cohenConditionSet.mp hg
    exact mem_cohenConditionSet.mpr ⟨t, Set.mem_univ _, rfl⟩
  · intro g hg
    obtain ⟨t, _, rfl⟩ := mem_cohenConditionSet.mp hg
    change cohenExtensionPredicate.eval ![cohenConditionSet D, wordGraph (t.map Bool.toNat)] ↔ _
    rw [eval_cohenExtensionPredicate]
    constructor
    · intro ht
      exact mem_cohenConditionSet.mpr ⟨t, ht, rfl⟩
    · intro ht
      obtain ⟨s, hs, he⟩ := mem_cohenConditionSet.mp ht
      have hst := (List.map_injective_iff.mpr bool_toNat_injective) (wordGraph_injective he)
      simpa only [hst] using hs

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Ground-model Cohen conditions
-/
theorem cohenExtensionClosure_cylinderCode (D : Set CohenCondition) :
    cylinderCode (cohenExtensionClosure D) = cylinderCode D := by
  ext x
  simp only [mem_cylinderCode]
  constructor
  · rintro ⟨t, ⟨s, hs, hts⟩, hxt⟩
    exact ⟨s, hs, cyl_subset_of_prefix hts hxt⟩
  · rintro ⟨s, hs, hxs⟩
    exact ⟨s, ⟨s, hs, List.prefix_refl s⟩, hxs⟩

/-- The coded condition has precisely the finite function graph of the word. -/
def cohenCodedCondition (s : CohenCondition) : Condition (cohenConditionSet.{u} Set.univ) :=
  ⟨wordGraph (s.map Bool.toNat), mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩⟩

lemma cohenCodedCondition_surjective : Function.Surjective cohenCodedCondition.{u} := by
  rintro ⟨p, hp⟩
  obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hp
  exact ⟨s, rfl⟩

/-- Stronger finite functions extend weaker finite functions. -/
@[reducible] def internalCohenOrder : Preorder (Condition (cohenConditionSet.{u} Set.univ)) where
  le p q := q.val ⊆ p.val
  le_refl _ := fun _ h => h
  le_trans _ _ _ hpq hqr := fun _ h => hpq (hqr h)

local instance : Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

lemma cohenCodedCondition_le_iff (s t : CohenCondition) :
    cohenCodedCondition.{u} t ≤ cohenCodedCondition s ↔ CohenStronger t s :=
  binaryWordGraph_subset_iff s t

lemma cohenCodedCondition_mem_iff (s : CohenCondition) (D : Set CohenCondition) :
    (cohenCodedCondition.{u} s).val ∈ cohenConditionSet D ↔ s ∈ D := by
  constructor
  · intro hs
    obtain ⟨t, ht, he⟩ := mem_cohenConditionSet.mp hs
    have hts := (List.map_injective_iff.mpr bool_toNat_injective) (wordGraph_injective he)
    simpa only [hts] using ht
  · intro hs
    exact mem_cohenConditionSet.mpr ⟨s, hs, rfl⟩

lemma cohenDense_iff_coded (D : Set CohenCondition) :
    CohenDense D ↔ IsCoinitial {p : Condition (cohenConditionSet.{u} Set.univ) |
      p.val ∈ cohenConditionSet D} := by
  constructor
  · intro h p
    obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective p
    obtain ⟨t, ht, hts⟩ := h s
    exact ⟨cohenCodedCondition t, (cohenCodedCondition_mem_iff t D).mpr ht,
      (cohenCodedCondition_le_iff s t).mpr hts⟩
  · intro h s
    obtain ⟨p, hp, hps⟩ := h (cohenCodedCondition s)
    obtain ⟨t, rfl⟩ := cohenCodedCondition_surjective p
    exact ⟨t, (cohenCodedCondition_mem_iff t D).mp hp,
      (cohenCodedCondition_le_iff s t).mp hps⟩

lemma cohenConditionSet_decode {W : ZFSet.{u}} (hW : W ⊆ cohenConditionSet Set.univ) :
    cohenConditionSet {s | (cohenCodedCondition s).val ∈ W} = W := by
  ext g
  constructor
  · intro hg
    obtain ⟨s, hs, rfl⟩ := mem_cohenConditionSet.mp hg
    exact hs
  · intro hg
    obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp (hW hg)
    exact mem_cohenConditionSet.mpr ⟨s, hg, rfl⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Ground-model Cohen conditions
-/
/-- The finite-word formulation meets every actual internal dense subset, not
only a selected list of requirements. No external countability of M is needed. -/
theorem modelGeneric_iff_cohenDense (M : ZFSet.{u})
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ))) :
    ModelGeneric (cohenConditionSet Set.univ) M G ↔
      ∀ D : Set CohenCondition, cohenConditionSet D ∈ M → CohenDense D →
        ∃ s ∈ D, cohenCodedCondition s ∈ G := by
  constructor
  · intro h D hDM hd
    have hsub : cohenConditionSet D ⊆ cohenConditionSet Set.univ := by
      intro g hg
      obtain ⟨s, _, rfl⟩ := mem_cohenConditionSet.mp hg
      exact mem_cohenConditionSet.mpr ⟨s, Set.mem_univ _, rfl⟩
    obtain ⟨p, hpG, hpD⟩ := h _ hDM hsub ((cohenDense_iff_coded D).mp hd)
    obtain ⟨s, rfl⟩ := cohenCodedCondition_surjective p
    exact ⟨s, (cohenCodedCondition_mem_iff s D).mp hpD, hpG⟩
  · intro h W hWM hWP hd
    let D : Set CohenCondition := {s | (cohenCodedCondition s).val ∈ W}
    have he : cohenConditionSet D = W := cohenConditionSet_decode hWP
    have hDM : cohenConditionSet D ∈ M := he ▸ hWM
    have hD : CohenDense D := (cohenDense_iff_coded D).mpr (by rw [he]; exact hd)
    obtain ⟨s, hsD, hsG⟩ := h D hDM hD
    exact ⟨cohenCodedCondition s, hsG, hsD⟩

end PolishSpaceBook
