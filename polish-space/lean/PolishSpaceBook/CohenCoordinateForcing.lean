module

public import PolishSpaceBook.ForcingCohenValuation
public import PolishSpaceBook.ForcingBookNotions

@[expose] public section

/-! # Finite conditions force the coordinates of the actual Cohen union name -/

noncomputable section
namespace PolishSpaceBook
open ZFSet SetTheoryModels ForcingNames ForcingAtomic
open FirstOrder Language
open CantorTreeMeasure BorelExpression
universe u

local instance cohenCoordinateOrder : Preorder (Condition (cohenConditionSet.{u} Set.univ)) := internalCohenOrder

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Two conditions are compatible iff one is an initial segment of the other.
-/
theorem cohen_compatible_iff_prefix (s t : CohenCondition) :
    ForcingCompatible (cohenCodedCondition.{u} s) (cohenCodedCondition t) ↔
      s.IsPrefix t ∨ t.IsPrefix s := by
  constructor
  · rintro ⟨r, hrs, hrt⟩
    obtain ⟨v, rfl⟩ := cohenCodedCondition_surjective r
    exact List.prefix_or_prefix_of_prefix
      ((cohenCodedCondition_le_iff s v).mp hrs)
      ((cohenCodedCondition_le_iff t v).mp hrt)
  · rintro (hst | hts)
    · exact ⟨cohenCodedCondition t, (cohenCodedCondition_le_iff s t).mpr hst, le_rfl⟩
    · exact ⟨cohenCodedCondition s, le_rfl, (cohenCodedCondition_le_iff t s).mpr hts⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $s \in P$, the corresponding basic open set in Cantor space is the cylinder
    $$\cyl{s}=\{x\in\CantorSpace:s\prefixOf x\}.$$
    Stronger conditions correspond to smaller cylinders:
    $$t \le s \quad\Longleftrightarrow\quad \cyl{t}\IncludedIn \cyl{s}.$$
-/
theorem cohen_stronger_iff_cylinder_subset (s t : CohenCondition) :
    cohenCodedCondition.{u} t ≤ cohenCodedCondition s ↔ cyl t ⊆ cyl s := by
  rw [cohenCodedCondition_le_iff, cyl_subset_iff_prefix]
  rfl

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is a useful calibration point. Disjunctiveness is a topologically generic property: the set of disjunctive
    sequences is comeager in $\CantorSpace$, because for each word $u$ the union
    $\bigcup_{s\in D_u}\cyl{s}$ is dense open and there are only countably many $u$.
-/
theorem cohen_disjunctive_residual :
    {x : ℕ → Bool | ∀ u : CohenCondition, CohenOccursIn u x} ∈ residual (ℕ → Bool) := by
  have h : (⋂ u : CohenCondition, cylinderCode (cohenWordRequirement u)) ∈
      residual (ℕ → Bool) := by
    apply countable_iInter_mem.mpr
    intro u
    obtain ⟨ho, hd⟩ := cohen_dense_cylinderCode (cohenWordRequirement_dense u)
    exact residual_of_dense_open ho hd
  apply Filter.mem_of_superset h
  intro x hx u
  obtain ⟨s, hs, hxs⟩ := mem_cylinderCode.mp (Set.mem_iInter.mp hx u)
  exact cohen_occursIn_of_agrees hs ((cohenAgrees_iff_prefixOfSeq s x).mpr hxs)

/-- The graph entry expressing the value of one binary coordinate. -/
def cohenBitLabel (n : ℕ) (b : Bool) : ZFSet.{u} :=
  pair (natOrdinal n) (natOrdinal b.toNat)

/-- Membership forcing for the checked graph entry in the genuine union name. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The forcing relation matches the cylinder interpretation. If $s\in\finseq{2}$ and $n<|s|$, then
    $$s\forces \dot c(n)=s(n).$$
-/
def CohenForcesBit (s : CohenCondition) (n : ℕ) (b : Bool) : Prop :=
  cohenCodedCondition s ∈ atomic (cohenConditionSet.{u} Set.univ) false
    (check (cohenConditionSet Set.univ) (cohenBitLabel n b))
    (unionName (cohenConditionSet Set.univ))

lemma cohenBitLabel_mem_condition (s : CohenCondition) (n : ℕ) (hn : n < s.length) :
    cohenBitLabel.{u} n s[n] ∈ (cohenCodedCondition s).val := by
  exact pair_mem_wordGraph.mpr ⟨by simpa using hn, by simp⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The forcing relation matches the cylinder interpretation. If $s\in\finseq{2}$ and $n<|s|$, then
    $$s\forces \dot c(n)=s(n).$$
-/
theorem cohen_forces_known_bit (s : CohenCondition) (n : ℕ) (hn : n < s.length) :
    CohenForcesBit.{u} s n s[n] := by
  apply membership_of_witness
  refine ⟨check (cohenConditionSet Set.univ) (cohenBitLabel n s[n]),
    cohenCodedCondition s, ?_, le_rfl, equality_refl _ _ _⟩
  apply ZFSet.mem_range.mpr
  exact ⟨⟨⟨_, (cohenCodedCondition s).property⟩,
    ⟨_, cohenBitLabel_mem_condition s n hn⟩⟩, rfl⟩

/-- Directed graph conditions cannot put two different bits at one coordinate. -/
theorem cohen_union_value_excludes_opposite
    (G : Order.PFilter (Condition (cohenConditionSet.{u} Set.univ)))
    (s : CohenCondition) (hs : cohenCodedCondition s ∈ G)
    (n : ℕ) (hn : n < s.length) (b : Bool) (hb : s[n] ≠ b) :
    cohenBitLabel n b ∉ value (cohenConditionSet Set.univ) G
      (unionName (cohenConditionSet Set.univ)) := by
  have hg : ∃ p ∈ chosen (cohenConditionSet Set.univ) G,
      p ∈ cohenConditionSet Set.univ :=
    ⟨_, ⟨cohenCodedCondition s, hs, rfl⟩, (cohenCodedCondition s).property⟩
  change cohenBitLabel n b ∉ valuation _ _
  rw [valuation_unionName _ _ hg]
  intro h
  obtain ⟨p, hp, hbit⟩ := ZFSet.mem_sUnion.mp h
  obtain ⟨_, q, hq, rfl⟩ := ZFSet.mem_sep.mp hp
  obtain ⟨r, _, hrs, hrq⟩ := G.directed (cohenCodedCondition s) hs q hq
  have hknown := hrs (cohenBitLabel_mem_condition s n hn)
  have hother := hrq hbit
  obtain ⟨t, rfl⟩ := cohenCodedCondition_surjective r
  obtain ⟨hi, hiEq⟩ := pair_mem_wordGraph.mp hknown
  obtain ⟨hj, hjEq⟩ := pair_mem_wordGraph.mp hother
  exact hb (bool_toNat_injective (hiEq.symm.trans hjEq))

theorem cohen_not_forces_wrong_bit {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hc : M.toSet.Countable) (s : CohenCondition) (n : ℕ) (hn : n < s.length)
    (b : Bool) (hb : s[n] ≠ b)
    (hcheck : check (cohenConditionSet Set.univ) (cohenBitLabel n b) ∈ M)
    (hunion : unionName (cohenConditionSet Set.univ) ∈ M) :
    ¬ CohenForcesBit.{u} s n b := by
  intro hf
  obtain ⟨G, hsG, hG⟩ := exists_atomic_test_filter (cohenConditionSet Set.univ) M hc
    (cohenCodedCondition s)
  have hv := (atomic_truth (cohenConditionSet Set.univ) M hM G hG false _ _
    hcheck hunion (check_isName _ _) (unionName_isName _)).mp ⟨_, hsG, hf⟩
  have hg : ∃ p ∈ chosen (cohenConditionSet Set.univ) G,
      p ∈ cohenConditionSet Set.univ :=
    ⟨_, ⟨cohenCodedCondition s, hsG, rfl⟩, (cohenCodedCondition s).property⟩
  change valuation _ (check _ _) ∈ _ at hv
  rw [valuation_check _ _ hg] at hv
  exact cohen_union_value_excludes_opposite G s hsG n hn b hb hv

/-- Padding fixes no earlier coordinate, and either bit can then be appended. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $n\ge |s|$, neither value is forced by $s$, but first extend $s$ to a string $t$ of length $n$. The
    refinements $t\concat(0)$ and
    $t\concat(1)$ then force opposite values at coordinate $n$. In this sense \termuse{Cohen forcing} is the
    model-theoretic version of the product topology on
    $\CantorSpace$.
-/
theorem cohen_opposite_extensions (s : CohenCondition) (n : ℕ) (hn : s.length ≤ n) :
    ∃ t : CohenCondition, CohenStronger t s ∧ t.length = n ∧
      ∀ b : Bool, CohenStronger (t ++ [b]) s ∧ CohenForcesBit.{u} (t ++ [b]) n b := by
  let t := s ++ List.replicate (n - s.length) false
  have hst : s.IsPrefix t := List.prefix_append _ _
  have ht : t.length = n := by simp only [t, List.length_append, List.length_replicate]; omega
  refine ⟨t, hst, ht, fun b => ⟨hst.trans (List.prefix_append _ _), ?_⟩⟩
  have hnb : n < (t ++ [b]).length := by simp [ht]
  have heq : (t ++ [b])[n] = b := by simp [ht]
  simpa only [heq] using cohen_forces_known_bit.{u} (t ++ [b]) n hnb

theorem cohen_not_forces_unfixed_bit {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hc : M.toSet.Countable) (s : CohenCondition) (n : ℕ) (hn : s.length ≤ n)
    (b : Bool)
    (hcheck : check (cohenConditionSet Set.univ) (cohenBitLabel n b) ∈ M)
    (hunion : unionName (cohenConditionSet Set.univ) ∈ M) :
    ¬ CohenForcesBit.{u} s n b := by
  obtain ⟨t, _, ht, hext⟩ := cohen_opposite_extensions.{u} s n hn
  have hnb : n < (t ++ [!b]).length := by simp [ht]
  have heq : (t ++ [!b])[n] = !b := by simp [ht]
  have hne : (t ++ [!b])[n] ≠ b := by simp [heq]
  intro hf
  apply cohen_not_forces_wrong_bit hM hc (t ++ [!b]) n hnb b hne hcheck hunion
  exact atomic_lower _ false _ _
    ((cohenCodedCondition_le_iff s (t ++ [!b])).mpr (hext (!b)).1) hf

/-- All name-membership hypotheses follow from the ground model's axioms. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $n\ge |s|$, neither value is forced by $s$, but first extend $s$ to a string $t$ of length $n$. The
    refinements $t\concat(0)$ and
    $t\concat(1)$ then force opposite values at coordinate $n$. In this sense \termuse{Cohen forcing} is the
    model-theoretic version of the product topology on
    $\CantorSpace$.
-/
theorem cohen_not_forces_unfixed_bit_in_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hc : M.toSet.Countable)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (s : CohenCondition) (n : ℕ) (hn : s.length ≤ n) (b : Bool) :
    ¬ CohenForcesBit.{u} s n b := by
  have hP : cohenConditionSet.{u} Set.univ ∈ M := binaryWords_mem hM hinf hpair hunion hpower hsep
  have hω := omegaOrdinal_mem hM hinf (hsep _)
  have hnat (k : ℕ) : natOrdinal k ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨k, rfl⟩) hω
  have hbit : cohenBitLabel n b ∈ M := orderedPair_mem hM hpair (hnat n) (hnat b.toNat)
  exact cohen_not_forces_unfixed_bit hM hc s n hn b
    (check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨_, hP⟩ ⟨_, hbit⟩)
    (unionName_mem_ground hM hinf hpair hunion hpower hsep hrep ⟨_, hP⟩)

end PolishSpaceBook
