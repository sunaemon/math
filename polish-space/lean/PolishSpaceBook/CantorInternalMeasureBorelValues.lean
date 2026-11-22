module

public import PolishSpaceBook.CantorInternalMeasureClosedValues
public import PolishSpaceBook.CantorInternalMeasureCutCode

@[expose] public section

/-! # The model's Borel measure values from internal closed approximations -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ForcingFormulas ZFSet SetTheoryModels BorelExpression MeasureTheory
universe u

/-- Restrict the interpretation of a standard Baire-cylinder code to the binary points.
This keeps the original labels, including those whose cylinders have no binary points. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $c$ be a valid Borel code with its label graph in $M$. Write $A$ for its full external
    interpretation on Cantor space and $X=\BorelInterpretation{c}{M}$ for its internal interpretation there.
    For codes using the standard Baire-cylinder labels, this means first evaluating those same labels and
    then intersecting with $Y_M$. Labels whose cylinders have no binary points contribute the empty set.
    The internal interpretation construction and bounded Separation give $X\in M$.
-/
def internalBorelCantorSet (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child) : ZFSet.{u} :=
  internalInterpretation M c hw NamedLambda.NatListCode.decode [] ∩ internalCantor M

lemma cantorPointGraph_mem_internalBorelCantorSet (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalBorelCantorSet M c hw ↔
      cantorPointGraph x ∈ M ∧ x ∈ cantorSet c hw := by
  simp only [internalBorelCantorSet, ZFSet.mem_inter, cantorPointGraph_mem_internalCantor]
  change (pointGraph (cantorInclusion x) ∈ internalInterpretation M c hw _ [] ∧ _) ↔ _
  rw [pointGraph_mem_internalInterpretation]
  change ((_ ∧ x ∈ cantorSet c hw) ∧ _) ↔ _
  tauto

lemma internalLevelIntersection_subset_cantor (M : ZFSet.{u}) (T : Set (List Bool)) :
    internalLevelIntersection M T ⊆ internalCantor M := fun _ hx => (ZFSet.mem_sep.mp hx).1

/-- Only the point membership characterization is needed to transport an external lower bound. -/
lemma internal_closed_subset_of_points {M X : ZFSet.{u}} {A : Set (ℕ → Bool)}
    (hp : ∀ x, cantorPointGraph x ∈ X ↔ cantorPointGraph x ∈ M ∧ x ∈ A)
    (T : Set (List Bool)) (hT : treeBody T ⊆ A) : internalLevelIntersection M T ⊆ X := by
  intro g hg
  obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (internalLevelIntersection_subset_cantor M T hg)
  obtain ⟨hxM, hxT⟩ := (cantorPointGraph_mem_internalLevelIntersection M T x).mp hg
  exact (hp x).mpr ⟨hxM, hT hxT⟩

lemma internal_subset_complement_of_points {M X : ZFSet.{u}} {A : Set (ℕ → Bool)}
    (hX : X ⊆ internalCantor M)
    (hp : ∀ x, cantorPointGraph x ∈ X ↔ cantorPointGraph x ∈ M ∧ x ∈ A)
    (S : Set (List Bool)) (hS : treeBody S ⊆ Aᶜ) :
    X ⊆ internalCantor M \ internalLevelIntersection M S := by
  intro g hg
  refine ZFSet.mem_sdiff.mpr ⟨hX hg, ?_⟩
  obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (hX hg)
  intro hs
  exact hS ((cantorPointGraph_mem_internalLevelIntersection M S x).mp hs).2 ((hp x).mp hg).2

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hinf hpair hunion hpower hsep

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $c$ be a valid Borel code with its label graph in $M$. Write $A$ for its full external
    interpretation on Cantor space and $X=\BorelInterpretation{c}{M}$ for its internal interpretation there.
    For codes using the standard Baire-cylinder labels, this means first evaluating those same labels and
    then intersecting with $Y_M$. Labels whose cylinders have no binary points contribute the empty set.
    The internal interpretation construction and bounded Separation give $X\in M$.
-/
lemma internalBorelCantorSet_mem (c : BorelExpression) (hw : WellFounded c.Child)
    (hcM : c.labelGraph ∈ M) : internalBorelCantorSet M c hw ∈ M := by
  have hA := borelMeasureCutValues_mem hM hinf hpair hunion hpower hsep c hw hcM 0 1 (5 : Fin 10)
  let Y : M := ⟨_, internalCantor_mem hM hinf hpair hunion hpower hsep⟩
  exact (BoundedSetPredicate.member (1 : Fin 2) 0).separation_mem hM (hsep _) ![Y] hA

/-- The squeeze uses only closed values and finite measure laws; no external measure on old points. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Squeezing internal values by closed approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Given $\varepsilon>0$, choose entire codes $W_T,W_O\in M$ such that
    $$\TreeBody{T}\IncludedIn A\IncludedIn U(O),\qquad
    \mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon.$$
    Here $T$ is downward closed and $U(O)$ is the open set coded by $O$.
    The avoidance construction in §{sec:internal-finite-measure-bounds} gives a downward-closed tree $S$
    with $W_S\in M$ and $\TreeBody{S}=U(O)^c$. Restricting the two inclusions to internal points gives
    $$\InternalTreeBody{M}{T}\IncludedIn X
    \IncludedIn\SetDifference{Y_M}{\InternalTreeBody{M}{S}}.$$
    Monotonicity, the complement formula, and the closed-value identities yield
    $$\mu(\TreeBody{T})\le\nu(X)\le1-\mu(\TreeBody{S})=\mu(U(O)).$$
    The external value $\mu(A)$ lies in the same interval, whose length is
    $\mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon$.
    Since $\varepsilon$ is arbitrary, the two values coincide.
-/
theorem value_eq_of_internal_approximations {D R F X : ZFSet.{u}}
    (h : FiniteAdditiveCutGraph D R F) {A : Set (ℕ → Bool)}
    (hX : X ∈ D) (hY : internalCantor M ∈ D) (hunit : h.value (internalCantor M) = 1)
    (hXY : X ⊆ internalCantor M)
    (hp : ∀ x, cantorPointGraph x ∈ X ↔ cantorPointGraph x ∈ M ∧ x ∈ A)
    (happrox : InternallyApproximable M A)
    (hclosed : ∀ T : Set (List Bool), IsSubtree T → wordTreeSet (binaryLift T) ∈ M →
      internalLevelIntersection M T ∈ D ∧ h.value (internalLevelIntersection M T) = fairCoinProduct.real (treeBody T)) :
    h.value X = fairCoinProduct.real A := by
  have bounds (ε : ℝ) (hε : 0 < ε) :
      h.value X < fairCoinProduct.real A + ε ∧ fairCoinProduct.real A < h.value X + ε := by
    obtain ⟨T, O, hT, hTM, hOM, hTA, hAO, hgap⟩ := happrox ε hε
    let S := avoidWords O
    have hSM := avoidWords_mem hM hinf hpair hunion hpower hsep O hOM
    obtain ⟨hTD, hvT⟩ := hclosed T hT hTM
    obtain ⟨hSD, hvS⟩ := hclosed S (avoidWords_isSubtree O) hSM
    have hlo := h.value_mono hTD hX (internal_closed_subset_of_points hp T hTA)
    have hSC : treeBody S ⊆ Aᶜ := by
      rw [show treeBody S = (openFromWords O)ᶜ from treeBody_avoidWords O]
      exact Set.compl_subset_compl.mpr hAO
    have hup := h.value_mono hX (h.diff_mem _ hY _ hSD)
      (internal_subset_complement_of_points hXY hp S hSC)
    rw [h.value_complement hY hSD (internalLevelIntersection_subset_cantor M S) hunit, hvS] at hup
    rw [hvT] at hlo
    have hOpen : IsOpen (openFromWords O) := isOpen_iUnion (fun s => isOpen_iUnion (fun _ => isOpen_cyl s))
    have hc := measureReal_add_measureReal_compl (μ := fairCoinProduct) hOpen.measurableSet
    simp only [probReal_univ] at hc
    rw [show treeBody S = (openFromWords O)ᶜ from treeBody_avoidWords O] at hup
    rw [measureReal_sdiff (hTA.trans hAO) (isClosed_treeBody T).measurableSet] at hgap
    have hmlo := measureReal_mono (μ := fairCoinProduct) hTA
    have hmup := measureReal_mono (μ := fairCoinProduct) hAO
    constructor <;> linarith
  apply le_antisymm
  · by_contra hn
    have hh := (bounds _ (sub_pos.mpr (lt_of_not_ge hn))).1
    linarith
  · by_contra hn
    have hh := (bounds _ (sub_pos.mpr (lt_of_not_ge hn))).2
    linarith

variable
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)

include hrep hchoice

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (hca : h.ModelsCountableAdditivity M)
    (hY : internalCantor M ∈ D) (hunit : h.value (internalCantor M) = 1)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hA : internalBorelCantorSet M c hc.2.2.2.2.2 ∈ D)

include hca hY hunit hcyl hcM hA

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Identification of the internal Borel measure
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The internal interpretation has the point-membership characterization required by the lemma.
    §{sec:internal-approximation-errors} supplies the two-sided approximation codes, including their
    external inclusions; their construction uses the inclusion transfer in §{sec:internal-closed-inclusions}.
    §{sec:internal-finite-measure-laws} supplies the closed-value identities from the measure axioms.
    The lemma therefore identifies the decoded value. Validity of $\MeasureValueCode{F}{X}$ and the
    encoding-decoding identity in §{sec:internal-borel-measure-cut} identify the whole code.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For an arbitrary $\varepsilon>0$, the internal approximation theorem in
    §{sec:internal-approximation-errors} supplies closed trees $T,S$ whose entire codes lie in $M$, with
    $$\TreeBody{T}\IncludedIn A\IncludedIn\TreeBody{S}^c,\qquad
    1-\mu(\TreeBody{S})-\mu(\TreeBody{T})<\varepsilon.$$
    The construction includes the transfer of the coded inclusions to all external points from
    §{sec:internal-closed-inclusions}.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Uniqueness of fraction-cut coding identifies the whole code, as detailed in
    §{sec:internal-borel-measure-identification}. Apply the same argument in $N$.
    The common code is empty exactly when its decoded value is zero.
-/
theorem countableMeasure_value_borel :
    h.value (internalBorelCantorSet M c hc.2.2.2.2.2) = fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  apply value_eq_of_internal_approximations hM hinf hpair hunion hpower hsep h hA hY hunit
    (fun _ hx => (ZFSet.mem_inter.mp hx).2) (cantorPointGraph_mem_internalBorelCantorSet M c _)
    (internallyApproximable_cantorSet hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM)
  exact countableMeasure_closed_values hM hinf hpair hunion hpower hsep hrep h hca hcyl

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Identification of the internal Borel measure
-/
theorem countableMeasure_code_borel :
    h.code (internalBorelCantorSet M c hc.2.2.2.2.2) =
      nonnegativeRealCutCode (fairCoinProduct.real (cantorSet c hc.2.2.2.2.2)) := by
  calc
    _ = nonnegativeRealCutCode (h.value (internalBorelCantorSet M c hc.2.2.2.2.2)) := (h.code_valid hA).encode_decode
    _ = _ := congrArg nonnegativeRealCutCode
      (countableMeasure_value_borel hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl c hc hcM hA)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: corollary
  title: The usual measure has the internal rational cut
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The lower-cut theorem makes the left side equivalent to $a/b<\mu(A)$.
    Substitute the value identity just proved. Thus the rational-cut definition and the value supplied by
    the model's measure graph agree, including the case of measure zero.
-/
theorem countableMeasure_lower_cut (a b : ℕ) (hb : 0 < b) (ps : Fin 10 → M)
    (hp : Subtype.val ∘ ps = borelMeasureCutValues M c hc.2.2.2.2.2 a b) :
    borelMeasureLowerCutFormula.Realize Empty.elim ps ↔
      (a : ℝ) / b < h.value (internalBorelCantorSet M c hc.2.2.2.2.2) := by
  rw [countableMeasure_value_borel hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl c hc hcM hA]
  exact realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM a b hb ps hp

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Absoluteness of coded Borel measure
-/
theorem countableMeasure_null_iff :
    h.value (internalBorelCantorSet M c hc.2.2.2.2.2) = 0 ↔
      fairCoinProduct (cantorSet c hc.2.2.2.2.2) = 0 := by
  rw [countableMeasure_value_borel hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl c hc hcM hA,
    measureReal_eq_zero_iff]

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Absoluteness of coded Borel measure
-/
theorem countableMeasure_code_empty_iff :
    h.code (internalBorelCantorSet M c hc.2.2.2.2.2) = ∅ ↔
      fairCoinProduct (cantorSet c hc.2.2.2.2.2) = 0 := by
  rw [countableMeasure_code_borel hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl c hc hcM hA,
    ← nonnegativeRealCutCode_zero, ← measureReal_eq_zero_iff]
  exact ⟨fun he => nonnegativeRealCutCode_injOn measureReal_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) he,
    fun he => congrArg nonnegativeRealCutCode he⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: theorem
  title: Absoluteness of coded Borel measure
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The measure comparison can now be made at the level of entire real codes. Let $M$ and $N$ be transitive
    models of ZFC containing the same externally valid Borel code $c$. Write $A$ for its full external
    Cantor-space interpretation and $F_M,F_N$ for the models' usual fair-coin probability measure graphs,
    using the fraction-cut representation of real values from §{sec:internal-borel-measure-cut}.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    This compares the measures of the two interpretations of a shared code. It does not assign external
    probability measure to the set of old points. In particular, the result applies to a transitive forcing
    extension $N=M[G]$ without asserting that the two interpretations have the same elements.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, both models contain the same entire fraction-cut code.
-/
theorem countableMeasure_code_borel_agreement {N D' R' F' : ZFSet.{u}} (hN : N.IsTransitive)
    (hinfN : N ⊨ infinitySentence) (hpairN : N ⊨ pairingSentence)
    (hunionN : N ⊨ unionSentence) (hpowerN : N ⊨ powerSentence)
    (hsepN : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), N ⊨ separationSentence φ)
    (hrepN : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), N ⊨ replacementSentence φ)
    (hchoiceN : N ⊨ choiceSentence) (h' : FiniteAdditiveCutGraph D' R' F')
    (hcaN : h'.ModelsCountableAdditivity N)
    (hY' : internalCantor N ∈ D') (hunit' : h'.value (internalCantor N) = 1)
    (hcyl' : ∀ s : List Bool, internalWordCylinder N s ∈ D' ∧
      pair (internalWordCylinder N s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F')
    (hcN : c.labelGraph ∈ N) (hA' : internalBorelCantorSet N c hc.2.2.2.2.2 ∈ D') :
    h.code (internalBorelCantorSet M c hc.2.2.2.2.2) = h'.code (internalBorelCantorSet N c hc.2.2.2.2.2) := by
  rw [countableMeasure_code_borel hM hinf hpair hunion hpower hsep hrep hchoice h hca hY hunit hcyl c hc hcM hA,
    countableMeasure_code_borel hN hinfN hpairN hunionN hpowerN hsepN hrepN hchoiceN h' hcaN hY' hunit' hcyl' c hc hcN hA']

end PolishSpaceBook.CantorTreeMeasure
