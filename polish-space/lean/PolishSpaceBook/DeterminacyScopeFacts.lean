module

public import PolishSpaceBook.UndeterminedGame
public import PolishSpaceBook.BorelDeterminacy
public import PolishSpaceBook.LusinScopeFacts
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

@[expose] public section

namespace PolishSpaceBook
open Set Function MeasureTheory MeasurableSpace
universe u v

/-- The quoted Borel-determinacy theorem excludes Borelness of the actual
payoff constructed by transfinite diagonalization. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The theorem in §{sec:martin-borel-det} says that every Borel payoff is determined. The following construction
    therefore produces a non-Borel payoff; its use of Choice is essential to the diagonalization.
-/
theorem undetermined_payoff_not_borel :
    ¬ MeasurableSet UndeterminedGame.payoff := by
  intro hB
  exact UndeterminedGame.payoff_not_determined (baire_borel_determined hB)

/-- AD asserts determinacy for every Baire-space payoff. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The assertion covering all real payoffs is the \termdefineas{Axiom of Determinacy}{Axiom of Determinacy (AD)}: every
    $A \IncludedIn \BaireSpace$ is determined.
-/
def AxiomOfDeterminacy : Prop := ∀ A : Set (ℕ → ℕ), BaireDetermined A

/-- Lean's ambient classical Choice supports the book's actual diagonal
construction, so that AD is incompatible with that ambient theory. This does
not assert an internal consistency theorem about a coded model of ZF. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **AD contradicts AC.** The construction of a non-determined payoff set in §{sec:determinacy} uses Choice to well-order
    all strategies and diagonalize against them. Hence AD cannot be added to ZFC.
-/
theorem not_axiomOfDeterminacy : ¬ AxiomOfDeterminacy := by
  intro hAD
  exact UndeterminedGame.payoff_not_determined (hAD UndeterminedGame.payoff)

/-- Countable Borel separators give an injection into Cantor space, and
Lusin--Suslin makes it a Borel embedding with Borel range. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard Borel classification transfers the finite-measure statement
    from Cantor space to arbitrary standard Borel spaces: use a Borel embedding and extend the transported measure
    by zero outside its image.
-/
theorem exists_standardBorel_cantor_embedding
    (X : Type u) [MeasurableSpace X] [StandardBorelSpace X] :
    ∃ e : X → (ℕ → Bool), MeasurableEmbedding e := by
  obtain ⟨e, he, hi⟩ := measurable_injection_nat_bool_of_countablySeparated X
  exact ⟨e, measurable_injection_embedding he hi⟩

/-- The pushforward along a Borel embedding is the transported measure
extended by zero outside the Borel image. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard Borel classification transfers the finite-measure statement
    from Cantor space to arbitrary standard Borel spaces: use a Borel embedding and extend the transported measure
    by zero outside its image.
-/
theorem embedding_pushforward_zero_outside
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → Y} (he : MeasurableEmbedding e) (μ : Measure X) :
    μ.map e (range e)ᶜ = 0 := by
  rw [Measure.map_apply he.measurable he.measurableSet_range.compl]
  simp

/-- Pull a completed-measurable image back along the actual measure transport.
No measurability of the original set is assumed. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard Borel classification transfers the finite-measure statement
    from Cantor space to arbitrary standard Borel spaces: use a Borel embedding and extend the transported measure
    by zero outside its image.
-/
theorem nullMeasurable_of_embedding_image
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → Y} (he : MeasurableEmbedding e) (μ : Measure X) {A : Set X}
    (hA : NullMeasurableSet (e '' A) (μ.map e)) : NullMeasurableSet A μ := by
  have hp := hA.preimage (he.measurable.quasiMeasurePreserving μ)
  rwa [he.injective.preimage_image] at hp

/-- Universal completion measurability of the Cantor image implies the
finite-measure assertion on the original standard Borel space. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard Borel classification transfers the finite-measure statement
    from Cantor space to arbitrary standard Borel spaces: use a Borel embedding and extend the transported measure
    by zero outside its image.
-/
theorem finite_completion_transfer_of_cantor_embedding
    {X : Type u} [MeasurableSpace X] {e : X → (ℕ → Bool)}
    (he : MeasurableEmbedding e) {A : Set X}
    (himage : ∀ ν : Measure (ℕ → Bool), IsFiniteMeasure ν →
      NullMeasurableSet (e '' A) ν) (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ := by
  exact nullMeasurable_of_embedding_image he μ (himage (μ.map e) inferInstance)

/-- A sigma-finite measure is exhausted by countably many measurable sets of
finite measure; completion measurability on the restrictions patches by union. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A countable exhaustion handles sigma-finite measures, including Lebesgue measure.
-/
theorem sigmaFinite_completion_of_finite_tests
    {X : Type u} [MeasurableSpace X] {A : Set X}
    (hfinite : ∀ ν : Measure X, IsFiniteMeasure ν → NullMeasurableSet A ν)
    (μ : Measure X) [SigmaFinite μ] : NullMeasurableSet A μ := by
  have hpart : ∀ n, NullMeasurableSet (A ∩ spanningSets μ n) μ := by
    intro n
    let : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      ⟨by simpa using measure_spanningSets_lt_top μ n⟩
    exact (nullMeasurableSet_restrict (measurableSet_spanningSets μ n).nullMeasurableSet).mp
      (hfinite _ inferInstance)
  have h := NullMeasurableSet.iUnion hpart
  have heq : (⋃ n, A ∩ spanningSets μ n) = A := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rwa [heq] at h

end PolishSpaceBook
