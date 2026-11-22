module

public import PolishSpaceBook.SetTheoryCountableCollapse
public import PolishSpaceBook.SetTheoryFiniteReflection
public import PolishSpaceBook.SetTheoryTransitiveModelDefinitions

@[expose] public section

/-! # Countable transitive seeds for fixed parameters

Iterate union starting with a set of parameters, then take the union of all
finite stages. Hereditary countability ensures each stage is countable. The
result includes the parameters themselves, as required to fix their values
under the Mostowski collapse.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Countability is external and transitivity and model truth are the usual
ones; no internal enumeration of the model is asserted. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In independence arguments one often takes $M$ to be a \termdefine{countable transitive model} from the ambient universe
    $V$.
-/
def IsCountableTransitiveSetModel (M : ZFSet.{u}) (T : membershipLanguage.Theory) : Prop :=
  Countable M ∧ IsTransitiveSetModel M T

/-- Finite membership depth below the parameter collection. -/
def parameterLayers (A : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => A
  | n + 1 => ZFSet.sUnion (parameterLayers A n)

def parameterSeed (A : ZFSet.{u}) : ZFSet.{u} := ZFSet.iUnion (parameterLayers A)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To preserve a parameter $a$, include $a$ and all its
    iterated members in the seed $T$
-/
theorem parameterSeed_contains (A : ZFSet.{u}) : A ⊆ parameterSeed A := by
  intro a ha
  exact ZFSet.mem_iUnion.mpr ⟨0, ha⟩

theorem parameterSeed_transitive (A : ZFSet.{u}) : (parameterSeed A).IsTransitive := by
  intro a ha b hb
  obtain ⟨n, hn⟩ := ZFSet.mem_iUnion.mp ha
  exact ZFSet.mem_iUnion.mpr ⟨n + 1, ZFSet.mem_sUnion.mpr ⟨a, hn, hb⟩⟩

theorem parameterSeed_subset {A M : ZFSet.{u}} (hM : M.IsTransitive) (hA : A ⊆ M) :
    parameterSeed A ⊆ M := by
  have h (n : ℕ) : parameterLayers A n ⊆ M := by
    induction n with
    | zero => exact hA
    | succ n ih =>
      intro b hb
      obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.mp hb
      exact hM.mem_trans hb (ih ha)
  intro a ha
  obtain ⟨n, hn⟩ := ZFSet.mem_iUnion.mp ha
  exact h n hn

/-- A countable union of countable sets, expressed for literal ZF sets. -/
theorem countable_sUnion (A : ZFSet.{u}) [Countable A]
    (h : ∀ a ∈ A, Countable a) : Countable (ZFSet.sUnion A) := by
  let : ∀ a : A, Countable a.val := fun a => h a.val a.property
  let f (p : Σ a : A, a.val) : ZFSet.sUnion A :=
    ⟨p.2.val, ZFSet.mem_sUnion.mpr ⟨p.1.val, p.1.property, p.2.property⟩⟩
  apply Function.Surjective.countable (f := f)
  intro b
  obtain ⟨a, ha, hba⟩ := ZFSet.mem_sUnion.mp b.property
  exact ⟨⟨⟨a, ha⟩, ⟨b.val, hba⟩⟩, rfl⟩

/-- Hereditary countability is the canonical recursive property on ZF sets. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A countable family of
    hereditarily countable parameters admits such a countable transitive seed.
-/
theorem parameterSeed_countable (A : ZFSet.{u}) [Countable A]
    (hA : ∀ a ∈ A, a.Hereditarily (fun x => Countable x)) : Countable (parameterSeed A) := by
  have hher (n : ℕ) : ∀ a ∈ parameterLayers A n,
      a.Hereditarily (fun x => Countable x) := by
    induction n with
    | zero => exact hA
    | succ n ih =>
      intro a ha
      obtain ⟨b, hb, hab⟩ := ZFSet.mem_sUnion.mp ha
      exact (ih b hb).mem hab
  have hcount (n : ℕ) : Countable (parameterLayers A n) := by
    induction n with
    | zero => exact inferInstanceAs (Countable A)
    | succ n ih =>
      let := ih
      exact countable_sUnion _ (fun a ha => (hher n a ha).self)
  let : ∀ n : ℕ, Countable (parameterLayers A n) := hcount
  let f (p : Σ n : ℕ, parameterLayers A n) : parameterSeed A :=
    ⟨p.2.val, ZFSet.mem_iUnion.mpr ⟨p.1, p.2.property⟩⟩
  apply Function.Surjective.countable (f := f)
  intro a
  obtain ⟨n, hn⟩ := ZFSet.mem_iUnion.mp a.property
  exact ⟨⟨n, ⟨a.val, hn⟩⟩, rfl⟩

/-- A countable family of hereditarily countable parameters is fixed literally,
not merely replaced by its collapsed images. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The countable-transitive convention is reached by starting from the reflected transitive set $V_\alpha$, then applying
    downward Löwenheim--Skolem from §{sec:appendix-logic} and the Mostowski collapse below. Parameters are handled with
    care: the collapse preserves actual parameters only when enough of their transitive closures is included in the
    elementary submodel; in general it carries them to their collapsed images.
-/
theorem exists_countable_transitive_model_fixed_parameters {V A : ZFSet.{u}}
    [Nonempty V] [Countable A] (hV : V.IsTransitive) (hAV : A ⊆ V)
    (hA : ∀ a ∈ A, a.Hereditarily (fun x => Countable x)) :
    ∃ M : ZFSet.{u}, M.IsTransitive ∧ Countable M ∧ A ⊆ M ∧
      ∀ φ : membershipLanguage.Sentence, M ⊨ φ ↔ V ⊨ φ := by
  let := parameterSeed_countable A hA
  obtain ⟨M, hM, hcount, hseed, hsentences⟩ := exists_countable_transitive_model hV
    (parameterSeed_transitive A) (parameterSeed_subset hV hAV)
  exact ⟨M, hM, hcount, (parameterSeed_contains A).trans hseed, hsentences⟩

/-- Reflection can be performed above the entire transitive seed before
applying the countable reduction. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a finite fragment, choose a nonempty $M_0=V_\alpha$ by reflection and apply this theorem, taking
    $T=\emptyset$ if no parameters need to be fixed.
-/
theorem finite_fragment_countable_model_with_seed
    (Φ : List membershipLanguage.Sentence) (hΦ : ∀ φ ∈ Φ, ZFSet.{u} ⊨ φ)
    (T : ZFSet.{u}) [Countable T] (hT : T.IsTransitive) :
    ∃ M : ZFSet.{u}, M.IsTransitive ∧ Countable M ∧ T ⊆ M ∧ ∀ φ ∈ Φ, M ⊨ φ := by
  obtain ⟨α, hTmem, hTV, hΦα⟩ := finite_true_sentences_reflect_parameters Φ hΦ T
  let : Nonempty (ZFSet.vonNeumann α) := ⟨⟨T, hTmem⟩⟩
  obtain ⟨M, hM, hcount, hTM, hsentences⟩ := exists_countable_transitive_model
    (ZFSet.isTransitive_vonNeumann α) hT hTV
  exact ⟨M, hM, hcount, hTM, fun φ hφ => (hsentences φ).mpr (hΦα φ hφ)⟩

theorem finite_fragment_countable_model_fixed_parameters
    (Φ : List membershipLanguage.Sentence) (hΦ : ∀ φ ∈ Φ, ZFSet.{u} ⊨ φ)
    (A : ZFSet.{u}) [Countable A]
    (hA : ∀ a ∈ A, a.Hereditarily (fun x => Countable x)) :
    ∃ M : ZFSet.{u}, M.IsTransitive ∧ Countable M ∧ A ⊆ M ∧ ∀ φ ∈ Φ, M ⊨ φ := by
  let := parameterSeed_countable A hA
  obtain ⟨M, hM, hcount, hTM, hs⟩ := finite_fragment_countable_model_with_seed Φ hΦ
    (parameterSeed A) (parameterSeed_transitive A)
  exact ⟨M, hM, hcount, (parameterSeed_contains A).trans hTM, hs⟩

end PolishSpaceBook.SetTheoryModels
