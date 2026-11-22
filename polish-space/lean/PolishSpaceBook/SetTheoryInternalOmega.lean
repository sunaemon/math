module

public import PolishSpaceBook.SetTheoryFiniteOrdinals

@[expose] public section

/-! # The actual natural-number set belongs to a transitive model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Transitivity turns the internal Infinity witness into an actual inductive set. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The Infinity axiom gives $I\in M$ that is internally inductive. Transitivity and Extensionality identify
    its internal empty set and successors with the actual empty set and successors. Thus
    $$\emptyset\in I,\qquad y\in I\ \Longrightarrow\ y\cup\{y\}\in I.$$
-/
lemma inductive_set_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) :
    ∃ I ∈ M, (∅ : ZFSet.{u}) ∈ I ∧ ∀ y ∈ I, insert y y ∈ I := by
  obtain ⟨I, ⟨e, heI, he⟩, hs⟩ := (models_infinity_iff M).mp hinf
  have heq : e.val = ∅ := by
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => False.elim (he ⟨z, hM.mem_trans hz e.property⟩ hz),
      fun hz => False.elim (ZFSet.notMem_empty _ hz)⟩
  refine ⟨I.val, I.property, heq ▸ heI, ?_⟩
  intro y hy
  have hyM := hM.mem_trans hy I.property
  obtain ⟨s, hsI, hs⟩ := hs ⟨y, hyM⟩ hy
  have heq : s.val = insert y y := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases (hs ⟨z, hM.mem_trans hz s.property⟩).mp hz with hzy | he
      · exact Or.inr hzy
      · exact Or.inl (congrArg Subtype.val he)
    · rintro (rfl | hzy)
      · exact (hs ⟨_, hyM⟩).mpr (Or.inr rfl)
      · exact (hs ⟨z, hM.mem_trans hzy hyM⟩).mpr (Or.inl hzy)
  exact heq ▸ hsI

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Ordinary induction gives $\omega\IncludedIn I$.
-/
lemma omegaOrdinal_subset_inductive {I : ZFSet.{u}} (hzero : (∅ : ZFSet.{u}) ∈ I)
    (hsucc : ∀ y ∈ I, insert y y ∈ I) : Ordinal.omega0.toZFSet ⊆ I := by
  intro z hz
  obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hz
  clear hz
  induction n with
  | zero => simpa only [natOrdinal_zero] using hzero
  | succ n ih => simpa only [natOrdinal_succ] using hsucc (natOrdinal n) ih

/-- Bounded Separation inside an inductive set constructs the external ω in M. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Separation inside $I$ gives
    $$\{y\in I:M\models\mathrm{FinOrd}(y)\}=\omega\in M.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Natural numbers in a transitive model
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The earlier natural-number lemma gives the actual set $\omega\in M$.
-/
theorem omegaOrdinal_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence)
    (hsep : M ⊨ separationSentence (finiteOrdinalFormula (0 : Fin 1))) :
    Ordinal.omega0.toZFSet ∈ M := by
  obtain ⟨I, hI, hzero, hsucc⟩ := inductive_set_mem hM hinf
  have hsub := omegaOrdinal_subset_inductive hzero hsucc
  have habs (z : M) :
      (finiteOrdinalFormula (0 : Fin 1)).Realize Empty.elim (Fin.snoc Fin.elim0 z) ↔
        z.val ∈ Ordinal.omega0.toZFSet := by
    exact realize_finiteOrdinalFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h)
      (0 : Fin 1) (Fin.snoc Fin.elim0 z)
  have hS := separation_mem_of_absolute hM (finiteOrdinalFormula (0 : Fin 1)) hsep Fin.elim0 hI
    (fun z => z ∈ Ordinal.omega0.toZFSet) (fun z _ => habs z)
  have he : I.sep (fun z => z ∈ Ordinal.omega0.toZFSet) = Ordinal.omega0.toZFSet := by
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => (ZFSet.mem_sep.mp hz).2, fun hz => ZFSet.mem_sep.mpr ⟨hsub hz, hz⟩⟩
  exact he ▸ hS

end PolishSpaceBook.SetTheoryModels
