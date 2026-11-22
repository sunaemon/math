module

public import PolishSpaceBook.SetTheoryAbstractIteration

@[expose] public section

/-! # Definable recursion on internal omega from actual Replacement -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

/-- Replacement collects the uniquely defined finite sequence graphs, and
Union glues them. Agreement was proved using internal formula induction. -/
theorem omega_iteration_exists (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) {p : ℕ} (φ : ForcingFormulas.Formula (p + 2))
    (ps : Fin p → M) (s : M)
    (hφ : ∀ a : M, ∃! b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃ f : M, (iterationBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps s) W) f) := by
  let R := fun a b : M => φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)
  have hR : ∀ a b c : M, R a b → R a c → b = c := by
    intro a b c hb hc
    obtain ⟨d, _, hd⟩ := hφ a
    exact (hd b hb).trans (hd c hc).symm
  have hfinite := finite_iteration_existsUnique hM hW φ ps s hφ
  obtain ⟨F, hF⟩ := (realize_replacement M (iterationBody φ)).mp
    (hM.realize_of_mem _ (ZFCAxiom.replacement _)) (Fin.snoc ps s) W hfinite
  obtain ⟨H, hH⟩ := (models_union_iff M).mp (hM.realize_of_mem _ ZFCAxiom.union) F
  have hFs (f : M) : member f F ↔ ∃ n : M, member n W ∧ IsIteration R s n f := by
    simpa only [realize_iterationBody] using hF f
  have happ (k a : M) : GraphApplication H k a ↔
      ∃ n f : M, member n W ∧ IsIteration R s n f ∧ GraphApplication f k a := by
    constructor
    · rintro ⟨q, hq, hqH⟩
      obtain ⟨f, hqf, hfF⟩ := (hH q).mp hqH
      obtain ⟨n, hn, hf⟩ := (hFs f).mp hfF
      exact ⟨n, f, hn, hf, q, hq, hqf⟩
    · rintro ⟨n, f, hn, hf, q, hq, hqf⟩
      exact ⟨q, hq, (hH q).mpr ⟨f, hqf, (hFs f).mpr ⟨n, hn, hf⟩⟩⟩
  have hWtrans := leastInductiveObject_transitive hM hW
  have hmemtrans := leastInductiveObject_members_transitive hM hW
  have hfunction : IsFunctionGraph H := by
    constructor
    · intro q hq
      obtain ⟨f, hqf, hfF⟩ := (hH q).mp hq
      obtain ⟨n, _, hf⟩ := (hFs f).mp hfF
      exact hf.1.1.1 q hqf
    · intro k a b ha hb
      obtain ⟨n, f, hn, hf, hfa⟩ := (happ k a).mp ha
      obtain ⟨m, g, hm, hg, hgb⟩ := (happ k b).mp hb
      exact iterations_agree hM hW hR hn hm hf hg k a b hfa hgb
  have hdomain : ∀ k : M, (∃ a : M, GraphApplication H k a) ↔ member k W := by
    intro k
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨n, f, hn, hf, hfa⟩ := (happ k a).mp ha
      exact hWtrans n hn k ((hf.1.2 k).mp ⟨a, hfa⟩)
    · intro hk
      obtain ⟨n, hn, hkn⟩ := hW.1.2 k hk
      obtain ⟨f, hf, _⟩ := hfinite n hn
      have hf' := (realize_iterationBody φ ps s n f).mp hf
      obtain ⟨a, ha⟩ := (hf'.1.2 k).mpr ((hkn k).mpr (Or.inr rfl))
      exact ⟨a, (happ k a).mpr ⟨n, f, hn, hf', ha⟩⟩
  refine ⟨H, (realize_iterationBody φ ps s W H).mpr ⟨⟨hfunction, hdomain⟩, ?_, ?_⟩⟩
  · intro e heW he
    obtain ⟨n, hn, hen⟩ := hW.1.2 e heW
    obtain ⟨f, hf, _⟩ := hfinite n hn
    have hf' := (realize_iterationBody φ ps s n f).mp hf
    exact (happ e s).mpr ⟨n, f, hn, hf', hf'.2.1 e ((hen e).mpr (Or.inr rfl)) he⟩
  · intro k l a b _ hkl hka hlb
    obtain ⟨n, f, hn, hf, hfa⟩ := (happ k a).mp hka
    obtain ⟨m, g, hm, hg, hgb⟩ := (happ l b).mp hlb
    have hlm := (hg.1.2 l).mp ⟨b, hgb⟩
    have hkm := hmemtrans m hm l hlm k ((hkl k).mpr (Or.inr rfl))
    obtain ⟨c, hgc⟩ := (hg.1.2 k).mpr hkm
    have hac := iterations_agree hM hW hR hn hm hf hg k a c hfa hgc
    subst c
    exact hg.2.2 k l a b hlm hkl hgc hgb

end PolishSpaceBook.SetTheoryModels.AbstractMembership
