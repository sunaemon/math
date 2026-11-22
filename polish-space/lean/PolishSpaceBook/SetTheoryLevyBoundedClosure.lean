module

public import PolishSpaceBook.SetTheoryLevyPrenex

@[expose] public section

/-! # Bounded quantifier closure at every finite Lévy level

The proof compresses genuine finite prefixes, then applies literal Collection.
No closure constructor is added to the hierarchy.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas

/-- A finite existential prefix can be compressed into one existential
quantifier. Pairing bounds successive witnesses, and the lower-level bounded
closure keeps the new matrix at its original level. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now induct simultaneously on the level for the two polarities. Level zero follows directly from the bounded
    syntax. Suppose both polarities at level $n$ are closed under bounded quantification. Any finite existential
    prefix with a $\Pi_n$ matrix can be compressed to one existential quantifier: replace two successive witnesses
    by a set containing both, and quantify the two witnesses boundedly over that set. Pairing gives the equivalence,
    and the induction hypothesis keeps the matrix in $\Pi_n$. A vacuous existential quantifier handles an empty
    prefix. Thus a $\Sigma_{n+1}$ formula can be written, up to ZFC-provable equivalence, as
    $\exists y\,\theta(x,y,\vec p)$ with $\theta\in\Pi_n$.
-/
theorem existentialPrefix_single {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (hb : ∀ {m : ℕ} {ψ : ForcingFormulas.Formula (m + 1)}, LevyPi k ψ →
      ∀ i : Fin m, LevyPi k (boundedExists i ψ))
    (h : ExistentialPrefix (fun {m} (ψ : ForcingFormulas.Formula m) => LevyPi k ψ) φ) :
    ∃ ψ : ForcingFormulas.Formula (n + 1), LevyPi k ψ ∧ ZFCFormulaEquivalent φ ψ.ex := by
  induction h with
  | @base n φ h =>
    exact ⟨renameParameters φ Fin.castSucc, LevyClass.renameParameters k h Fin.castSucc, zfc_dummy_existential φ⟩
  | @ex n φ _ ih =>
    obtain ⟨ψ, hψ, he⟩ := ih
    refine ⟨levyPairMatrix ψ, ?_, he.ex.trans (zfc_pair_existentials ψ)⟩
    exact hb (hb (LevyClass.renameParameters k hψ (liftParameterMap (levyInsertBound n))) (Fin.last n).castSucc) (Fin.last n)

theorem levySigma_single {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (hb : ∀ {m : ℕ} {ψ : ForcingFormulas.Formula (m + 1)}, LevyPi k ψ →
      ∀ i : Fin m, LevyPi k (boundedExists i ψ))
    (h : LevySigma (k + 1) φ) :
    ∃ ψ : ForcingFormulas.Formula (n + 1), LevyPi k ψ ∧ ZFCFormulaEquivalent φ ψ.ex := by
  obtain ⟨χ, hχ, he⟩ := h
  obtain ⟨ψ, hψ, heψ⟩ := existentialPrefix_single hb hχ
  exact ⟨ψ, hψ, he.trans heψ⟩

/-- Simultaneous induction supplies all positive levels. The zero case uses
only the original bounded syntax, and each successor uses the preceding level. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a bounded existential quantifier, interchange the two existential quantifiers:
    $$
    \exists x\in a\,\exists y\,\theta(x,y,\vec p)
    \quad\Longleftrightarrow\quad
    \exists y\,\exists x\in a\,\theta(x,y,\vec p).
    $$
    For a bounded universal quantifier, use the displayed Collection equivalence.
    In both cases the matrix following the new unbounded existential quantifier remains $\Pi_n$ by the induction
    hypothesis. This proves both closures for $\Sigma_{n+1}$. Negation interchanges the two polarities and the two
    bounded quantifiers, giving the closures for $\Pi_{n+1}$. Applying both results gives the closures for
    $\Delta_{n+1}$. Bound variables are renamed throughout to retain the original free parameters and to keep each
    bounding variable outside the scope of the quantifier it bounds.
-/
theorem levy_boundedQuantifiers_of_collection (hc : FullZFCCollectionSchema) (k : ℕ)
    {p : LevyPolarity} {n : ℕ} {φ : ForcingFormulas.Formula (n + 1)} (h : LevyClass p k φ) (i : Fin n) :
    LevyClass p k (boundedAll i φ) ∧ LevyClass p k (boundedExists i φ) := by
  induction k generalizing p n with
  | zero => exact ⟨IsDeltaZero.all i h, IsDeltaZero.exists i h⟩
  | succ k ih =>
    have hsAll {m : ℕ} {ψ : ForcingFormulas.Formula (m + 1)} (hψ : LevySigma (k + 1) ψ) (j : Fin m) :
        LevySigma (k + 1) (boundedAll j ψ) := by
      obtain ⟨χ, hχ, he⟩ := levySigma_single (fun h i => (ih h i).2) hψ
      have hr := LevyClass.renameParameters k hχ (liftParameterMap (levyInsertBound m))
      have hb := (ih hr (Fin.last m).castSucc).2
      have hm := (ih hb j.castSucc).1
      exact (LevySigma.of_prefix (.ex (.base hm))).of_equivalent
        ((he.boundedAll j).trans (zfc_boundedAll_ex_of_collection hc j χ))
    have hsEx {m : ℕ} {ψ : ForcingFormulas.Formula (m + 1)} (hψ : LevySigma (k + 1) ψ) (j : Fin m) :
        LevySigma (k + 1) (boundedExists j ψ) := by
      obtain ⟨χ, hχ, he⟩ := levySigma_single (fun h i => (ih h i).2) hψ
      have hr := LevyClass.renameParameters k hχ (levySwapLast m)
      have hm := (ih hr j.castSucc).2
      exact (LevySigma.of_prefix (.ex (.base hm))).of_equivalent
        ((he.boundedExists j).trans (zfc_boundedExists_ex j χ))
    cases p with
    | sigma => exact ⟨hsAll h i, hsEx h i⟩
    | pi =>
      exact ⟨(LevySigma.not (hsEx (LevyPi.not h) i)).of_equivalent (zfc_boundedAll_dual i φ),
        (LevySigma.not (hsAll (LevyPi.not h) i)).of_equivalent (zfc_boundedExists_dual i φ)⟩

theorem levyDelta_boundedQuantifiers_of_collection (hc : FullZFCCollectionSchema) (k : ℕ)
    {n : ℕ} {φ : ForcingFormulas.Formula (n + 1)} (h : LevyDelta k φ) (i : Fin n) :
    LevyDelta k (boundedAll i φ) ∧ LevyDelta k (boundedExists i φ) := by
  cases k with
  | zero => exact ⟨IsDeltaZero.all i h, IsDeltaZero.exists i h⟩
  | succ k =>
    have hs := levy_boundedQuantifiers_of_collection hc (k + 1) h.1 i
    have hp := levy_boundedQuantifiers_of_collection hc (k + 1) h.2 i
    exact ⟨⟨hs.1, hp.1⟩, ⟨hs.2, hp.2⟩⟩

end PolishSpaceBook.SetTheoryModels
