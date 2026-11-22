module

public import PolishSpaceBook.LambdaRecursionTheorem

@[expose] public section

/-! # Numerical search with a certified result

The result function is evaluated only in a successful branch. This matters
when proving exact domains of partial applications, not just forward simulation.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

/-- Pointwise application of a total ternary numerical operation. -/
def numericalApply3 (B F G H : AlphaTerm) : AlphaTerm := lam 90
  (app (app (app B (app F (var 90))) (app G (var 90))) (app H (var 90)))

theorem NumericalComputes.apply3 {F G H B : AlphaTerm} {f g h : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) (hh : NumericalComputes H h)
    (hB : B.Closed) (b : ℕ → ℕ → ℕ → ℕ)
    (hb : ∀ i j k, Relation.ReflTransGen Beta
      (app (app (app B (numeral i)) (numeral j)) (numeral k)) (numeral (b i j k))) :
    NumericalComputes (numericalApply3 B F G H) (fun n => b (f n) (g n) (h n)) := by
  refine ⟨?_,fun n => ?_⟩
  · unfold numericalApply3 Closed
    simp only [fv_lam,fv_app,fv_var]
    rw [hB,hf.1,hg.1,hh.1]
    decide
  · have hs : Beta (app (numericalApply3 B F G H) (numeral n))
        (app (app (app B (app F (numeral n))) (app G (numeral n))) (app H (numeral n))) := by
      simpa only [numericalApply3,subst_app,subst_var,ite_true,
        subst_closed _ _ _ hB,subst_closed _ _ _ hf.1,
        subst_closed _ _ _ hg.1,subst_closed _ _ _ hh.1] using
        Beta.contract 90 (app (app (app B (app F (var 90))) (app G (var 90))) (app H (var 90))) (numeral n)
    exact (Relation.ReflTransGen.single hs).trans
      ((beta_steps_app (beta_steps_app (beta_steps_app_right B (hf.2 n)) (hg.2 n)) (hh.2 n)).trans
        (hb (f n) (g n) (h n)))

def numericalResultSearch (F G : AlphaTerm) : AlphaTerm :=
  lam 42 (app (app resultSearchTerm
    (app (curryNumerical (numericalCompose reverseZeroTerm F)) (var 42))) G)

theorem numericalResultSearch_closed {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) :
    (numericalResultSearch F G).Closed := by
  unfold numericalResultSearch Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [resultSearchTerm_closed,curryNumerical_closed (reverseZero_computes.comp hf).1,hg.1]
  decide

theorem numericalResultSearch_start {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) (n : ℕ) :
    Relation.ReflTransGen Beta (app (numericalResultSearch F G) (numeral n))
      (app (app resultSearchTerm
        (app (curryNumerical (numericalCompose reverseZeroTerm F)) (numeral n))) G) := by
  apply Relation.ReflTransGen.single
  simpa only [numericalResultSearch,subst_app,subst_var,ite_true,
    subst_closed _ _ _ resultSearchTerm_closed,subst_closed _ _ _ hg.1,
    subst_closed _ _ _ (curryNumerical_closed (reverseZero_computes.comp hf).1)] using
    Beta.contract 42 (app (app resultSearchTerm
      (app (curryNumerical (numericalCompose reverseZeroTerm F)) (var 42))) G) (numeral n)

theorem numericalResultSearch_hit {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g)
    (n j : ℕ) (hj : f (Nat.pair n j) ≠ 0) (hb : ∀ k < j, f (Nat.pair n k) = 0) :
    Relation.ReflTransGen Beta (app (numericalResultSearch F G) (numeral n)) (numeral (g j)) := by
  have ht := reverseZero_computes.comp hf
  have hs (k : ℕ) := (curryNumerical_apply ht.1 n k).trans (ht.2 (Nat.pair n k))
  apply (numericalResultSearch_start hf hg n).trans
  exact (resultSearchTerm_hit (closed_app (curryNumerical_closed ht.1) (numeral_closed n))
    hg.1 j (by simpa [hj] using hs j) (fun k hk => ⟨0,by simpa [hb k hk] using hs k⟩)).trans (hg.2 j)

/-- Exact output and domain when all successful certificates have the same result. -/
theorem numericalResultSearch_runs_iff {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hf : NumericalComputes F f) (hg : NumericalComputes G g) (n m : ℕ)
    (hunique : ∀ i j, f (Nat.pair n i) ≠ 0 → f (Nat.pair n j) ≠ 0 → g i = g j) :
    Relation.ReflTransGen Beta (app (numericalResultSearch F G) (numeral n)) (numeral m) ↔
      ∃ k, f (Nat.pair n k) ≠ 0 ∧ g k = m := by
  classical
  by_cases hex : ∃ k, f (Nat.pair n k) ≠ 0
  · have hj := Nat.find_spec hex
    have hr := numericalResultSearch_hit hf hg n (Nat.find hex) hj
      (fun k hk => not_ne_iff.mp (Nat.find_min hex hk))
    constructor
    · intro hm
      exact ⟨Nat.find hex,hj,numeral_output_unique hr hm⟩
    · rintro ⟨k,hk,hkm⟩
      rw [← hkm,← hunique (Nat.find hex) k hj hk]
      exact hr
  · have hz : ∀ k, f (Nat.pair n k) = 0 := by simpa using hex
    have ht := reverseZero_computes.comp hf
    have hs (k : ℕ) := (curryNumerical_apply ht.1 n k).trans (ht.2 (Nat.pair n k))
    have hno : ¬ Relation.ReflTransGen Beta
        (app (numericalResultSearch F G) (numeral n)) (numeral m) := by
      intro hm
      exact resultSearchTerm_no_output (closed_app (curryNumerical_closed ht.1) (numeral_closed n))
        hg.1 (fun k => ⟨0,by simpa [hz k] using hs k⟩) m
        (numeral_after_reduction (numericalResultSearch_start hf hg n) hm)
    exact iff_of_false hno (by rintro ⟨k,hk,_⟩; exact hk (hz k))

end PolishSpaceBook.NamedLambda.AlphaTerm
