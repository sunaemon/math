module

public import PolishSpaceBook.LambdaEffectiveOpenSets
public import PolishSpaceBook.LambdaCauchyDomain
public import PolishSpaceBook.LambdaBaireQuantifiers

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaTree

/-- Lightface closed subsets of Baire space use a closed lambda semidecider
for their complements. -/
def LambdaPi01 (C : Set (ℕ → ℕ)) : Prop := LambdaSigma01 Cᶜ

/-- Every finite trial has a total decision bit, uniformly in the input name.
The fixed parameter remains paired with the point; this test ignores its left component. -/
theorem finiteTrial_zero_decides (e : ℕ) :
    ∃ Q : AlphaTerm, ∀ (ε x : ℕ → ℕ),
      LambdaRelative.Decides (pairBaire ε x) Q (fun k : ℕ => Term.finiteTrial x e 0 k = 0) := by
  let R := mapOutputProgram (numericalProjectionTerm false) identityProgram
  have hR : R.Closed := mapOutputProgram_closed (projection_computes false).1 identityProgram_closed
  have hr (ε x : ℕ → ℕ) (k : ℕ) : OracleRuns (pairBaire ε x) R k (x k) := by
    simpa [R, pairBaire] using
      mapOutputProgram_runs (projection_computes false).1 identityProgram_closed
        (identityProgram_runs (pairBaire ε x) k) ((projection_computes false).2 (pairBaire ε x k))
  let T := compositionProgram (semidecisionNameProgram e) R
  have hT : T.Closed := compositionProgram_closed (semidecisionNameProgram_closed e) hR
  have ht (ε x : ℕ → ℕ) (k : ℕ) : OracleRuns (pairBaire ε x) T k (Term.finiteTrial x e 0 k) :=
    compositionProgram_runs (semidecisionNameProgram_closed e) hR
      (semidecisionNameProgram_runs x e k) (hr ε x)
  refine ⟨mapOutputProgram reverseZeroTerm T, fun ε x => ⟨mapOutputProgram_closed reverseZero_computes.1 hT,
    fun k => ⟨?_, ?_⟩⟩⟩
  · intro hk
    simpa only [Encodable.encode_nat, hk, ite_true] using
      mapOutputProgram_runs reverseZero_computes.1 hT (ht ε x k)
        (reverseZero_computes.2 (Term.finiteTrial x e 0 k))
  · intro hk
    simpa only [Encodable.encode_nat, hk, ite_false] using
      mapOutputProgram_runs reverseZero_computes.1 hT (ht ε x k)
        (reverseZero_computes.2 (Term.finiteTrial x e 0 k))

/-- Co-semidecision becomes a universal numerical test, hence a lambda pair tree.
No witnesses or new oracle are selected effectively. -/
theorem LambdaPi01.projected {C : Set (ℕ → ℕ)} (hC : LambdaPi01 C) (ε : ℕ → ℕ) :
    Projected ε C := by
  obtain ⟨P, hP, hc⟩ := hC
  obtain ⟨e, he⟩ := Term.closedProgram_surjective P hP
  obtain ⟨Q, hQ⟩ := finiteTrial_zero_decides e
  have hp := projected_forall_baire (ε := ε) (hQ ε)
  have hevent (x : ℕ → ℕ) : (∃ k, Term.finiteTrial x e 0 k ≠ 0) ↔ x ∉ C := by
    rw [finiteTrial_positive_iff, he]
    exact hc ⟨x, mem_univ _⟩
  convert hp using 1
  ext x
  constructor
  · intro hx k
    by_contra hk
    exact (hevent x |>.mp ⟨k, hk⟩) hx
  · intro hall
    by_contra hx
    obtain ⟨k, hk⟩ := (hevent x).mpr hx
    exact hk (hall k)

/-- Effective analyticity is relative to the valid-name domain. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    This matches the lightface hierarchy of §{sec:effective-dst}. A subset $E\IncludedIn X$ is
    \termdefineas{effective analytic set}{effectively analytic} when
    $$
    \rho_X^{-1}(E)=\DomainOf{\rho_X}\cap W
    $$
    for some lightface $\lSigma^1_1$ set $W\IncludedIn\BaireSpace$. Since $\DomainOf{\rho_X}$ is lightface
    $\lPi^0_1$, this preimage is itself lightface $\lSigma^1_1$; the analogous simplification fails for effective openness.
-/
def LambdaEffectivelyAnalytic {X : Type*} (δ : Representation X) (A : Set X) : Prop :=
  ∃ W, Projected (fun _ => 0) W ∧ δ.namePreimage A = δ.domain ∩ W

/-- For a projected name domain, restriction preserves the same lightface class. -/
theorem lambdaEffectivelyAnalytic_iff_projected_namePreimage {X : Type*}
    (δ : Representation X) (hδ : Projected (fun _ => 0) δ.domain) (A : Set X) :
    LambdaEffectivelyAnalytic δ A ↔ Projected (fun _ => 0) (δ.namePreimage A) := by
  constructor
  · rintro ⟨W, hW, hA⟩
    rw [hA]
    exact hδ.inter hW
  · intro hA
    refine ⟨δ.namePreimage A, hA, ?_⟩
    ext p
    exact ⟨fun h => ⟨h.choose, h⟩, fun h => h.2⟩

namespace LambdaMetricApproximation
variable {X : Type*} [MetricSpace X] {q : ℕ → X}

theorem cauchyDomain_lambdaPi01 (A : LambdaMetricApproximation q) :
    LambdaPi01 (cauchyNameDomain q) := A.semidecidable_invalid_names

theorem cauchyDomain_projected (A : LambdaMetricApproximation q) (ε : ℕ → ℕ) :
    Projected ε (cauchyNameDomain q) := A.cauchyDomain_lambdaPi01.projected ε

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    This matches the lightface hierarchy of §{sec:effective-dst}. A subset $E\IncludedIn X$ is
    \termdefineas{effective analytic set}{effectively analytic} when
    $$
    \rho_X^{-1}(E)=\DomainOf{\rho_X}\cap W
    $$
    for some lightface $\lSigma^1_1$ set $W\IncludedIn\BaireSpace$. Since $\DomainOf{\rho_X}$ is lightface
    $\lPi^0_1$, this preimage is itself lightface $\lSigma^1_1$; the analogous simplification fails for effective openness.
-/
theorem effectivelyAnalytic_iff_namePreimage [CompleteSpace X]
    (A : LambdaMetricApproximation q) (hq : DenseRange q) (S : Set X) :
    LambdaEffectivelyAnalytic (cauchyRepresentationObject q hq) S ↔
      Projected (fun _ => 0) ((cauchyRepresentationObject q hq).namePreimage S) :=
  lambdaEffectivelyAnalytic_iff_projected_namePreimage _ (A.cauchyDomain_projected _) S

end LambdaMetricApproximation
end PolishSpaceBook
