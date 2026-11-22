module

public import PolishSpaceBook.LambdaEnumeratedBallSemidecision
public import PolishSpaceBook.RepresentedBaireSpace
public import PolishSpaceBook.LambdaRealMetric
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- The full Baire-space preimage, retaining membership in the name domain. -/
def Representation.namePreimage {X : Type*} (δ : Representation X) (U : Set X) :
    Set (ℕ → ℕ) :=
  {p | ∃ hp : p ∈ δ.domain, δ.toFun ⟨p, hp⟩ ∈ U}

/-- Lightface open subsets of Baire space, given by a closed lambda semidecider. -/
def LambdaSigma01 (V : Set (ℕ → ℕ)) : Prop :=
  SemidecidableFromNames baireIdentityRepresentation V

/-- Effective openness is relative to valid names, without an extension of the representation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For a computable Polish space $X$, a subset $U\IncludedIn X$ is \termdefine{effectively open} if there is a lightface
    $\lSigma^0_1$ set $V\IncludedIn\BaireSpace$ such that
    $$
    \rho_X^{-1}(U)=\DomainOf{\rho_X}\cap V.
    $$
    Thus the preimage is $\lSigma^0_1$ relative to the name space; it need not be $\lSigma^0_1$ as a subset of all of
    $\BaireSpace$. By the effective-basis lemma proved below, this is equivalent to giving $U$ as an r.e. union of
    rational balls
    $$U=\bigcup_{e\in J} \Ball{q_{i_e}}{r_e},$$
    where $J$ is recursively enumerable and the centers and rational radii are effectively decoded.
-/
def LambdaEffectivelyOpen {X : Type*} (δ : Representation X) (U : Set X) : Prop :=
  ∃ V, LambdaSigma01 V ∧ δ.namePreimage U = δ.domain ∩ V

/-- Effective closedness is defined by effective openness of the complement. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Membership in an effectively open set is semidecidable from a Cauchy name: watch the name until some approximation is
    accurate enough to certify containment in one of the listed balls. The complement of an effectively open set is
    \termdefine{effectively closed}. Nonmembership in such a closed set is therefore semidecidable: one can eventually
    recognize that a point does not belong to the closed set, but cannot in general recognize membership.
-/
def LambdaEffectivelyClosed {X : Type*} (δ : Representation X) (C : Set X) : Prop :=
  LambdaEffectivelyOpen δ Cᶜ

/-- The same closed program works on the name domain and its open extension. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Membership in an effectively open set is semidecidable from a Cauchy name: watch the name until some approximation is
    accurate enough to certify containment in one of the listed balls. The complement of an effectively open set is
    \termdefine{effectively closed}. Nonmembership in such a closed set is therefore semidecidable: one can eventually
    recognize that a point does not belong to the closed set, but cannot in general recognize membership.
-/
theorem lambdaEffectivelyOpen_iff_semidecidable {X : Type*} (δ : Representation X) (U : Set X) :
    LambdaEffectivelyOpen δ U ↔ SemidecidableFromNames δ U := by
  constructor
  · rintro ⟨V, ⟨P, hP, hV⟩, hU⟩
    refine ⟨P, hP, fun p => ?_⟩
    have he : p.val ∈ V ↔ δ.toFun p ∈ U := by
      constructor
      · intro hp
        have hm : p.val ∈ δ.namePreimage U := by rw [hU]; exact ⟨p.property, hp⟩
        obtain ⟨_, hm⟩ := hm
        exact hm
      · intro hp
        have hm : p.val ∈ δ.namePreimage U := ⟨p.property, hp⟩
        rw [hU] at hm
        exact hm.2
    exact (hV ⟨p.val, mem_univ _⟩).trans he
  · rintro ⟨P, hP, hU⟩
    refine ⟨{p | ∃ m, OracleRuns p P 0 m}, ⟨P, hP, fun _ => Iff.rfl⟩, ?_⟩
    ext p
    constructor
    · rintro ⟨hp, hx⟩
      exact ⟨hp, (hU ⟨p, hp⟩).mpr hx⟩
    · rintro ⟨hp, hx⟩
      exact ⟨hp, (hU ⟨p, hp⟩).mp hx⟩

theorem Representation.namePreimage_univ {X : Type*} (δ : Representation X) :
    δ.namePreimage univ = δ.domain := by
  ext p
  exact ⟨fun ⟨hp, _⟩ => hp, fun hp => ⟨hp, mem_univ _⟩⟩

theorem lambdaEffectivelyOpen_univ {X : Type*} (δ : Representation X) :
    LambdaEffectivelyOpen δ univ := by
  apply (lambdaEffectivelyOpen_iff_semidecidable _ _).mpr
  refine ⟨constantProgram 0, constantProgram_closed 0, fun p => ?_⟩
  exact ⟨fun _ => mem_univ _, fun _ => ⟨0, constantProgram_runs 0 p.val 0⟩⟩

/-- The relative-name definition is equivalent to an enumerable union of rational balls. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For a computable Polish space $X$, a subset $U\IncludedIn X$ is \termdefine{effectively open} if there is a lightface
    $\lSigma^0_1$ set $V\IncludedIn\BaireSpace$ such that
    $$
    \rho_X^{-1}(U)=\DomainOf{\rho_X}\cap V.
    $$
    Thus the preimage is $\lSigma^0_1$ relative to the name space; it need not be $\lSigma^0_1$ as a subset of all of
    $\BaireSpace$. By the effective-basis lemma proved below, this is equivalent to giving $U$ as an r.e. union of
    rational balls
    $$U=\bigcup_{e\in J} \Ball{q_{i_e}}{r_e},$$
    where $J$ is recursively enumerable and the centers and rational radii are effectively decoded.
-/
theorem lambdaEffectivelyOpen_iff_ball_enumeration {X : Type*} [MetricSpace X]
    [CompleteSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (hq : DenseRange q) (U : Set X) :
    LambdaEffectivelyOpen (cauchyRepresentationObject q hq) U ↔
      ∃ E : AlphaTerm, ∃ f : ℕ → ℕ, NumericalComputes E f ∧
        U = ⋃ j, enumeratedRationalBall q (f j) :=
  (lambdaEffectivelyOpen_iff_semidecidable _ _).trans
    (A.semidecidable_iff_ball_enumeration hq U)

/-- With two distinct basic points, even the whole valid-name domain is not lightface open
as a subset of all Baire space. A late digit can violate an earlier Cauchy bound. -/
theorem cauchyNameDomain_not_lambdaSigma01 {X : Type*} [MetricSpace X]
    (q : ℕ → X) (i j : ℕ) (hij : q i ≠ q j) :
    ¬ LambdaSigma01 (cauchyNameDomain q) := by
  rintro ⟨P, _, hP⟩
  have hvalid : IsCauchyName q (fun _ => i) := by
    intro n m _
    simp only [dist_self]
    positivity
  obtain ⟨m, hm⟩ := (hP ⟨fun _ => i, mem_univ _⟩).mpr hvalid
  obtain ⟨K, hK⟩ := hm.finite_use
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hij)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let k := max K (n + 1)
  have hnk : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  let p : ℕ → ℕ := fun a => if a = k then j else i
  have hp : ∀ a < K, p a = i := by
    intro a ha
    have hak : a < k := lt_of_lt_of_le ha (le_max_left _ _)
    simp [p, ne_of_lt hak]
  have hbad : IsCauchyName q p := (hP ⟨p, mem_univ _⟩).mp ⟨m, hK p hp⟩
  have hb : dist (q i) (q j) ≤ (1 / 2 : ℝ)^n := by
    simpa [p, ne_of_lt hnk] using hbad n k hnk.le
  exact (not_le_of_gt hn) hb

/-- Relative effective openness does not imply effective openness of the full name preimage. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For a computable Polish space $X$, a subset $U\IncludedIn X$ is \termdefine{effectively open} if there is a lightface
    $\lSigma^0_1$ set $V\IncludedIn\BaireSpace$ such that
    $$
    \rho_X^{-1}(U)=\DomainOf{\rho_X}\cap V.
    $$
    Thus the preimage is $\lSigma^0_1$ relative to the name space; it need not be $\lSigma^0_1$ as a subset of all of
    $\BaireSpace$. By the effective-basis lemma proved below, this is equivalent to giving $U$ as an r.e. union of
    rational balls
    $$U=\bigcup_{e\in J} \Ball{q_{i_e}}{r_e},$$
    where $J$ is recursively enumerable and the centers and rational radii are effectively decoded.
-/
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
theorem exists_effectivelyOpen_nonSigma01_namePreimage {X : Type*} [MetricSpace X]
    [CompleteSpace X] (q : ℕ → X) (hq : DenseRange q) (i j : ℕ) (hij : q i ≠ q j) :
    ∃ U : Set X, LambdaEffectivelyOpen (cauchyRepresentationObject q hq) U ∧
      ¬ LambdaSigma01 ((cauchyRepresentationObject q hq).namePreimage U) := by
  refine ⟨univ, lambdaEffectivelyOpen_univ _, ?_⟩
  rw [Representation.namePreimage_univ]
  exact cauchyNameDomain_not_lambdaSigma01 q i j hij

/-- Membership in an effectively closed set need not be semidecidable. -/
theorem zeroSingleton_not_semidecidable :
    ¬ SemidecidableFromNames baireIdentityRepresentation {fun _ : ℕ => 0} := by
  rintro ⟨P, _, hP⟩
  obtain ⟨m, hm⟩ := (hP ⟨fun _ => 0, mem_univ _⟩).mpr (by simp [baireIdentityRepresentation])
  obtain ⟨k, hk⟩ := hm.finite_use
  let q : ℕ → ℕ := fun i => if i = k then 1 else 0
  have hq : ∀ i < k, q i = 0 := by
    intro i hi
    simp [q, ne_of_lt hi]
  have heq : q = fun _ => 0 := by
    simpa [baireIdentityRepresentation] using (hP ⟨q, mem_univ _⟩).mp ⟨m, hk q hq⟩
  have hx := congrFun heq k
  simp [q] at hx

/-- Searching for a nonzero digit semidecides the complement of the zero name. -/
theorem zeroSingleton_complement_semidecidable :
    SemidecidableFromNames baireIdentityRepresentation {fun _ : ℕ => 0}ᶜ := by
  refine ⟨digitSearchProgram identityProgram, digitSearchProgram_closed identityProgram_closed,
    fun p => ?_⟩
  rw [digitSearchProgram_domain identityProgram_closed p.val p.val (identityProgram_runs p.val) 0]
  change (∃ k, p.val k ≠ 0) ↔ p.val ≠ fun _ => 0
  constructor
  · rintro ⟨k, hk⟩ he
    exact hk (congrFun he k)
  · intro h
    by_contra hn
    push Not at hn
    exact h (funext hn)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Membership in an effectively open set is semidecidable from a Cauchy name: watch the name until some approximation is
    accurate enough to certify containment in one of the listed balls. The complement of an effectively open set is
    \termdefine{effectively closed}. Nonmembership in such a closed set is therefore semidecidable: one can eventually
    recognize that a point does not belong to the closed set, but cannot in general recognize membership.
-/
theorem exists_effectivelyClosed_not_semidecidable :
    ∃ C : Set (ℕ → ℕ), LambdaEffectivelyClosed baireIdentityRepresentation C ∧
      ¬ SemidecidableFromNames baireIdentityRepresentation C :=
  ⟨{fun _ => 0}, (lambdaEffectivelyOpen_iff_semidecidable _ _).mpr
    zeroSingleton_complement_semidecidable, zeroSingleton_not_semidecidable⟩

/-- A counterexample for the actual effective Cauchy representation of the real line. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Membership in an effectively open set is semidecidable from a Cauchy name: watch the name until some approximation is
    accurate enough to certify containment in one of the listed balls. The complement of an effectively open set is
    \termdefine{effectively closed}. Nonmembership in such a closed set is therefore semidecidable: one can eventually
    recognize that a point does not belong to the closed set, but cannot in general recognize membership.
-/
theorem exists_real_effectivelyClosed_not_semidecidable :
    ∃ C : Set ℝ, LambdaEffectivelyClosed realRepresentation C ∧
      ¬ SemidecidableFromNames realRepresentation C := by
  let U : Set ℝ := Metric.ball (rationalPoint 0) 1
  have hU : SemidecidableFromNames realRepresentation U := by
    have h := realMetricApproximation.semidecidable_ball rationalPoint_dense 0 ((1, 0), 0)
    norm_num [RationalCode.value] at h
    exact h
  refine ⟨Uᶜ, ?_, ?_⟩
  · change LambdaEffectivelyOpen realRepresentation (Uᶜ)ᶜ
    rw [compl_compl]
    exact (lambdaEffectivelyOpen_iff_semidecidable _ _).mpr hU
  · intro hC
    have hopen : IsOpen Uᶜ := hC.isOpen
      (isQuotientMap_of_admissible realRepresentation
        (cauchyRepresentationObject_isAdmissible rationalPoint rationalPoint_dense))
    have hclosed : IsClosed U := isOpen_compl_iff.mp hopen
    change IsClosed (Metric.ball (rationalPoint 0) 1) at hclosed
    rw [Real.ball_eq_Ioo] at hclosed
    have hbad := isClosed_Ioo_iff.mp hclosed
    linarith

end PolishSpaceBook
