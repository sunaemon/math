module

public import PolishSpaceBook.LambdaRealEquality
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-! # Reading the halting set from a hypothetical name of its base-four real

The tail estimate leaves a strict gap between the two possible digits. The
reader uses rational comparison and recursion, never equality of real numbers.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
open Filter Topology
set_option maxRecDepth 4096

noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The weight of digit e in the base-four coding. -/
def haltingWeight (e : ℕ) : ℝ := (1/4:ℝ)^(e+1)

def haltingDigit (K : ℕ → Prop) (e : ℕ) : ℝ :=
  if K e then haltingWeight e else 0

def haltingSetReal (K : ℕ → Prop) : ℝ := ∑' e, haltingDigit K e

def haltingPrefix (K : ℕ → Prop) (e : ℕ) : ℝ :=
  ∑ j ∈ Finset.range e, haltingDigit K j

theorem haltingWeight_pos (e : ℕ) : 0 < haltingWeight e := by
  unfold haltingWeight; positivity

theorem haltingWeight_summable : Summable haltingWeight := by
  change Summable (fun e : ℕ => (1/4:ℝ)^(e+1))
  simpa only [haltingWeight,pow_succ,mul_comm] using
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)).mul_left (1/4)

theorem haltingDigit_nonneg (K : ℕ → Prop) (e : ℕ) : 0 ≤ haltingDigit K e := by
  classical
  simp only [haltingDigit]
  split_ifs
  · exact (haltingWeight_pos e).le
  · exact le_rfl

theorem haltingDigit_le (K : ℕ → Prop) (e : ℕ) : haltingDigit K e ≤ haltingWeight e := by
  classical
  simp only [haltingDigit]
  split_ifs <;> simp [le_of_lt (haltingWeight_pos e)]

theorem haltingDigit_summable (K : ℕ → Prop) : Summable (haltingDigit K) :=
  Summable.of_nonneg_of_le (haltingDigit_nonneg K) (haltingDigit_le K) haltingWeight_summable

theorem haltingWeight_tail (e : ℕ) :
    ∑' j, haltingWeight (j+(e+1)) = haltingWeight e/3 := by
  have he (j : ℕ) : haltingWeight (j+(e+1)) = haltingWeight e * (1/4:ℝ)^(j+1) := by
    unfold haltingWeight
    rw [← pow_add]
    congr 1; omega
  simp_rw [he]
  rw [tsum_mul_left]
  have hs : ∑' j : ℕ, (1/4:ℝ)^(j+1) = 1/3 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [hs]; ring

/-- The prefix and current digit leave a tail of at most one third of the current weight. -/
theorem haltingSetReal_split (K : ℕ → Prop) (e : ℕ) :
    haltingSetReal K - haltingPrefix K e =
      haltingDigit K e + ∑' j, haltingDigit K (j+(e+1)) := by
  have h := (haltingDigit_summable K).sum_add_tsum_nat_add (e+1)
  rw [Finset.sum_range_succ] at h
  dsimp [haltingSetReal,haltingPrefix]
  linarith

theorem haltingSetReal_gap (K : ℕ → Prop) (e : ℕ) :
    (¬ K e → 0 ≤ haltingSetReal K - haltingPrefix K e ∧
      haltingSetReal K - haltingPrefix K e ≤ haltingWeight e/3) ∧
    (K e → haltingWeight e ≤ haltingSetReal K - haltingPrefix K e) := by
  classical
  have hn : 0 ≤ ∑' j, haltingDigit K (j+(e+1)) :=
    tsum_nonneg (fun j => haltingDigit_nonneg K (j+(e+1)))
  have hb : (∑' j, haltingDigit K (j+(e+1))) ≤ haltingWeight e/3 := by
    rw [← haltingWeight_tail]
    exact ((summable_nat_add_iff (e+1)).mpr (haltingDigit_summable K)).tsum_le_tsum
      (fun j => haltingDigit_le K _) ((summable_nat_add_iff (e+1)).mpr haltingWeight_summable)
  rw [haltingSetReal_split]
  constructor
  · intro h; simpa [haltingDigit,h] using And.intro hn hb
  · intro h
    rw [show haltingDigit K e = haltingWeight e by simp [haltingDigit,h]]
    linarith

/-- A fixed precision, linear in the digit index, is sufficient. -/
theorem haltingWeight_precision (e : ℕ) :
    (1/2:ℝ)^(2*e+5) = haltingWeight e/8 := by
  rw [show 2*e+5 = 2*(e+1)+3 by omega,pow_add,pow_mul]
  norm_num [haltingWeight]
  ring

theorem haltingSetReal_read_digit (K : ℕ → Prop) (e : ℕ) (q : ℝ)
    (hq : |q-haltingSetReal K| ≤ (1/2:ℝ)^(2*e+5)) :
    haltingPrefix K e + 2*haltingWeight e/3 < q ↔ K e := by
  classical
  rw [haltingWeight_precision] at hq
  obtain ⟨hlo,hhi⟩ := abs_le.mp hq
  have hw := haltingWeight_pos e
  obtain ⟨hn,hy⟩ := haltingSetReal_gap K e
  by_cases h : K e
  · have := hy h
    constructor
    · exact fun _ => h
    · intro _; linarith
  · have := hn h
    constructor
    · intro hlt; exfalso; linarith
    · exact fun hk => (h hk).elim

end

/-- The threshold 2 w_e / 3, with an explicitly positive denominator. -/
def haltingThresholdCode (e : ℕ) : RationalCode := ((2,0),3*2^(2*e+2)-1)

theorem haltingThresholdCode_value (e : ℕ) :
    ((haltingThresholdCode e).value:ℝ) = 2*haltingWeight e/3 := by
  have hp : 1 ≤ 3*2^(2*e+2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hw : (1/2:ℝ)^(2*e+2) = haltingWeight e := by
    rw [show 2*e+2 = 2*(e+1) by omega,pow_mul]
    norm_num [haltingWeight]
  simp only [haltingThresholdCode,RationalCode.value,Nat.sub_add_cancel hp]
  push_cast
  rw [← hw,one_div_pow]
  field_simp
  norm_num

def haltingThresholdProgram : AlphaTerm :=
  pairNumerical (numericalConstant (Nat.pair 2 0))
    (numericalCompose predecessorTerm (mulNumerical (numericalConstant 3)
      (numericalCompose powerTwoTerm
        (addNumerical (mulNumerical (numericalConstant 2) numericalIdentity) (numericalConstant 2)))))

theorem haltingThreshold_computes : NumericalComputes haltingThresholdProgram
    (fun e => (haltingThresholdCode e).natCode) := by
  have h := predecessor_computes.comp ((numericalConstant_computes 3).mul
    (powerTwo_computes.comp (((numericalConstant_computes 2).mul numericalIdentity_computes).add
      (numericalConstant_computes 2))))
  simpa only [haltingThresholdProgram,haltingThresholdCode,RationalCode.natCode,id_eq] using
    (numericalConstant_computes (Nat.pair 2 0)).pair h

/-- The test reads an approximate real value and the already recovered prefix. -/
def haltingReaderTest (p : ℕ → ℕ) (e s : ℕ) : ℕ :=
  if (RationalCode.add (RationalCode.ofNat s) (haltingThresholdCode e)).value <
      (RationalCode.ofNat (p (2*e+5))).value then 1 else 0

def haltingReaderTestProgram (P : AlphaTerm) : AlphaTerm :=
  let E := numericalProjectionTerm true
  let S := numericalProjectionTerm false
  let H := numericalCompose haltingThresholdProgram E
  let Q := numericalCompose P (addNumerical (mulNumerical (numericalConstant 2) E) (numericalConstant 5))
  numericalCompose rationalLessTerm (pairNumerical
    (numericalCompose rationalAddTerm (pairNumerical S H)) Q)

theorem haltingReaderTest_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (haltingReaderTestProgram P)
      (fun z => haltingReaderTest p z.unpair.1 z.unpair.2) := by
  have he := projection_computes true
  have hs := projection_computes false
  have hh := haltingThreshold_computes.comp he
  have hq := hp.comp (((numericalConstant_computes 2).mul he).add (numericalConstant_computes 5))
  simpa [haltingReaderTestProgram,haltingReaderTest,Nat.unpair_pair] using
    rationalLess_computes.comp ((rationalAdd_computes.comp (hs.pair hh)).pair hq)

def haltingReaderStep (p : ℕ → ℕ) (e s : ℕ) : ℕ :=
  if haltingReaderTest p e s = 0 then s else
    (RationalCode.add (RationalCode.ofNat s) (RationalCode.dyadic (2*e+2))).natCode

/-- Store the rational prefix; no membership oracle occurs in this recursion. -/
def haltingReaderPrefix (p : ℕ → ℕ) : ℕ → ℕ := primitiveRec 0 (haltingReaderStep p)

def haltingReaderStepProgram (P : AlphaTerm) : AlphaTerm :=
  let E := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let S := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let T := numericalCompose (haltingReaderTestProgram P) (pairNumerical E S)
  let W := numericalCompose rationalDyadicTerm
    (addNumerical (mulNumerical (numericalConstant 2) E) (numericalConstant 2))
  numericalIfZero T S (numericalCompose rationalAddTerm (pairNumerical S W))

theorem haltingReaderStep_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (haltingReaderStepProgram P)
      (fun z => haltingReaderStep p z.unpair.2.unpair.1 z.unpair.2.unpair.2) := by
  have he := (projection_computes true).comp (projection_computes false)
  have hs := (projection_computes false).comp (projection_computes false)
  have ht := (haltingReaderTest_computes hp).comp (he.pair hs)
  have hw := rationalDyadic_computes.comp
    (((numericalConstant_computes 2).mul he).add (numericalConstant_computes 2))
  simpa [haltingReaderStepProgram,haltingReaderStep,Nat.unpair_pair] using
    numericalIfZero_computes ht hs (rationalAdd_computes.comp (hs.pair hw))

def haltingReaderPrefixProgram (P : AlphaTerm) : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 0) (haltingReaderStepProgram P))
  (pairNumerical (numericalConstant 0) numericalIdentity)

theorem haltingReaderPrefix_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (haltingReaderPrefixProgram P) (haltingReaderPrefix p) := by
  simpa only [haltingReaderPrefixProgram,haltingReaderPrefix,Nat.unpair_pair,id_eq] using
    (numericalRecursion_computes (numericalConstant_computes 0) (haltingReaderStep_computes hp)).comp
      ((numericalConstant_computes 0).pair numericalIdentity_computes)

def haltingReaderProgram (P : AlphaTerm) : AlphaTerm :=
  numericalCompose (haltingReaderTestProgram P)
    (pairNumerical numericalIdentity (haltingReaderPrefixProgram P))

theorem haltingReader_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (haltingReaderProgram P)
      (fun e => haltingReaderTest p e (haltingReaderPrefix p e)) := by
  simpa only [haltingReaderProgram,Nat.unpair_pair,id_eq] using
    (haltingReaderTest_computes hp).comp (numericalIdentity_computes.pair (haltingReaderPrefix_computes hp))


section
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem haltingReaderTest_correct (K : ℕ → Prop) (p : ℕ → ℕ) (e s : ℕ)
    (hp : |rationalPoint (p (2*e+5))-haltingSetReal K| ≤ (1/2:ℝ)^(2*e+5))
    (hs : rationalPoint s = haltingPrefix K e) :
    haltingReaderTest p e s = if K e then 1 else 0 := by
  classical
  have he : (RationalCode.add (RationalCode.ofNat s) (haltingThresholdCode e)).value <
      (RationalCode.ofNat (p (2*e+5))).value ↔ K e := by
    rw [← Rat.cast_lt (K := ℝ),RationalCode.value_add,Rat.cast_add,
      haltingThresholdCode_value]
    change rationalPoint s + 2*haltingWeight e/3 < rationalPoint (p (2*e+5)) ↔ K e
    rw [hs]
    exact haltingSetReal_read_digit K e _ hp
  simp only [haltingReaderTest,he]

theorem haltingReaderPrefix_correct (K : ℕ → Prop) (p : ℕ → ℕ)
    (hp : ∀ n, |rationalPoint (p n)-haltingSetReal K| ≤ (1/2:ℝ)^n) (e : ℕ) :
    rationalPoint (haltingReaderPrefix p e) = haltingPrefix K e := by
  classical
  induction e with
  | zero => simp [haltingReaderPrefix,primitiveRec,haltingPrefix]
  | succ e ih =>
    change rationalPoint (haltingReaderStep p e (haltingReaderPrefix p e)) = _
    rw [haltingReaderStep,haltingReaderTest_correct K p e _ (hp _) ih]
    have hw : (1/2:ℝ)^(2*e+2) = haltingWeight e := by
      rw [show 2*e+2 = 2*(e+1) by omega,pow_mul]
      norm_num [haltingWeight]
    rw [haltingPrefix,Finset.sum_range_succ,← haltingPrefix]
    by_cases h : K e
    · simp only [ite_eq_left h,one_ne_zero,ite_false,rationalPoint,RationalCode.ofNat_natCode,
        RationalCode.value_add,Rat.cast_add,RationalCode.real_value_dyadic]
      change rationalPoint (haltingReaderPrefix p e) + (1/2:ℝ)^(2*e+2) = _
      rw [ih,hw]
      simp [haltingDigit,h]
    · simp [h,ih,haltingDigit]

/-- A numerical name of the weighted real computes every digit by the displayed recursion. -/
theorem haltingSetReal_decider (K : ℕ → Prop) {P : AlphaTerm} {p : ℕ → ℕ}
    (hP : NumericalComputes P p)
    (hp : ∀ n, |rationalPoint (p n)-haltingSetReal K| ≤ (1/2:ℝ)^n) :
    NumericalComputes (haltingReaderProgram P) (fun e => if K e then 1 else 0) := by
  classical
  have h := haltingReader_computes hP
  refine ⟨h.1,fun e => ?_⟩
  simpa only [haltingReaderTest_correct K p e _ (hp _) (haltingReaderPrefix_correct K p hp e)] using h.2 e

/-- Even an approximation program with the stated error bound would decide halting. -/
theorem haltingSetReal_not_approximable :
    ¬ ∃ (P : AlphaTerm) (p : ℕ → ℕ), NumericalComputes P p ∧
      ∀ n, |rationalPoint (p n)-haltingSetReal diagonalHalts| ≤ (1/2:ℝ)^n := by
  classical
  rintro ⟨P,p,hP,hp⟩
  have hd := haltingSetReal_decider diagonalHalts hP hp
  apply diagonalHalts_not_decidable
  have h := numericalIfZero_computes hd (numericalConstant_computes 1) (numericalConstant_computes 0)
  refine ⟨numericalIfZero (haltingReaderProgram P) (numericalConstant 1) (numericalConstant 0),?_⟩
  convert h using 1
  funext e
  by_cases hh : diagonalHalts e <;> simp [hh]

/-- No computable Cauchy name represents the real coding diagonal numerical halting. -/
theorem haltingSetReal_not_computable :
    ¬ ∃ p : realRepresentation.domain, realRepresentation.toFun p = haltingSetReal diagonalHalts ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val := by
  rintro ⟨p,hp,P,hP⟩
  apply haltingSetReal_not_approximable
  refine ⟨P,p.val,hP,fun n => ?_⟩
  have h := cauchyRepresentation_dist_le rationalPoint p n
  change dist (rationalPoint (p.val n)) (realRepresentation.toFun p) ≤ _ at h
  simpa only [hp,Real.dist_eq] using h

theorem haltingSetReal_irrational : Irrational (haltingSetReal diagonalHalts) := by
  rintro ⟨q,hq⟩
  obtain ⟨c,hc⟩ := RationalCode.value_surjective q
  have hv : rationalPoint c.natCode = haltingSetReal diagonalHalts := by
    simpa [rationalPoint,hc] using hq
  apply haltingSetReal_not_approximable
  refine ⟨numericalConstant c.natCode,fun _ => c.natCode,numericalConstant_computes _,fun n => ?_⟩
  rw [hv,sub_self,abs_zero]
  positivity

end

/-- The existing finite certificate scan is nonzero exactly when a certificate has appeared. -/
theorem haltingRealName_detects (e s : ℕ) :
    haltingRealName e s ≠ 0 ↔ ∃ k < s, Term.outputCandidate e e k = true := by
  induction s with
  | zero => simp [haltingRealName,primitiveRec]
  | succ s ih =>
    change (if haltingRealName e s = 0 then
      if Term.outputCandidate e e s then (RationalCode.dyadic (s+2)).natCode else 0
      else haltingRealName e s) ≠ 0 ↔ _
    by_cases hz : haltingRealName e s = 0
    · have hn : ¬ ∃ k < s, Term.outputCandidate e e k = true := by simpa [hz] using ih.symm
      simp only [hz,ite_true]
      cases hc : Term.outputCandidate e e s
      · simp only [Bool.false_eq_true,ite_false,ne_eq,not_true_eq_false,false_iff]
        rintro ⟨k,hk,hc'⟩
        by_cases hks : k<s
        · exact hn ⟨k,hks,hc'⟩
        · have : k=s := by omega
          simp [this,hc] at hc'
      · simp only [ite_true]
        exact ⟨fun _ => ⟨s,by omega,hc⟩,fun _ => dyadic_code_ne_zero _⟩
    · simp only [hz,ite_false]
      obtain ⟨k,hk,hc⟩ := ih.mp hz
      exact ⟨fun _ => ⟨k,by omega,hc⟩,fun _ => hz⟩

def haltingStageTerm (s e : ℕ) : ℕ :=
  if haltingRealName e s = 0 then 0 else (RationalCode.dyadic (2*e+2)).natCode

def haltingStageSum (s : ℕ) : ℕ → ℕ := primitiveRec 0 (fun e r =>
  (RationalCode.add (RationalCode.ofNat r) (RationalCode.ofNat (haltingStageTerm s e))).natCode)

def haltingApproximation (s : ℕ) : ℕ := haltingStageSum s s

def haltingStageTermProgram : AlphaTerm :=
  let S := numericalProjectionTerm true
  let E := numericalProjectionTerm false
  numericalIfZero (numericalCompose haltingRealNameProgram (pairNumerical E S))
    (numericalConstant 0) (numericalCompose rationalDyadicTerm
      (addNumerical (mulNumerical (numericalConstant 2) E) (numericalConstant 2)))

theorem haltingStageTerm_computes : NumericalComputes haltingStageTermProgram
    (fun z => haltingStageTerm z.unpair.1 z.unpair.2) := by
  have hs := projection_computes true
  have he := projection_computes false
  have hh := haltingRealName_computes.comp (he.pair hs)
  have hw := rationalDyadic_computes.comp
    (((numericalConstant_computes 2).mul he).add (numericalConstant_computes 2))
  simpa [haltingStageTermProgram,haltingStageTerm,Nat.unpair_pair] using
    numericalIfZero_computes hh (numericalConstant_computes 0) hw

def haltingStageSumStep : AlphaTerm :=
  let S := numericalProjectionTerm true
  let E := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let R := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  numericalCompose rationalAddTerm (pairNumerical R
    (numericalCompose haltingStageTermProgram (pairNumerical S E)))

def haltingApproximationProgram : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 0) haltingStageSumStep)
  (pairNumerical numericalIdentity numericalIdentity)

theorem haltingApproximation_computes :
    NumericalComputes haltingApproximationProgram haltingApproximation := by
  have hs := projection_computes true
  have he := (projection_computes true).comp (projection_computes false)
  have hr := (projection_computes false).comp (projection_computes false)
  have ht := rationalAdd_computes.comp (hr.pair (haltingStageTerm_computes.comp (hs.pair he)))
  have ht' : NumericalComputes haltingStageSumStep (fun z =>
      (RationalCode.add (RationalCode.ofNat z.unpair.2.unpair.2)
        (RationalCode.ofNat (haltingStageTerm z.unpair.1 z.unpair.2.unpair.1))).natCode) := by
    simpa [haltingStageSumStep,Nat.unpair_pair] using ht
  have h := (numericalRecursion_computes (numericalConstant_computes 0) ht').comp
    (numericalIdentity_computes.pair numericalIdentity_computes)
  refine ⟨h.1,fun s => ?_⟩
  simpa only [haltingApproximationProgram,haltingApproximation,haltingStageSum,Nat.unpair_pair,id_eq] using h.2 s

noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def haltingStageDigit (s e : ℕ) : ℝ :=
  if e < s ∧ ∃ k < s, Term.outputCandidate e e k = true then haltingWeight e else 0

theorem haltingStageTerm_value (s e : ℕ) :
    rationalPoint (haltingStageTerm s e) =
      if ∃ k < s, Term.outputCandidate e e k = true then haltingWeight e else 0 := by
  have hw : (1/2:ℝ)^(2*e+2) = haltingWeight e := by
    rw [show 2*e+2 = 2*(e+1) by omega,pow_mul]; norm_num [haltingWeight]
  unfold haltingStageTerm
  by_cases hz : haltingRealName e s = 0
  · have hn := mt (haltingRealName_detects e s).mpr (not_not_intro hz)
    simp [hz,hn]
  · have hy := (haltingRealName_detects e s).mp hz
    simpa only [ite_eq_right hz,ite_eq_left hy,rationalPoint_dyadic] using hw

theorem haltingStageSum_value (s n : ℕ) :
    rationalPoint (haltingStageSum s n) =
      ∑ e ∈ Finset.range n, rationalPoint (haltingStageTerm s e) := by
  induction n with
  | zero => simp [haltingStageSum,primitiveRec]
  | succ n ih =>
    change rationalPoint (RationalCode.add (RationalCode.ofNat (haltingStageSum s n))
      (RationalCode.ofNat (haltingStageTerm s n))).natCode = _
    rw [Finset.sum_range_succ]
    simp only [rationalPoint,RationalCode.ofNat_natCode,RationalCode.value_add,Rat.cast_add]
    exact congrArg (· + rationalPoint (haltingStageTerm s n)) ih

theorem haltingApproximation_value (s : ℕ) :
    rationalPoint (haltingApproximation s) = ∑' e, haltingStageDigit s e := by
  rw [haltingApproximation,haltingStageSum_value]
  rw [tsum_eq_sum (s := Finset.range s) (fun e he => by
    simp [haltingStageDigit,show ¬ e<s by simpa using he])]
  apply Finset.sum_congr rfl
  intro e he
  simp [haltingStageTerm_value,haltingStageDigit,Finset.mem_range.mp he]

theorem haltingStageDigit_nonneg (s e : ℕ) : 0 ≤ haltingStageDigit s e := by
  unfold haltingStageDigit
  split_ifs
  · exact (haltingWeight_pos e).le
  · exact le_rfl

theorem haltingStageDigit_le (s e : ℕ) : haltingStageDigit s e ≤ haltingDigit diagonalHalts e := by
  unfold haltingStageDigit
  split_ifs with h
  · have hh := (candidate_exists_iff_halts e).mp ⟨h.2.choose,h.2.choose_spec.2⟩
    simp [haltingDigit,hh]
  · exact haltingDigit_nonneg _ _

theorem haltingStageDigit_summable (s : ℕ) : Summable (haltingStageDigit s) :=
  Summable.of_nonneg_of_le (haltingStageDigit_nonneg s) (haltingStageDigit_le s)
    (haltingDigit_summable diagonalHalts)

theorem haltingApproximation_le (s : ℕ) :
    rationalPoint (haltingApproximation s) ≤ haltingSetReal diagonalHalts := by
  rw [haltingApproximation_value,haltingSetReal]
  exact (haltingStageDigit_summable s).tsum_le_tsum (haltingStageDigit_le s)
    (haltingDigit_summable diagonalHalts)

theorem haltingApproximation_monotone : Monotone (fun s => rationalPoint (haltingApproximation s)) := by
  intro s t hst
  dsimp only
  rw [haltingApproximation_value,haltingApproximation_value]
  apply (haltingStageDigit_summable s).tsum_le_tsum _ (haltingStageDigit_summable t)
  intro e
  unfold haltingStageDigit
  split_ifs with hs ht ht
  · exact le_rfl
  · obtain ⟨he,k,hk,hc⟩ := hs
    exact (ht ⟨by omega,k,by omega,hc⟩).elim
  · exact (haltingWeight_pos e).le
  · exact le_rfl

theorem haltingApproximation_tendsto :
    Tendsto (fun s => rationalPoint (haltingApproximation s)) atTop (𝓝 (haltingSetReal diagonalHalts)) := by
  simp_rw [haltingApproximation_value]
  apply tendsto_tsum_of_dominated_convergence haltingWeight_summable
  · intro e
    by_cases h : diagonalHalts e
    · obtain ⟨k,hk⟩ := (candidate_exists_iff_halts e).mpr h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (max e k+1)] with s hs
      simp [haltingStageDigit,haltingDigit,h,show e<s by omega,
        show ∃ j<s, Term.outputCandidate e e j = true from ⟨k,by omega,hk⟩]
    · have hn : ∀ s, ¬ ∃ k<s, Term.outputCandidate e e k = true := by
        rintro s ⟨k,_,hk⟩; exact h ((candidate_exists_iff_halts e).mp ⟨k,hk⟩)
      simp [haltingStageDigit,haltingDigit,h,hn]
  · exact Filter.Eventually.of_forall (fun s e => by
      rw [Real.norm_eq_abs,abs_of_nonneg (haltingStageDigit_nonneg s e)]
      exact (haltingStageDigit_le s e).trans (haltingDigit_le _ e))

/-- A computable modulus would turn this particular increasing sequence into a name. -/
theorem haltingApproximation_no_computable_modulus :
    ¬ ∃ (H : AlphaTerm) (h : ℕ → ℕ), NumericalComputes H h ∧
      ∀ n, haltingSetReal diagonalHalts - rationalPoint (haltingApproximation (h n)) ≤ (1/2:ℝ)^n := by
  rintro ⟨H,h,hH,hh⟩
  apply haltingSetReal_not_approximable
  refine ⟨numericalCompose haltingApproximationProgram H,fun n => haltingApproximation (h n),
    haltingApproximation_computes.comp hH,fun n => ?_⟩
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (haltingApproximation_le _))]
  exact hh n

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: example
  title: A noncomputable irrational from the halting set
  excerpt: |
    \begin{example*}[\termdefineas{halting-set real}{A noncomputable irrational from the halting set}]
    The real number
    $$\HaltingReal:=\sum_{e\in K}4^{-(e+1)}$$
    is noncomputable, hence irrational. It is the limit of a computable increasing sequence of rational numbers, but that
    sequence has no computable convergence bound.
    \end{example*}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $w_e:=4^{-(e+1)}$ and $S_e:=\sum_{j<e,\,j\in K}w_j$. The geometric series gives
    $$\sum_{j\ge0}w_j=\frac13,\qquad \sum_{j>e}w_j=\frac{w_e}{3}.$$
    Thus the defining series converges, and removing the prefix gives the two bounds
    $$\begin{cases}
    0\le\HaltingReal-S_e\le w_e/3,&e\notin K,\\
    \HaltingReal-S_e\ge w_e,&e\in K.
    \end{cases}$$
    Suppose a closed term $P$ computes a rational-code name $p$ of $\HaltingReal$. The Cauchy-name estimate gives
    $$\bigl|\RationalValue{p(n)}-\HaltingReal\bigr|\le2^{-n}.$$
    At $n=2e+5$ the error is at most $w_e/8$. Consequently, writing $q=\RationalValue{p(2e+5)}$, we have
    $$\begin{cases}
    q-S_e\le 11w_e/24<2w_e/3,&e\notin K,\\
    q-S_e\ge 7w_e/8>2w_e/3,&e\in K.
    \end{cases}$$
    In particular, the rational comparison $S_e+2w_e/3<q$ decides the next digit once the prefix has been recovered.

    Here is the recursion on codes that implements this argument. Let $W,H$ be the closed terms computing
    $$d_e:=\RationalCode{1}{0}{2^{2e+2}-1},\qquad
    h_e:=\RationalCode{2}{0}{3\cdot2^{2e+2}-1}.$$
    Their values are $w_e$ and $2w_e/3$. Powers of two, multiplication, predecessor, and numerical pairing construct $W,H$;
    both denominators are positive, so the displayed subtractions are ordinary subtraction. A closed term $T$ takes the
    encoded pair of $e$ and a rational prefix code $s$. It adds $s$ to $h_e$ using $\LambdaRationalAdd$, evaluates $P$ at
    $2e+5$, and compares the two rational codes using $\LambdaRationalLess$. Thus
    $$T\ChurchNumeral{\NatPair{e}{s}}\to_\beta^*\ChurchNumeral{b(e,s)},\qquad
    b(e,s):=\begin{cases}
    1,&\RationalValue{s}+2w_e/3<\RationalValue{p(2e+5)},\\
    0,&\text{otherwise}.
    \end{cases}$$
    All the operations are total on natural inputs.

    Start with the zero code $s_0=0$. At step $e$, retain $s_e$ if $b(e,s_e)=0$, and otherwise replace it by the code
    obtained by adding $d_e$ to $s_e$. The numerical recursor, with the zero test and rational addition for its step,
    therefore gives a closed term $R$ satisfying
    $$R\ChurchNumeral{e}\to_\beta^*\ChurchNumeral{s_e}.$$
    Induction proves $\RationalValue{s_e}=S_e$: the comparison gives $b(e,s_e)=1$ exactly when $e\in K$, so the update adds
    exactly the next summand of the prefix. Hence the closed term
    $$D:=\lambdaab{u}{T\,(\LambdaNumericPair\,u\,(R\,u))}$$
    returns $1$ on $K$ and $0$ outside $K$, contradicting the diagonal argument. Every rational has a constant computable
    name, so $\HaltingReal$ is also irrational. The strict gap in the comparison avoids any ambiguity of positional
    expansions.

    To construct an increasing approximation, let $c_e(k)\in\{0,1\}$ be the result of the finite certificate test
    $\LambdaOutputCandidate$ for $\varphi_e(e)$ at candidate $k$. Thus $e\in K$ exactly when some $c_e(k)=1$. Define
    $$K_s:=\{e<s:\exists k<s\ (c_e(k)=1)\},\qquad a_s:=\sum_{e\in K_s}w_e.$$
    Both bounds increase with $s$, so $K_s\IncludedIn K_{s+1}$ and $a_s\le a_{s+1}\le\HaltingReal$.
    For each fixed $e$, the contribution to $a_s$ is eventually $w_e$ if $e\in K$, and is always zero otherwise.
    These contributions are bounded by the summable sequence $\Sequence{w_e}{e\in\omega}$; dominated convergence for series
    therefore gives
    $a_s\to\HaltingReal$.

    The rational codes of $a_s$ are computed by two bounded recursions. For each $e<s$, scan all $k<s$ and retain
    whether an accepted certificate has appeared. This flag selects $d_e$ or the zero code. Starting with zero, the outer
    recursion adds these selected codes for $e<s$ using $\LambdaRationalAdd$. The parameterized numerical
    recursor keeps $s$ available in both loops. Thus a single closed term $A$ computes codes $u_s$ with
    $$A\ChurchNumeral{s}\to_\beta^*\ChurchNumeral{u_s},\qquad \RationalValue{u_s}=a_s.$$
    For $s=0$, the outer loop is empty and outputs the zero code.
    Only finite certificate checks are performed, even when the indexed programs diverge.

    Finally, suppose a closed term $M$ computed a total function $h$ with
    $$0\le\HaltingReal-a_{h(n)}\le2^{-n}\qquad(n\in\NN).$$
    Then $\lambdaab{v}{A\,(M\,v)}$ would compute rational approximations to $\HaltingReal$ with that error bound.
    The same digit-reading construction would decide $K$, a contradiction. Thus even this increasing computable
    convergent sequence has no computable convergence bound.
    \end{proof}
-/
theorem haltingSetReal_example :
    (¬ ∃ p : realRepresentation.domain, realRepresentation.toFun p = haltingSetReal diagonalHalts ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val) ∧
    Irrational (haltingSetReal diagonalHalts) ∧
    NumericalComputes haltingApproximationProgram haltingApproximation ∧
    Monotone (fun s => rationalPoint (haltingApproximation s)) ∧
    Tendsto (fun s => rationalPoint (haltingApproximation s)) atTop (𝓝 (haltingSetReal diagonalHalts)) ∧
    (¬ ∃ (H : AlphaTerm) (h : ℕ → ℕ), NumericalComputes H h ∧
      ∀ n, haltingSetReal diagonalHalts - rationalPoint (haltingApproximation (h n)) ≤ (1/2:ℝ)^n) :=
  ⟨haltingSetReal_not_computable,haltingSetReal_irrational,haltingApproximation_computes,
    haltingApproximation_monotone,haltingApproximation_tendsto,haltingApproximation_no_computable_modulus⟩

end
end PolishSpaceBook.LambdaIndexPCA
