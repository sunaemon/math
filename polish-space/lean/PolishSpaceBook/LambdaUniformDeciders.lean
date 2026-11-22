module

public import PolishSpaceBook.LambdaJumpQuantifiers
public import PolishSpaceBook.LambdaTreeMapPrograms

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # One decision term for a family of input parameters

The term is selected before the family index. Boolean operations, numerical
reindexing and bounded quantification preserve that order of quantifiers.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
set_option maxHeartbeats 400000

def conjunctionProgram (P Q : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))
    (pairOutputProgram P Q)

theorem conjunctionProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (conjunctionProgram P Q).Closed :=
  mapOutputProgram_closed ((projection_computes true).mul (projection_computes false)).1
    (pairOutputProgram_closed hP hQ)

theorem conjunctionProgram_decides {ε : ℕ → ℕ} {P Q : AlphaTerm} {R S : ℕ → Prop}
    (hP : Decides ε P R) (hQ : Decides ε Q S) :
    Decides ε (conjunctionProgram P Q) (fun n => R n ∧ S n) := by
  classical
  have hM : NumericalComputes
      (mulNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))
      (fun z => z.unpair.1 * z.unpair.2) :=
    (projection_computes true).mul (projection_computes false)
  refine ⟨conjunctionProgram_closed hP.1 hQ.1, fun n => ?_⟩
  have hr := mapOutputProgram_runs hM.1 (pairOutputProgram_closed hP.1 hQ.1)
    (pairOutputProgram_runs hP.1 hQ.1 (hP.runs n) (hQ.runs n))
    (hM.2 (Nat.pair (if R n then 1 else 0) (if S n then 1 else 0)))
  simp only [Nat.unpair_pair] at hr
  constructor
  · rintro ⟨hR,hS⟩
    simpa only [conjunctionProgram,ite_eq_left hR,ite_eq_left hS,mul_one] using hr
  · intro hn
    by_cases hR : R n
    · have hS : ¬ S n := fun hs => hn ⟨hR,hs⟩
      simpa only [conjunctionProgram,ite_eq_left hR,ite_eq_right hS,mul_zero] using hr
    · simpa only [conjunctionProgram,ite_eq_right hR,zero_mul] using hr


/-- One closed term decides every member at its indicated input parameter. -/
def UniformlyDecidable {ι : Type*} (ε : ι → ℕ → ℕ) (R : ι → ℕ → Prop) : Prop :=
  ∃ P : AlphaTerm, P.Closed ∧ ∀ i, Decides (ε i) P (R i)

theorem UniformlyDecidable.and {ι : Type*} {ε : ι → ℕ → ℕ} {R S : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) (hS : UniformlyDecidable ε S) :
    UniformlyDecidable ε (fun i n => R i n ∧ S i n) := by
  obtain ⟨P,hP,hR⟩ := hR
  obtain ⟨Q,hQ,hS⟩ := hS
  exact ⟨conjunctionProgram P Q,conjunctionProgram_closed hP hQ,
    fun i => conjunctionProgram_decides (hR i) (hS i)⟩

theorem UniformlyDecidable.not {ι : Type*} {ε : ι → ℕ → ℕ} {R : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) : UniformlyDecidable ε (fun i n => ¬ R i n) := by
  obtain ⟨P,hP,hR⟩ := hR
  exact ⟨mapOutputProgram reverseZeroTerm P,mapOutputProgram_closed reverseZero_computes.1 hP,
    fun i => (hR i).negate⟩

theorem UniformlyDecidable.imp {ι : Type*} {ε : ι → ℕ → ℕ} {R S : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) (hS : UniformlyDecidable ε S) :
    UniformlyDecidable ε (fun i n => R i n → S i n) := by
  simpa only [not_and,not_not] using (hR.and hS.not).not

theorem UniformlyDecidable.reindex {ι : Type*} {ε : ι → ℕ → ℕ} {R : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : UniformlyDecidable ε (fun i n => R i (f n)) := by
  obtain ⟨P,hP,hR⟩ := hR
  exact ⟨reindexProgram P F,reindexProgram_closed hP hF.1,
    fun i => (hR i).precompNumerical hF (g := f) (by intro n; rfl)⟩

def boundedAllProgram (P N : AlphaTerm) : AlphaTerm :=
  reindexProgram (relativeProductProgram P) (pairNumerical numericalIdentity N)

theorem Decides.boundedAll {ε : ℕ → ℕ} {P N : AlphaTerm} {R : ℕ → Prop} {n : ℕ → ℕ}
    (hP : Decides ε P R) (hN : NumericalComputes N n) :
    Decides ε (boundedAllProgram P N) (fun z : ℕ => ∀ i < n z, R (Nat.pair z i)) := by
  classical
  let t : ℕ → ℕ := fun z => if R z then 1 else 0
  have ht : Computes ε P t := ⟨hP.1,fun z => hP.runs z⟩
  have hc := ht.boundedProduct.reindex (numericalIdentity_computes.pair hN)
  refine ⟨hc.1,fun z => ?_⟩
  have hr := hc.2 z
  simp only [Nat.unpair_pair,id_eq] at hr
  change OracleRuns ε _ z (boundedProduct t z (n z)) at hr
  have hb := boundedProduct_zero_or_one t z (n z) (fun i => by dsimp [t]; split_ifs <;> simp)
  have he : boundedProduct t z (n z) ≠ 0 ↔ ∀ i < n z, R (Nat.pair z i) := by
    rw [boundedProduct_ne_zero]
    simp [t]
  constructor
  · intro h
    simpa only [boundedAllProgram,Encodable.encode_nat,hb.resolve_left (he.mpr h)] using hr
  · intro h
    have hz : boundedProduct t z (n z) = 0 := not_not.mp (fun hn => h (he.mp hn))
    simpa only [boundedAllProgram,Encodable.encode_nat,hz] using hr

theorem UniformlyDecidable.boundedAll {ι : Type*} {ε : ι → ℕ → ℕ} {R : ι → ℕ → Prop}
    (hR : UniformlyDecidable ε R) {N : AlphaTerm} {n : ℕ → ℕ}
    (hN : NumericalComputes N n) :
    UniformlyDecidable ε (fun a z => ∀ i < n z, R a (Nat.pair z i)) := by
  obtain ⟨P,hP,hR⟩ := hR
  exact ⟨boundedAllProgram P N,
    reindexProgram_closed (relativeProductProgram_closed hP) (numericalIdentity_computes.pair hN).1,
    fun a => (hR a).boundedAll hN⟩

theorem uniformly_decidable_numerical {ι : Type*} (ε : ι → ℕ → ℕ)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) (R : ℕ → Prop)
    (hpos : ∀ n, R n → f n = 1) (hneg : ∀ n, ¬ R n → f n = 0) :
    UniformlyDecidable ε (fun _ => R) := by
  refine ⟨liftNumericalProgram F,hF.uniform.1,fun i => ⟨hF.uniform.1,fun n => ⟨?_,?_⟩⟩⟩
  · intro hn; simpa only [Encodable.encode_nat,hpos n hn] using hF.uniform.2 (ε i) n
  · intro hn; simpa only [Encodable.encode_nat,hneg n hn] using hF.uniform.2 (ε i) n

theorem uniformly_decidable_le {ι : Type*} (ε : ι → ℕ → ℕ)
    {A B : AlphaTerm} {a b : ℕ → ℕ} (hA : NumericalComputes A a) (hB : NumericalComputes B b) :
    UniformlyDecidable ε (fun _ z => a z ≤ b z) := by
  apply uniformly_decidable_numerical ε
    (hA.ifLe hB (numericalConstant_computes 1) (numericalConstant_computes 0))
  · intro z h; simp [h]
  · intro z h; simp [h]

theorem uniformly_decidable_prefix {ι : Type*} (ε : ι → ℕ → ℕ)
    {A B : AlphaTerm} {a b : ℕ → ℕ} (hA : NumericalComputes A a) (hB : NumericalComputes B b) :
    UniformlyDecidable ε
      (fun _ z => NatListCode.decode (a z) <+: NatListCode.decode (b z)) := by
  apply uniformly_decidable_numerical ε (listPrefix_computes.comp (hA.pair hB))
  · intro z h
    simpa [Nat.unpair_pair, List.IsPrefix] using h
  · intro z h
    simpa [Nat.unpair_pair, List.IsPrefix] using h

end LambdaRelative
end PolishSpaceBook
