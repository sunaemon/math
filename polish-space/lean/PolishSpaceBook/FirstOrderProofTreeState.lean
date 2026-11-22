module

public import PolishSpaceBook.FirstOrderProofTreeProgram

@[expose] public section

/-! # Exact numerical state equations for the proof-tree lambda fold

These projections unfold the implemented handlers. In particular, the local
acceptance component is the actual seventeen-clause numerical program.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
open NamedLambda
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency.types false

def code (s : ℕ) := s.unpair.1
def rootSeq (s : ℕ) := s.unpair.2.unpair.2.unpair.1
def listBit (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.1
def rootList (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
def payloadBit (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
def payloadRoot (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2

def validSeq (n : ℕ) := (LocalRulePrograms.Program.validSequent Grammar.Program.ident).value n

@[simp] theorem code_pack (c t r l rs p pr : ℕ) : code (pack c t r l rs p pr) = c := by simp [code, pack]
@[simp] theorem treeBit_pack (c t r l rs p pr : ℕ) : treeBit (pack c t r l rs p pr) = t := by simp [treeBit, pack]
@[simp] theorem rootSeq_pack (c t r l rs p pr : ℕ) : rootSeq (pack c t r l rs p pr) = r := by simp [rootSeq, pack]
@[simp] theorem listBit_pack (c t r l rs p pr : ℕ) : listBit (pack c t r l rs p pr) = l := by simp [listBit, pack]
@[simp] theorem rootList_pack (c t r l rs p pr : ℕ) : rootList (pack c t r l rs p pr) = rs := by simp [rootList, pack]
@[simp] theorem payloadBit_pack (c t r l rs p pr : ℕ) : payloadBit (pack c t r l rs p pr) = p := by simp [payloadBit, pack]
@[simp] theorem payloadRoot_pack (c t r l rs p pr : ℕ) : payloadRoot (pack c t r l rs p pr) = pr := by simp [payloadRoot, pack]

namespace Program
@[simp] theorem pack_value (c t r l rs p pr : P) (n : ℕ) :
    (pack c t r l rs p pr).value n = ProofTreeProgram.pack
      (c.value n) (t.value n) (r.value n) (l.value n) (rs.value n) (p.value n) (pr.value n) := rfl
@[simp] theorem code_value (p : P) (n : ℕ) : (code p).value n = ProofTreeProgram.code (p.value n) := rfl
@[simp] theorem tree_value (p : P) (n : ℕ) : (tree p).value n = treeBit (p.value n) := rfl
@[simp] theorem root_value (p : P) (n : ℕ) : (root p).value n = rootSeq (p.value n) := rfl
@[simp] theorem listBit_value (p : P) (n : ℕ) : (listBit p).value n = ProofTreeProgram.listBit (p.value n) := rfl
@[simp] theorem roots_value (p : P) (n : ℕ) : (roots p).value n = rootList (p.value n) := rfl
@[simp] theorem payloadBit_value (p : P) (n : ℕ) : (payloadBit p).value n = ProofTreeProgram.payloadBit (p.value n) := by
  simp only [payloadBit, Grammar.Program.first, Grammar.Program.second, ProofTreeProgram.payloadBit]
@[simp] theorem payloadRoot_value (p : P) (n : ℕ) : (payloadRoot p).value n = ProofTreeProgram.payloadRoot (p.value n) := by
  simp only [payloadRoot, Grammar.Program.second, ProofTreeProgram.payloadRoot]
@[simp] theorem ruleCheck_value (p : P) (n : ℕ) :
    (ruleCheck p).value n = LocalRulePrograms.checker.value (p.value n) := rfl
end Program

theorem validSequent_value (p : P) (n : ℕ) :
    (LocalRulePrograms.Program.validSequent p).value n = validSeq (p.value n) := rfl

theorem state_var (x : ℕ) : state (.var x) = pack (Term.var x).code 0 0
    (if x = 0 then 1 else 0) 0 0 0 := rfl

theorem state_lam_raw (x : ℕ) (A : LTerm) : state (.lam x A) =
    pack (3 * Nat.pair x (code (state A)) + 2) 0 0 0 0 0 0 := by
  simp [state, abstractionHandler, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, Grammar.Program.abstraction, Grammar.Program.const]

theorem state_app_raw (A B : LTerm) : state (.app A B) =
    pack (3 * Nat.pair (code (state A)) (code (state B)) + 1)
      ((if (Term.decode (code (state A))).Alpha (tag 8) then 1 else 0) * payloadBit (state B))
      (payloadRoot (state B))
      (treeBit (state A) * listBit (state B))
      (Nat.pair (rootSeq (state A)) (rootList (state B)) + 1)
      ((if code (state A) % 3 = 0 then 1 else 0) *
        (listBit (state B) * (validSeq (code (state A) / 3) *
          (LocalRulePrograms.checker.value (Nat.pair (code (state A) / 3) (rootList (state B))) * 1))))
      (code (state A) / 3) := by
  simp only [state, applicationHandler, Program.pack_value,
    Grammar.Program.application, Grammar.Program.mul, Program.code_value,
    Program.tree_value, Program.root_value, Program.listBit_value, Program.roots_value,
    Program.payloadBit_value, Program.payloadRoot_value, Grammar.Program.alpha,
    Grammar.Program.const, Term.decode_code, LocalRulePrograms.Program.all,
    List.foldr_cons, List.foldr_nil, Grammar.Program.equal, Grammar.Program.syntaxTag,
    validSequent_value, Program.ruleCheck_value, Grammar.Program.pair,
    LocalRulePrograms.Program.payload, LocalRulePrograms.Program.call,
    TemplatePrograms.Program.cons, TemplatePrograms.Program.binary,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair]

@[simp] theorem code_state (A : LTerm) : code (state A) = A.code := by
  induction A with
  | var x => simp [state_var]
  | app A B ihA ihB => simp [state_app_raw, ihA, ihB, Term.code]
  | lam x A ih => simp [state_lam_raw, ih, Term.code]

theorem state_lam (x : ℕ) (A : LTerm) : state (.lam x A) = pack (Term.lam x A).code 0 0 0 0 0 0 := by
  simp [state_lam_raw, Term.code]

theorem state_app (A B : LTerm) : state (.app A B) =
    pack (Term.app A B).code
      ((if A.Alpha (tag 8) then 1 else 0) * payloadBit (state B))
      (payloadRoot (state B))
      (treeBit (state A) * listBit (state B))
      (Nat.pair (rootSeq (state A)) (rootList (state B)) + 1)
      ((if A.code % 3 = 0 then 1 else 0) * listBit (state B) * validSeq (A.code / 3) *
        LocalRulePrograms.checker.value (Nat.pair (A.code / 3) (rootList (state B))))
      (A.code / 3) := by
  simp [state_app_raw, Term.code, Nat.mul_assoc]

@[simp] theorem treeBit_state_var (x : ℕ) : treeBit (state (.var x)) = 0 := by rw [state_var, treeBit_pack]
@[simp] theorem rootSeq_state_var (x : ℕ) : rootSeq (state (.var x)) = 0 := by rw [state_var, rootSeq_pack]
@[simp] theorem listBit_state_var (x : ℕ) : listBit (state (.var x)) = if x = 0 then 1 else 0 := by rw [state_var, listBit_pack]
@[simp] theorem rootList_state_var (x : ℕ) : rootList (state (.var x)) = 0 := by rw [state_var, rootList_pack]
@[simp] theorem payloadBit_state_var (x : ℕ) : payloadBit (state (.var x)) = 0 := by rw [state_var, payloadBit_pack]
@[simp] theorem payloadRoot_state_var (x : ℕ) : payloadRoot (state (.var x)) = 0 := by rw [state_var, payloadRoot_pack]

@[simp] theorem treeBit_state_lam (x : ℕ) (A : LTerm) : treeBit (state (.lam x A)) = 0 := by rw [state_lam, treeBit_pack]
@[simp] theorem rootSeq_state_lam (x : ℕ) (A : LTerm) : rootSeq (state (.lam x A)) = 0 := by rw [state_lam, rootSeq_pack]
@[simp] theorem listBit_state_lam (x : ℕ) (A : LTerm) : listBit (state (.lam x A)) = 0 := by rw [state_lam, listBit_pack]
@[simp] theorem rootList_state_lam (x : ℕ) (A : LTerm) : rootList (state (.lam x A)) = 0 := by rw [state_lam, rootList_pack]
@[simp] theorem payloadBit_state_lam (x : ℕ) (A : LTerm) : payloadBit (state (.lam x A)) = 0 := by rw [state_lam, payloadBit_pack]
@[simp] theorem payloadRoot_state_lam (x : ℕ) (A : LTerm) : payloadRoot (state (.lam x A)) = 0 := by rw [state_lam, payloadRoot_pack]

@[simp] theorem treeBit_state_app (A B : LTerm) : treeBit (state (.app A B)) =
    (if A.Alpha (tag 8) then 1 else 0) * payloadBit (state B) := by rw [state_app, treeBit_pack]
@[simp] theorem rootSeq_state_app (A B : LTerm) : rootSeq (state (.app A B)) = payloadRoot (state B) := by rw [state_app, rootSeq_pack]
@[simp] theorem listBit_state_app (A B : LTerm) : listBit (state (.app A B)) =
    treeBit (state A) * listBit (state B) := by rw [state_app, listBit_pack]
@[simp] theorem rootList_state_app (A B : LTerm) : rootList (state (.app A B)) =
    Nat.pair (rootSeq (state A)) (rootList (state B)) + 1 := by rw [state_app, rootList_pack]
@[simp] theorem payloadBit_state_app (A B : LTerm) : payloadBit (state (.app A B)) =
    (if A.code % 3 = 0 then 1 else 0) * listBit (state B) * validSeq (A.code / 3) *
      LocalRulePrograms.checker.value (Nat.pair (A.code / 3) (rootList (state B))) := by rw [state_app, payloadBit_pack]
@[simp] theorem payloadRoot_state_app (A B : LTerm) : payloadRoot (state (.app A B)) = A.code / 3 := by rw [state_app, payloadRoot_pack]

end PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
