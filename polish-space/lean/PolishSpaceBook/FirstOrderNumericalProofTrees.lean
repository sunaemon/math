module

public import PolishSpaceBook.FirstOrderProofTreeCorrectness

@[expose] public section

/-! # The actual structural tree checker parameterized by two numerical programs

The parameters are closed lambda programs, not semantic validity assumptions.
The general-language endpoint instantiates them with its concrete sequent
recognizer and primitive-rule checker.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.NumericalProofTrees
open NamedLambda NamedLambda.AlphaTerm
open ProofTreeProgram (Data parse parseCode parse_app_tree parseCode_encode pack treeBit
  code rootSeq listBit rootList payloadBit payloadRoot)
open ProofTreeProgram
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency.types false
abbrev P := Grammar.Program
abbrev parse := ProofTreeProgram.parse
abbrev parseCode := ProofTreeProgram.parseCode

structure Config where
  sequent : P
  rule : P

def call (q p : P) : P :=
  ⟨numericalCompose q.term p.term, fun n => q.value (p.value n), q.computes.comp p.computes⟩

def variableHandler : P := ProofTreeProgram.variableHandler
def abstractionHandler : P := ProofTreeProgram.abstractionHandler

def applicationHandler (C : Config) : P :=
  let a := Grammar.Program.ident.first
  let b := Grammar.Program.ident.second
  let seq := LocalRulePrograms.Program.payload (Program.code a)
  let nodePayload := LocalRulePrograms.Program.all
    [(Program.code a).syntaxTag.equal (Grammar.Program.const 0), Program.listBit b,
      call C.sequent seq, call C.rule (seq.pair (Program.roots b))]
  Program.pack ((Program.code a).application (Program.code b))
    (((Program.code a).alpha (Grammar.Program.const (tag 8).code)).mul (Program.payloadBit b))
    (Program.payloadRoot b)
    ((Program.tree a).mul (Program.listBit b))
    (TemplatePrograms.Program.cons (Program.root a) (Program.roots b))
    nodePayload seq

def state (C : Config) : LTerm → ℕ
  | .var x => variableHandler.value x
  | .app A B => (applicationHandler C).value (Nat.pair (state C A) (state C B))
  | .lam x A => abstractionHandler.value (Nat.pair x (state C A))

def validSeq (C : Config) (n : ℕ) := C.sequent.value n

variable (C : Config)
theorem state_var (x : ℕ) : state C (.var x) = pack (Term.var x).code 0 0
    (if x = 0 then 1 else 0) 0 0 0 := rfl

theorem state_lam_raw (x : ℕ) (A : LTerm) : state C (.lam x A) =
    pack (3 * Nat.pair x (code (state C A)) + 2) 0 0 0 0 0 0 := by
  simp [state, abstractionHandler, ProofTreeProgram.abstractionHandler, Grammar.Program.first, Grammar.Program.second,
    Grammar.Program.ident, Grammar.Program.abstraction, Grammar.Program.const]

theorem state_app_raw (A B : LTerm) : state C (.app A B) =
    pack (3 * Nat.pair (code (state C A)) (code (state C B)) + 1)
      ((if (Term.decode (code (state C A))).Alpha (tag 8) then 1 else 0) * payloadBit (state C B))
      (payloadRoot (state C B))
      (treeBit (state C A) * listBit (state C B))
      (Nat.pair (rootSeq (state C A)) (rootList (state C B)) + 1)
      ((if code (state C A) % 3 = 0 then 1 else 0) *
        (listBit (state C B) * (validSeq C (code (state C A) / 3) *
          (C.rule.value (Nat.pair (code (state C A) / 3) (rootList (state C B))) * 1))))
      (code (state C A) / 3) := by
  simp only [state, applicationHandler, Program.pack_value,
    Grammar.Program.application, Grammar.Program.mul, Program.code_value,
    Program.tree_value, Program.root_value, Program.listBit_value, Program.roots_value,
    Program.payloadBit_value, Program.payloadRoot_value, Grammar.Program.alpha,
    Grammar.Program.const, Term.decode_code, LocalRulePrograms.Program.all,
    List.foldr_cons, List.foldr_nil, Grammar.Program.equal, Grammar.Program.syntaxTag,
    call, validSeq, Grammar.Program.pair,
    LocalRulePrograms.Program.payload, LocalRulePrograms.Program.call,
    TemplatePrograms.Program.cons, TemplatePrograms.Program.binary,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair]

@[simp] theorem code_state (A : LTerm) : code (state C A) = A.code := by
  induction A with
  | var x => simp [state_var]
  | app A B ihA ihB => simp [state_app_raw, ihA, ihB, Term.code]
  | lam x A ih => simp [state_lam_raw, ih, Term.code]

theorem state_lam (x : ℕ) (A : LTerm) : state C (.lam x A) = pack (Term.lam x A).code 0 0 0 0 0 0 := by
  simp [state_lam_raw, Term.code]

theorem state_app (A B : LTerm) : state C (.app A B) =
    pack (Term.app A B).code
      ((if A.Alpha (tag 8) then 1 else 0) * payloadBit (state C B))
      (payloadRoot (state C B))
      (treeBit (state C A) * listBit (state C B))
      (Nat.pair (rootSeq (state C A)) (rootList (state C B)) + 1)
      ((if A.code % 3 = 0 then 1 else 0) * listBit (state C B) * validSeq C (A.code / 3) *
        C.rule.value (Nat.pair (A.code / 3) (rootList (state C B))))
      (A.code / 3) := by
  simp [state_app_raw, Term.code, Nat.mul_assoc]

@[simp] theorem treeBit_state_var (x : ℕ) : treeBit (state C (.var x)) = 0 := by rw [state_var, treeBit_pack]
@[simp] theorem rootSeq_state_var (x : ℕ) : rootSeq (state C (.var x)) = 0 := by rw [state_var, rootSeq_pack]
@[simp] theorem listBit_state_var (x : ℕ) : listBit (state C (.var x)) = if x = 0 then 1 else 0 := by rw [state_var, listBit_pack]
@[simp] theorem rootList_state_var (x : ℕ) : rootList (state C (.var x)) = 0 := by rw [state_var, rootList_pack]
@[simp] theorem payloadBit_state_var (x : ℕ) : payloadBit (state C (.var x)) = 0 := by rw [state_var, payloadBit_pack]
@[simp] theorem payloadRoot_state_var (x : ℕ) : payloadRoot (state C (.var x)) = 0 := by rw [state_var, payloadRoot_pack]

@[simp] theorem treeBit_state_lam (x : ℕ) (A : LTerm) : treeBit (state C (.lam x A)) = 0 := by rw [state_lam, treeBit_pack]
@[simp] theorem rootSeq_state_lam (x : ℕ) (A : LTerm) : rootSeq (state C (.lam x A)) = 0 := by rw [state_lam, rootSeq_pack]
@[simp] theorem listBit_state_lam (x : ℕ) (A : LTerm) : listBit (state C (.lam x A)) = 0 := by rw [state_lam, listBit_pack]
@[simp] theorem rootList_state_lam (x : ℕ) (A : LTerm) : rootList (state C (.lam x A)) = 0 := by rw [state_lam, rootList_pack]
@[simp] theorem payloadBit_state_lam (x : ℕ) (A : LTerm) : payloadBit (state C (.lam x A)) = 0 := by rw [state_lam, payloadBit_pack]
@[simp] theorem payloadRoot_state_lam (x : ℕ) (A : LTerm) : payloadRoot (state C (.lam x A)) = 0 := by rw [state_lam, payloadRoot_pack]

@[simp] theorem treeBit_state_app (A B : LTerm) : treeBit (state C (.app A B)) =
    (if A.Alpha (tag 8) then 1 else 0) * payloadBit (state C B) := by rw [state_app, treeBit_pack]
@[simp] theorem rootSeq_state_app (A B : LTerm) : rootSeq (state C (.app A B)) = payloadRoot (state C B) := by rw [state_app, rootSeq_pack]
@[simp] theorem listBit_state_app (A B : LTerm) : listBit (state C (.app A B)) =
    treeBit (state C A) * listBit (state C B) := by rw [state_app, listBit_pack]
@[simp] theorem rootList_state_app (A B : LTerm) : rootList (state C (.app A B)) =
    Nat.pair (rootSeq (state C A)) (rootList (state C B)) + 1 := by rw [state_app, rootList_pack]
@[simp] theorem payloadBit_state_app (A B : LTerm) : payloadBit (state C (.app A B)) =
    (if A.code % 3 = 0 then 1 else 0) * listBit (state C B) * validSeq C (A.code / 3) *
      C.rule.value (Nat.pair (A.code / 3) (rootList (state C B))) := by rw [state_app, payloadBit_pack]
@[simp] theorem payloadRoot_state_app (A B : LTerm) : payloadRoot (state C (.app A B)) = A.code / 3 := by rw [state_app, payloadRoot_pack]

def stateTerm : AlphaTerm := syntaxFold variableHandler.term
  (curryNumerical (applicationHandler C).term) (curryNumerical abstractionHandler.term)

theorem stateTerm_closed : (stateTerm C).Closed := syntaxFold_closed variableHandler.computes.1
  (curryNumerical_closed (applicationHandler C).computes.1)
  (curryNumerical_closed abstractionHandler.computes.1)

theorem stateTerm_code (M : LTerm) : Relation.ReflTransGen Beta
    (app (stateTerm C) (numeral M.code)) (numeral (state C M)) := by
  apply syntaxFold_apply variableHandler.computes.1
    (curryNumerical_closed (applicationHandler C).computes.1)
    (curryNumerical_closed abstractionHandler.computes.1) (fun M => numeral (state C M))
  · intro x; exact variableHandler.computes.2 x
  · intro A B
    exact (curryNumerical_apply (applicationHandler C).computes.1 _ _).trans
      ((applicationHandler C).computes.2 (Nat.pair (state C A) (state C B)))
  · intro x A
    exact (curryNumerical_apply abstractionHandler.computes.1 _ _).trans
      (abstractionHandler.computes.2 (Nat.pair x (state C A)))

theorem stateTerm_computes : NumericalComputes (stateTerm C) (fun n => state C (Term.decode n)) :=
  ⟨stateTerm_closed C, fun n => by simpa only [Term.code_decode] using stateTerm_code C (Term.decode n)⟩

def flagProgram : P :=
  ⟨numericalCompose (Program.tree Grammar.Program.ident).term (stateTerm C),
    fun n => treeBit (state C (Term.decode n)),
    (Program.tree Grammar.Program.ident).computes.comp (stateTerm_computes C)⟩

def checker : P := LocalRulePrograms.Program.normalize (flagProgram C)

def accepts (n : ℕ) : Prop := treeBit (state C (Term.decode n)) ≠ 0
instance acceptsDecidable (n : ℕ) : Decidable (accepts C n) := inferInstanceAs (Decidable (_ ≠ 0))

theorem checker_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app (checker C).term (numeral n)) (numeral (if accepts C n then 1 else 0)) := by
  have h := (checker C).computes.2 n
  convert h using 1
  apply congrArg numeral
  change (if accepts C n then 1 else 0 : ℕ) = if treeBit (state C (Term.decode n)) = 0 then 0 else 1
  by_cases h : treeBit (state C (Term.decode n)) = 0 <;> simp [accepts, h]

theorem checker_closed : (checker C).term.Closed := (checker C).computes.1

inductive Checked (C : Config) : Data → Prop where
  | node {s : ℕ} {cs : List Data} : validSeq C s ≠ 0 →
      C.rule.value (Nat.pair s (NatListCode.encode (cs.map Data.root))) ≠ 0 →
      (∀ c ∈ cs, Checked C c) → Checked C (.node s cs)

/-- Successful parser views retain exactly the root fields held by the fold. -/
theorem parse_fields (M : LTerm) :
    (∀ T, (parse M).tree = some T → rootSeq (state C M) = T.root) ∧
    (∀ cs, (parse M).children = some cs → rootList (state C M) = NatListCode.encode (cs.map Data.root)) ∧
    (∀ p, (parse M).payload = some p → payloadRoot (state C M) = p.1) := by
  induction M with
  | var x =>
    refine ⟨by simp [parse, ProofTreeProgram.parse], ?_, by simp [parse, ProofTreeProgram.parse]⟩
    intro cs hp
    by_cases hx : x = 0
    · simp only [parse, ProofTreeProgram.parse, hx, ↓reduceIte, Option.some.injEq] at hp
      subst cs; simp only [rootList_state_var, List.map_nil, NatListCode.encode]
    · simp [parse, ProofTreeProgram.parse, hx] at hp
  | lam x M ih => simp [parse, ProofTreeProgram.parse]
  | app A B ihA ihB =>
    refine ⟨?_, ?_, ?_⟩
    · intro T hp
      obtain ⟨_, s, cs, hs, rfl⟩ := (parse_app_tree A B T).mp hp
      exact (rootSeq_state_app C A B).trans (ihB.2.2 (s, cs) hs)
    · intro cs hp
      change ((parse A).tree.bind (fun T => (parse B).children.bind (fun ts => some (T :: ts)))) = some cs at hp
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
      obtain ⟨T, hT, ts, hts, rfl⟩ := hp
      rw [rootList_state_app, ihA.1 T hT, ihB.2.1 ts hts]
      rfl
    · intro p hp
      cases A with
      | var x =>
        change (parse B).children.map (fun cs => (x, cs)) = some p at hp
        obtain ⟨cs, _, rfl⟩ := Option.map_eq_some_iff.mp hp
        simp [Term.code]
      | app => simp [parse, ProofTreeProgram.parse] at hp
      | lam => simp [parse, ProofTreeProgram.parse] at hp

theorem tree_flag_iff (M : LTerm) :
    (treeBit (state C M) ≠ 0 ↔ ∃ T, (parse M).tree = some T ∧ Checked C T) ∧
    (listBit (state C M) ≠ 0 ↔ ∃ cs, (parse M).children = some cs ∧ ∀ c ∈ cs, Checked C c) ∧
    (payloadBit (state C M) ≠ 0 ↔ ∃ s cs, (parse M).payload = some (s, cs) ∧
      validSeq C s ≠ 0 ∧
      C.rule.value (Nat.pair s (NatListCode.encode (cs.map Data.root))) ≠ 0 ∧
      ∀ c ∈ cs, Checked C c) := by
  induction M with
  | var x =>
    by_cases hx : x = 0 <;> simp [parse, ProofTreeProgram.parse, hx]
  | lam x M ih => simp [parse, ProofTreeProgram.parse]
  | app A B ihA ihB =>
    refine ⟨?_, ?_, ?_⟩
    · rw [treeBit_state_app, mul_ne_zero_iff]
      constructor
      · rintro ⟨htag, hp⟩
        have htag' : A.Alpha (tag 8) := by by_contra h; simp [h] at htag
        obtain ⟨s, cs, hparse, hs, hr, hcs⟩ := ihB.2.2.mp hp
        refine ⟨.node s cs, (parse_app_tree A B _).mpr ⟨htag', s, cs, hparse, rfl⟩, .node hs hr hcs⟩
      · rintro ⟨T, hp, hT⟩
        obtain ⟨htag, s, cs, hPayload, rfl⟩ := (parse_app_tree A B T).mp hp
        cases hT with
        | node hs hr hcs =>
          exact ⟨by simp [htag], ihB.2.2.mpr ⟨s, cs, hPayload, hs, hr, hcs⟩⟩
    · rw [listBit_state_app, mul_ne_zero_iff]
      constructor
      · rintro ⟨ht, hl⟩
        obtain ⟨T, hpT, hT⟩ := ihA.1.mp ht
        obtain ⟨cs, hpcs, hcs⟩ := ihB.2.1.mp hl
        refine ⟨T :: cs, ?_, ?_⟩
        · change ((parse A).tree.bind (fun T => (parse B).children.bind (fun cs => some (T :: cs)))) = _
          rw [hpT, hpcs]; rfl
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hT
          · exact hcs c hc
      · rintro ⟨cs, hp, hcs⟩
        change ((parse A).tree.bind (fun T => (parse B).children.bind (fun ts => some (T :: ts)))) = some cs at hp
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
        obtain ⟨T, hT, ts, hts, rfl⟩ := hp
        exact ⟨ihA.1.mpr ⟨T, hT, hcs T (by simp)⟩,
          ihB.2.1.mpr ⟨ts, hts, fun c hc => hcs c (by simp [hc])⟩⟩
    · cases A with
      | var s =>
        rw [payloadBit_state_app]
        have hdiv : 3 * s / 3 = s := by omega
        simp only [Term.code, Nat.mul_mod_right, ↓reduceIte, hdiv,
          Nat.one_mul, mul_ne_zero_iff]
        constructor
        · rintro ⟨⟨hl, hs⟩, hr⟩
          obtain ⟨cs, hp, hcs⟩ := ihB.2.1.mp hl
          rw [(parse_fields C B).2.1 cs hp] at hr
          refine ⟨s, cs, ?_, hs, hr, hcs⟩
          change (parse B).children.map (fun cs => (s, cs)) = _
          rw [hp]; rfl
        · rintro ⟨s', cs, hp, hs, hr, hcs⟩
          change (parse B).children.map (fun cs => (s, cs)) = some (s', cs) at hp
          obtain ⟨ts, hts, he⟩ := Option.map_eq_some_iff.mp hp
          have he' : s = s' ∧ ts = cs := Prod.mk.inj he
          rcases he' with ⟨hss, htscs⟩
          subst s'
          subst ts
          rw [← (parse_fields C B).2.1 cs hts] at hr
          exact ⟨⟨ihB.2.1.mpr ⟨cs, hts, hcs⟩, hs⟩, hr⟩
      | app C D => simp [payloadBit_state_app, Term.code, parse, ProofTreeProgram.parse]
      | lam x C => simp [payloadBit_state_app, Term.code, parse, ProofTreeProgram.parse]

/-- Acceptance on arbitrary natural numbers includes successful structural parsing. -/
theorem accepts_iff_parsed_checked (n : ℕ) :
    accepts C n ↔ ∃ T, parseCode n = some T ∧ Checked C T := (tree_flag_iff C (Term.decode n)).1

/-- An invalid tree shape is rejected by the actual closed lambda program. -/
theorem checker_reject_malformed (n : ℕ) (hn : parseCode n = none) :
    Relation.ReflTransGen AlphaTerm.Beta
      (AlphaTerm.app (checker C).term (AlphaTerm.numeral n)) (AlphaTerm.numeral 0) := by
  have h : ¬accepts C n := by
    intro ha
    obtain ⟨T, hp, _⟩ := (accepts_iff_parsed_checked C n).mp ha
    simp [hn] at hp
  simpa only [h, ↓reduceIte] using checker_apply C n

/-- On the advertised finite inputs, the program checks every node and descendant. -/
theorem accepts_encode_iff (T : Data) : accepts C T.encode.code ↔ Checked C T := by
  rw [accepts_iff_parsed_checked]
  change (∃ U, ProofTreeProgram.parseCode (Data.encode T).code = some U ∧ Checked C U) ↔ Checked C T
  simp only [ProofTreeProgram.parseCode_encode, Option.some.injEq, exists_eq_left']

end PolishSpaceBook.FirstOrderLambdaEncoding.NumericalProofTrees
