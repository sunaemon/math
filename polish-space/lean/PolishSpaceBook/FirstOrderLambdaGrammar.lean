module

public import PolishSpaceBook.FirstOrderLambdaParsing
public import PolishSpaceBook.LambdaNumericalSearch
public import PolishSpaceBook.LambdaRealEquality

@[expose] public section

/-! # A total lambda recognizer for membership-formula data

The structural fold stores the original syntax code and four grammar bits.
Every component below expands into existing closed named lambda terms; the
record merely keeps each term together with its proved numerical equation.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Grammar

/-- A closed lambda term together with its numerical beta equation. -/
structure Program where
  term : AlphaTerm
  value : ℕ → ℕ
  computes : NumericalComputes term value

namespace Program

def const (n : ℕ) : Program := ⟨numericalConstant n, fun _ => n, numericalConstant_computes n⟩
def ident : Program := ⟨numericalIdentity, id, numericalIdentity_computes⟩
def first (p : Program) : Program :=
  ⟨numericalCompose (numericalProjectionTerm true) p.term,
    fun n => (p.value n).unpair.1, (projection_computes true).comp p.computes⟩
def second (p : Program) : Program :=
  ⟨numericalCompose (numericalProjectionTerm false) p.term,
    fun n => (p.value n).unpair.2, (projection_computes false).comp p.computes⟩
def pair (p q : Program) : Program :=
  ⟨pairNumerical p.term q.term, fun n => Nat.pair (p.value n) (q.value n), p.computes.pair q.computes⟩
def mul (p q : Program) : Program :=
  ⟨mulNumerical p.term q.term, fun n => p.value n * q.value n, p.computes.mul q.computes⟩
def ifZero (p q r : Program) : Program :=
  ⟨numericalIfZero p.term q.term r.term,
    fun n => if p.value n = 0 then q.value n else r.value n,
    numericalIfZero_computes p.computes q.computes r.computes⟩
def equal (p q : Program) : Program :=
  ⟨numericalCombine equalityTerm p.term q.term,
    fun n => if p.value n = q.value n then 1 else 0,
    p.computes.combine q.computes equalityTerm_closed _ equalityTerm_apply⟩
def alpha (p q : Program) : Program :=
  ⟨numericalCombine alphaDecisionTerm p.term q.term,
    fun n => if (Term.decode (p.value n)).Alpha (Term.decode (q.value n)) then 1 else 0,
    p.computes.combine q.computes alphaDecisionTerm_closed _ alphaDecisionTerm_apply⟩
def syntaxTag (p : Program) : Program :=
  ⟨numericalCompose syntaxTagTerm p.term, fun n => p.value n % 3,
    (show NumericalComputes syntaxTagTerm (· % 3) from
      ⟨syntaxTagTerm_closed, syntaxTagTerm_apply⟩).comp p.computes⟩
def varCode (p : Program) : Program :=
  ⟨numericalCompose variableCodeTerm p.term, fun n => (Term.var (p.value n)).code,
    (show NumericalComputes variableCodeTerm (fun n => (Term.var n).code) from
      ⟨variableCodeTerm_closed, variableCodeTerm_apply⟩).comp p.computes⟩
def application (p q : Program) : Program :=
  ⟨numericalCombine applicationCodeTerm p.term q.term,
    fun n => 3 * Nat.pair (p.value n) (q.value n) + 1,
    p.computes.combine q.computes (taggedPairCodeTerm_closed 1) _ (taggedPairCodeTerm_apply 1)⟩
def abstraction (p q : Program) : Program :=
  ⟨numericalCombine abstractionCodeTerm p.term q.term,
    fun n => 3 * Nat.pair (p.value n) (q.value n) + 2,
    p.computes.combine q.computes (taggedPairCodeTerm_closed 2) _ (taggedPairCodeTerm_apply 2)⟩

end Program

/-- State fields: original code, formula bit, atomic-payload bit,
binary-payload bit, quantified-payload bit. -/
def pack (c f a b q : ℕ) := Nat.pair c (Nat.pair f (Nat.pair a (Nat.pair b q)))
def code (s : ℕ) := s.unpair.1
def formula (s : ℕ) := s.unpair.2.unpair.1
def atomic (s : ℕ) := s.unpair.2.unpair.2.unpair.1
def binary (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.1
def quantified (s : ℕ) := s.unpair.2.unpair.2.unpair.2.unpair.2

@[simp] theorem code_pack (c f a b q : ℕ) : code (pack c f a b q) = c := by simp [code, pack]
@[simp] theorem formula_pack (c f a b q : ℕ) : formula (pack c f a b q) = f := by simp [formula, pack]
@[simp] theorem atomic_pack (c f a b q : ℕ) : atomic (pack c f a b q) = a := by simp [atomic, pack]
@[simp] theorem binary_pack (c f a b q : ℕ) : binary (pack c f a b q) = b := by simp [binary, pack]
@[simp] theorem quantified_pack (c f a b q : ℕ) : quantified (pack c f a b q) = q := by simp [quantified, pack]

def tagTest (c k : ℕ) : ℕ := if (Term.decode c).Alpha (tag k) then 1 else 0

def applicationFormula (a b : ℕ) : ℕ :=
  if tagTest (code a) 0 = 0 then
    if tagTest (code a) 1 = 0 then
      if tagTest (code a) 2 = 0 then
        if tagTest (code a) 3 = 0 then
          if tagTest (code a) 4 = 0 then
            if tagTest (code a) 5 = 0 then
              if tagTest (code a) 6 = 0 then
                if tagTest (code a) 7 = 0 then 0 else quantified b
              else quantified b
            else binary b
          else binary b
        else binary b
      else atomic b
    else atomic b
  else tagTest (code b) 0

def state : LTerm → ℕ
  | .var x => pack (Term.var x).code 0 0 0 0
  | .app a b => pack (Term.app a b).code (applicationFormula (state a) (state b))
      ((if a.code % 3 = 0 then 1 else 0) * (if b.code % 3 = 0 then 1 else 0))
      (formula (state a) * formula (state b)) 0
  | .lam x a => pack (Term.lam x a).code 0 0 0 (formula (state a))

@[simp] theorem code_state (t : LTerm) : code (state t) = t.code := by cases t <;> simp [state]

namespace Program

def stateCode := first
def stateFormula (p : Program) := p.second.first
def stateAtomic (p : Program) := p.second.second.first
def stateBinary (p : Program) := p.second.second.second.first
def stateQuantified (p : Program) := p.second.second.second.second
def pack (c f a b q : Program) := c.pair (f.pair (a.pair (b.pair q)))
def tagTest (p : Program) (k : ℕ) := p.alpha (const (tag k).code)

def applicationFormula (a b : Program) : Program :=
  (a.stateCode.tagTest 0).ifZero
    ((a.stateCode.tagTest 1).ifZero
      ((a.stateCode.tagTest 2).ifZero
        ((a.stateCode.tagTest 3).ifZero
          ((a.stateCode.tagTest 4).ifZero
            ((a.stateCode.tagTest 5).ifZero
              ((a.stateCode.tagTest 6).ifZero
                ((a.stateCode.tagTest 7).ifZero (const 0) b.stateQuantified)
                b.stateQuantified)
              b.stateBinary)
            b.stateBinary)
          b.stateBinary)
        b.stateAtomic)
      b.stateAtomic)
    (b.stateCode.tagTest 0)

@[simp] theorem applicationFormula_value (a b : Program) (n : ℕ) :
    (applicationFormula a b).value n = Grammar.applicationFormula (a.value n) (b.value n) := by
  simp only [applicationFormula, ifZero, tagTest, alpha, const, stateCode, first,
    stateAtomic, stateBinary, stateQuantified, second, Term.decode_code,
    Grammar.applicationFormula, Grammar.tagTest, code, atomic, binary, quantified]
  rfl

end Program

open Program in
def variableHandler : Program := Program.pack (varCode ident) (const 0) (const 0) (const 0) (const 0)
open Program in
def applicationHandler : Program :=
  let a := first ident
  let b := second ident
  Program.pack (application a.stateCode b.stateCode) (Program.applicationFormula a b)
    ((equal (syntaxTag a.stateCode) (const 0)).mul (equal (syntaxTag b.stateCode) (const 0)))
    (a.stateFormula.mul b.stateFormula) (const 0)
open Program in
def abstractionHandler : Program :=
  Program.pack (abstraction (first ident) (stateCode (second ident))) (const 0) (const 0) (const 0)
    (stateFormula (second ident))

@[simp] theorem variableHandler_value (x : ℕ) : variableHandler.value x = state (.var x) := rfl
@[simp] theorem applicationHandler_value (a b : LTerm) :
    applicationHandler.value (Nat.pair (state a) (state b)) = state (.app a b) := by
  simp [applicationHandler, Program.pack, Program.pair, Program.application,
    Program.stateCode, Program.first, Program.second, Program.ident,
    Program.mul, Program.equal, Program.syntaxTag, Program.const, Program.stateFormula,
    state, show ∀ t, (state t).unpair.1 = t.code from code_state, formula, pack, Term.code]
@[simp] theorem abstractionHandler_value (x : ℕ) (a : LTerm) :
    abstractionHandler.value (Nat.pair x (state a)) = state (.lam x a) := by
  simp [abstractionHandler, Program.pack, Program.pair, Program.abstraction,
    Program.stateCode, Program.first, Program.second, Program.ident,
    Program.const, Program.stateFormula, state, show ∀ t, (state t).unpair.1 = t.code from code_state, formula, pack, Term.code]

/-- The executable structural fold; recursive calls are on proper syntax subtrees. -/
def stateTerm : AlphaTerm := syntaxFold variableHandler.term
  (curryNumerical applicationHandler.term) (curryNumerical abstractionHandler.term)

theorem stateTerm_closed : stateTerm.Closed :=
  syntaxFold_closed variableHandler.computes.1
    (curryNumerical_closed applicationHandler.computes.1)
    (curryNumerical_closed abstractionHandler.computes.1)

theorem stateTerm_code (t : LTerm) : Relation.ReflTransGen Beta
    (app stateTerm (numeral t.code)) (numeral (state t)) := by
  apply syntaxFold_apply variableHandler.computes.1
    (curryNumerical_closed applicationHandler.computes.1)
    (curryNumerical_closed abstractionHandler.computes.1) (fun t => numeral (state t))
  · intro x; exact variableHandler.computes.2 x
  · intro a b
    exact (curryNumerical_apply applicationHandler.computes.1 _ _).trans
      (by simpa using applicationHandler.computes.2 (Nat.pair (state a) (state b)))
  · intro x a
    exact (curryNumerical_apply abstractionHandler.computes.1 _ _).trans
      (by simpa using abstractionHandler.computes.2 (Nat.pair x (state a)))

theorem stateTerm_computes : NumericalComputes stateTerm (fun n => state (Term.decode n)) :=
  ⟨stateTerm_closed, fun n => by simpa only [Term.code_decode] using stateTerm_code (Term.decode n)⟩


private theorem bit_zero (p : Prop) [Decidable p] :
    (if p then 1 else 0 : ℕ) = 0 ↔ ¬p := by by_cases h : p <;> simp [h]

/-- The formula flag of the fold agrees with the concrete recursive parser. -/
theorem formula_state (t : LTerm) :
    formula (state t) = if (parse t).isSome then 1 else 0 := by
  have aux : ∀ n (t : LTerm), t.nodes ≤ n →
      formula (state t) = if (parse t).isSome then 1 else 0 := by
    intro n
    induction n with
    | zero => intro t hn; have := t.nodes_pos; omega
    | succ n ih =>
      intro t hn
      cases t with
      | var => simp [state, parse.eq_def]
      | lam => simp [state, parse.eq_def]
      | app k p =>
        have hb (c : NamedFirstOrder.Connective) :
            binary (state p) = if (match p with
              | .app a b => do return NamedFirstOrder.Formula.binary (L := ForcingFormulas.membershipLanguage) c (← parse a) (← parse b)
              | _ => none).isSome then 1 else 0 := by
          cases p with
          | var => simp [state]
          | lam => simp [state]
          | app a b =>
            simp only [state, binary_pack]
            rw [ih a (by simp only [Term.nodes] at hn; omega),
              ih b (by simp only [Term.nodes] at hn; omega)]
            change ((if (parse a).isSome then 1 else 0) *
              (if (parse b).isSome then 1 else 0)) =
              if ((parse a).bind (fun α => (parse b).bind (fun β =>
                some (NamedFirstOrder.Formula.binary c α β)))).isSome then 1 else 0
            cases parse a <;> cases parse b <;> rfl
        have hq (q : NamedFirstOrder.Quantifier) :
            quantified (state p) = if (match p with
              | .lam x a => do return NamedFirstOrder.Formula.quant (L := ForcingFormulas.membershipLanguage) q x (← parse a)
              | _ => none).isSome then 1 else 0 := by
          cases p with
          | var => simp [state]
          | app => simp [state]
          | lam x a =>
            simp only [state, quantified_pack]
            rw [ih a (by simp only [Term.nodes] at hn; omega)]
            change (if (parse a).isSome then 1 else 0) =
              if ((parse a).bind (fun α => some (NamedFirstOrder.Formula.quant q x α))).isSome then 1 else 0
            cases parse a <;> rfl
        have heq : atomic (state p) = if (match p with
              | .app (.var x) (.var y) => some (NamedFirstOrder.Formula.equal
                  (L := ForcingFormulas.membershipLanguage) (.var x) (.var y))
              | _ => none).isSome then 1 else 0 := by
          cases p with
          | var => simp [state]
          | lam => simp [state]
          | app a b => cases a <;> cases b <;> simp [state, Term.code]
        have hmem : atomic (state p) = if (match p with
              | .app (.var x) (.var y) => some (NamedFirstOrder.Formula.rel (L := ForcingFormulas.membershipLanguage)
                  ForcingFormulas.MembershipSymbol.mem ![.var x, .var y])
              | _ => none).isSome then 1 else 0 := by
          cases p with
          | var => simp [state]
          | lam => simp [state]
          | app a b => cases a <;> cases b <;> simp [state, Term.code]
        rw [state, formula_pack, parse.eq_def]
        simp only [applicationFormula, tagTest, code_state, Term.decode_code]
        simp only [bit_zero, ite_not]
        by_cases h0 : k.Alpha (tag 0)
        · simp [h0]
        by_cases h1 : k.Alpha (tag 1)
        · simp only [h0, h1, ↓reduceIte]
          cases p <;> exact heq
        by_cases h2 : k.Alpha (tag 2)
        · simp only [h0, h1, h2, ↓reduceIte]
          cases p <;> exact hmem
        by_cases h3 : k.Alpha (tag 3)
        · simp only [h0, h1, h2, h3, ↓reduceIte]
          cases p <;> exact hb .conj
        by_cases h4 : k.Alpha (tag 4)
        · simp only [h0, h1, h2, h3, h4, ↓reduceIte]
          cases p <;> exact hb .disj
        by_cases h5 : k.Alpha (tag 5)
        · simp only [h0, h1, h2, h3, h4, h5, ↓reduceIte]
          cases p <;> exact hb .imp
        by_cases h6 : k.Alpha (tag 6)
        · simp only [h0, h1, h2, h3, h4, h5, h6, ↓reduceIte]
          cases p <;> exact hq .all
        by_cases h7 : k.Alpha (tag 7)
        · simp only [h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
          cases p <;> exact hq .ex
        simp only [h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte,
          Option.isSome_none, Bool.false_eq_true]
  exact aux t.nodes t le_rfl

/-- The closed grammar recognizer returns one exactly for well-formed formula data. -/
def formulaTerm : AlphaTerm := numericalCompose
  (Program.stateFormula Program.ident).term stateTerm

theorem formulaTerm_computes : NumericalComputes formulaTerm
    (fun n => if (parseCode n).isSome then 1 else 0) := by
  have h := (Program.stateFormula Program.ident).computes.comp stateTerm_computes
  change NumericalComputes formulaTerm (fun n => formula (state (Term.decode n))) at h
  convert h using 1
  funext n
  exact (formula_state (Term.decode n)).symm

 theorem formulaTerm_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app formulaTerm (numeral n)) (numeral (if (parseCode n).isSome then 1 else 0)) :=
  formulaTerm_computes.2 n

theorem formulaTerm_reject (n : ℕ) (h : ¬∃ φ : FOL, (Term.decode n).Alpha (encode φ)) :
    Relation.ReflTransGen Beta (app formulaTerm (numeral n)) (numeral 0) := by
  have hp := (parseCode_none_iff n).mpr h
  simpa only [hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using formulaTerm_apply n

theorem formulaTerm_encode (φ : FOL) : Relation.ReflTransGen Beta
    (app formulaTerm (numeral (encode φ).code)) (numeral 1) := by
  simpa only [parseCode_encode, Option.isSome_some, ↓reduceIte] using formulaTerm_apply (encode φ).code

end Grammar
end PolishSpaceBook.FirstOrderLambdaEncoding
