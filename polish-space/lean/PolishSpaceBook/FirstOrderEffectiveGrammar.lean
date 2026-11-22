module

public import PolishSpaceBook.FirstOrderEffectiveGrammarState

@[expose] public section

/-! # Total lambda grammar folds for effective first-order signatures

The state contains numerical syntax and grammar flags only. Symbol recognition
calls the supplied, proved arity programs; recursive calls follow syntax
subtrees even when the numerical input is malformed.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open NamedLambda NamedLambda.AlphaTerm
open FirstOrderLambdaEncoding (LTerm tag)
universe u v
variable {L : FirstOrder.Language.{u,v}}
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace EffectiveGrammar

def fieldTerm : ℕ → AlphaTerm
  | 0 => numericalProjectionTerm true
  | i + 1 => numericalCompose (fieldTerm i) (numericalProjectionTerm false)

theorem fieldTerm_computes (i : ℕ) : NumericalComputes (fieldTerm i) (field i) := by
  induction i with
  | zero => exact projection_computes true
  | succ i ih => exact ih.comp (projection_computes false)

namespace Program
open FirstOrderLambdaEncoding.Grammar.Program

private theorem equal_value (p q : P) (n : ℕ) : (p.equal q).value n = if p.value n = q.value n then 1 else 0 := rfl
private theorem ifZero_value (p q r : P) (n : ℕ) : (p.ifZero q r).value n = if p.value n = 0 then q.value n else r.value n := rfl
private theorem const_value (k n : ℕ) : (const k).value n = k := rfl
private theorem ident_value (n : ℕ) : ident.value n = n := rfl
private theorem first_value (p : P) (n : ℕ) : p.first.value n = (p.value n).unpair.1 := rfl
private theorem second_value (p : P) (n : ℕ) : p.second.value n = (p.value n).unpair.2 := rfl
private theorem mul_value (p q : P) (n : ℕ) : (p.mul q).value n = p.value n * q.value n := rfl
private theorem application_value (p q : P) (n : ℕ) : (p.application q).value n = 3 * Nat.pair (p.value n) (q.value n) + 1 := rfl
private theorem abstraction_value (p q : P) (n : ℕ) : (p.abstraction q).value n = 3 * Nat.pair (p.value n) (q.value n) + 2 := rfl

def field (i : ℕ) (p : P) : P :=
  ⟨numericalCompose (fieldTerm i) p.term, fun n => EffectiveGrammar.field i (p.value n),
    (fieldTerm_computes i).comp p.computes⟩

@[simp] theorem field_value (i : ℕ) (p : P) (n : ℕ) :
    (field i p).value n = EffectiveGrammar.field i (p.value n) := rfl


def succ (p : P) : P := ⟨numericalCompose successorTerm p.term, fun n => p.value n + 1,
  successor_computes.comp p.computes⟩
def pred (p : P) : P := ⟨numericalCompose predecessorTerm p.term, fun n => p.value n - 1,
  predecessor_computes.comp p.computes⟩
def call (f p : P) : P :=
  ⟨numericalCompose f.term p.term, fun n => f.value (p.value n), f.computes.comp p.computes⟩

@[simp] theorem succ_value (p : P) (n : ℕ) : (succ p).value n = p.value n + 1 := rfl
@[simp] theorem pred_value (p : P) (n : ℕ) : (pred p).value n = p.value n - 1 := rfl
@[simp] theorem call_value (f p : P) (n : ℕ) : (call f p).value n = f.value (p.value n) := rfl

def pack (c tag t args fp rp tp f bf qf : P) : P :=
  c.pair (tag.pair (t.pair (args.pair (fp.pair (rp.pair (tp.pair (f.pair (bf.pair (qf.pair (const 0))))))))))

@[simp] theorem pack_value (c tag t args fp rp tp f bf qf : P) (n : ℕ) :
    (pack c tag t args fp rp tp f bf qf).value n = EffectiveGrammar.pack
      (c.value n) (tag.value n) (t.value n) (args.value n) (fp.value n) (rp.value n)
      (tp.value n) (f.value n) (bf.value n) (qf.value n) := by
  simp only [pack, pair, const, EffectiveGrammar.pack]

attribute [irreducible] pack

def lambdaTag (x s : P) : P :=
  ((field 0 s).equal x.varCode).ifZero
    ((field 1 s).ifZero (const 0) (succ (field 1 s))) (const 1)

@[simp] theorem lambdaTag_value (x s : P) (n : ℕ) :
    (lambdaTag x s).value n = EffectiveGrammar.lambdaTag (x.value n) (s.value n) := by
  simp only [lambdaTag, equal, ifZero, field_value, varCode, const, succ_value, EffectiveGrammar.lambdaTag,
    code, tagIndexPlus1]
  split_ifs <;> simp_all


def symbolPayload (arity a b : P) : P :=
  let symbol := field 1 a
  let ar := call arity (pred symbol)
  symbol.ifZero (const 0) (ar.ifZero (const 0) (ar.equal (field 3 b)))

@[simp] theorem symbolPayload_value (arity a b : P) (n : ℕ) :
    (symbolPayload arity a b).value n = EffectiveGrammar.symbolPayload arity.value (a.value n) (b.value n) := by
  simp only [symbolPayload, ifZero, equal, call_value, pred_value, field_value, const,
    EffectiveGrammar.symbolPayload, tagIndexPlus1, argsLenPlus1]
  rfl

attribute [irreducible] symbolPayload

def chooseEqual (p : P) (k : ℕ) (yes no : P) : P where
  term := ((p.equal (const k)).ifZero no yes).term
  value n := if p.value n = k then yes.value n else no.value n
  computes := by
    have h := ((p.equal (const k)).ifZero no yes).computes
    refine ⟨h.1, fun n => ?_⟩
    by_cases hp : p.value n = k <;>
      simpa only [ifZero_value, equal_value, const_value, hp, ite_true, ite_false,
        Nat.one_ne_zero] using h.2 n

@[simp] theorem chooseEqual_value (p : P) (k : ℕ) (yes no : P) (n : ℕ) :
    (chooseEqual p k yes no).value n = if p.value n = k then yes.value n else no.value n := rfl

attribute [irreducible] chooseEqual

def appFormula (a b : P) : P :=
  let t := field 1 a
  chooseEqual t 1 ((field 1 b).equal (const 1))
    (chooseEqual t 2 (field 6 b)
      (chooseEqual t 3 (field 5 b)
        (chooseEqual t 4 (field 8 b)
          (chooseEqual t 5 (field 8 b)
            (chooseEqual t 6 (field 8 b)
              (chooseEqual t 7 (field 9 b)
                (chooseEqual t 8 (field 9 b) (const 0))))))))

set_option backward.isDefEq.respectTransparency.types true in
@[simp] theorem appFormula_value (a b : P) (n : ℕ) :
    (appFormula a b).value n = EffectiveGrammar.appFormula (a.value n) (b.value n) := by
  rw [appFormula]
  repeat rw [chooseEqual_value]
  simp only [field_value, equal_value, const_value, EffectiveGrammar.appFormula,
    tagIndexPlus1, termPairBit, relationPayloadBit, binaryFormulaBit, quantFormulaBit]
  rfl

attribute [irreducible] appFormula

end Program

open FirstOrderLambdaEncoding.Grammar.Program in
def variableHandler : P := Program.pack ident.varCode (const 0) (const 1)
  (const 0) (const 0) (const 0) (const 0) (const 0) (const 0) (const 0)

open FirstOrderLambdaEncoding.Grammar.Program in
def applicationHandler (S : EffectiveSignature L) : P :=
  let a := ident.first
  let b := ident.second
  Program.pack ((Program.field 0 a).application (Program.field 0 b)) (const 0)
    (Program.chooseEqual (Program.field 1 a) 9 (Program.field 4 b) (const 0))
    ((Program.field 2 a).ifZero (const 0)
      ((Program.field 3 b).ifZero (const 0) (Program.succ (Program.field 3 b))))
    (Program.symbolPayload S.functionArityProgram a b)
    (Program.symbolPayload S.relationArityProgram a b)
    ((Program.field 2 a).mul (Program.field 2 b)) (Program.appFormula a b)
    ((Program.field 7 a).mul (Program.field 7 b)) (const 0)

open FirstOrderLambdaEncoding.Grammar.Program in
def abstractionHandler : P :=
  let x := ident.first
  let a := ident.second
  let t := Program.lambdaTag x a
  Program.pack (x.abstraction (Program.field 0 a)) t (const 0)
    (t.equal (const 10)) (const 0) (const 0) (const 0) (const 0) (const 0) (Program.field 7 a)

@[simp] theorem variableHandler_value (S : EffectiveSignature L) (x : ℕ) :
    variableHandler.value x = state S (.var x) := by
  simp only [variableHandler, Program.pack_value, FirstOrderLambdaEncoding.Grammar.Program.varCode,
    Program.const_value, Program.ident_value, state]

set_option backward.isDefEq.respectTransparency.types true in
@[simp] theorem applicationHandler_value (S : EffectiveSignature L) (A B : LTerm) :
    (applicationHandler S).value (Nat.pair (state S A) (state S B)) = state S (.app A B) := by
  rw [applicationHandler, Program.pack_value]
  simp only [Program.symbolPayload_value, Program.appFormula_value, Program.chooseEqual_value,
    Program.field_value, Program.succ_value, Program.application_value, Program.const_value,
    Program.ifZero_value, Program.mul_value, Program.first_value, Program.second_value,
    Program.ident_value, Nat.unpair_pair, state,
    show ∀ A, field 0 (state S A) = A.code from code_state S,
    termBit, argsLenPlus1, tagIndexPlus1, functionPayloadBit, formulaBit, Term.code]
  rfl

@[simp] theorem abstractionHandler_value (S : EffectiveSignature L) (x : ℕ) (A : LTerm) :
    abstractionHandler.value (Nat.pair x (state S A)) = state S (.lam x A) := by
  simp only [abstractionHandler, Program.pack_value, Program.lambdaTag_value,
    Program.field_value, Program.abstraction_value,
    Program.const_value,
    Program.equal_value,
    Program.first_value,
    Program.second_value,
    Program.ident_value, Nat.unpair_pair,
    state, show ∀ A, field 0 (state S A) = A.code from code_state S, formulaBit, Term.code]

attribute [irreducible] variableHandler applicationHandler abstractionHandler

def stateTerm (S : EffectiveSignature L) : AlphaTerm := syntaxFold variableHandler.term
  (curryNumerical (applicationHandler S).term) (curryNumerical abstractionHandler.term)

theorem stateTerm_closed (S : EffectiveSignature L) : (stateTerm S).Closed :=
  syntaxFold_closed variableHandler.computes.1
    (curryNumerical_closed (applicationHandler S).computes.1)
    (curryNumerical_closed abstractionHandler.computes.1)

theorem stateTerm_code (S : EffectiveSignature L) (A : LTerm) : Relation.ReflTransGen Beta
    (app (stateTerm S) (numeral A.code)) (numeral (state S A)) := by
  apply syntaxFold_apply variableHandler.computes.1
    (curryNumerical_closed (applicationHandler S).computes.1)
    (curryNumerical_closed abstractionHandler.computes.1) (fun A => numeral (state S A))
  · intro x
    simpa only [variableHandler_value S] using variableHandler.computes.2 x
  · intro A B
    exact (curryNumerical_apply (applicationHandler S).computes.1 _ _).trans
      (by simpa only [applicationHandler_value] using (applicationHandler S).computes.2 (Nat.pair (state S A) (state S B)))
  · intro x A
    exact (curryNumerical_apply abstractionHandler.computes.1 _ _).trans
      (by simpa only [abstractionHandler_value] using abstractionHandler.computes.2 (Nat.pair x (state S A)))

theorem stateTerm_computes (S : EffectiveSignature L) :
    NumericalComputes (stateTerm S) (fun n => state S (Term.decode n)) :=
  ⟨stateTerm_closed S, fun n => by simpa only [Term.code_decode] using stateTerm_code S (Term.decode n)⟩

def recognizer (S : EffectiveSignature L) (i : ℕ) : P :=
  ⟨numericalCompose (fieldTerm i) (stateTerm S), fun n => field i (state S (Term.decode n)),
    (fieldTerm_computes i).comp (stateTerm_computes S)⟩

theorem recognizer_computes (S : EffectiveSignature L) (i : ℕ) :
    NumericalComputes (recognizer S i).term (fun n => field i (state S (Term.decode n))) :=
  (fieldTerm_computes i).comp (stateTerm_computes S)

@[simp] theorem recognizer_value (S : EffectiveSignature L) (i n : ℕ) :
    (recognizer S i).value n = field i (state S (Term.decode n)) := rfl

attribute [irreducible] recognizer

def termRecognizer (S : EffectiveSignature L) : P := recognizer S 2
def formulaRecognizer (S : EffectiveSignature L) : P := recognizer S 7

@[simp] theorem termRecognizer_value (S : EffectiveSignature L) (n : ℕ) :
    (termRecognizer S).value n = termBit (state S (Term.decode n)) := recognizer_value S 2 n
@[simp] theorem formulaRecognizer_value (S : EffectiveSignature L) (n : ℕ) :
    (formulaRecognizer S).value n = formulaBit (state S (Term.decode n)) := recognizer_value S 7 n

theorem termRecognizer_apply (S : EffectiveSignature L) (n : ℕ) : Relation.ReflTransGen Beta
    (app (termRecognizer S).term (numeral n)) (numeral (termBit (state S (Term.decode n)))) :=
  (recognizer_computes S 2).2 n
theorem formulaRecognizer_apply (S : EffectiveSignature L) (n : ℕ) : Relation.ReflTransGen Beta
    (app (formulaRecognizer S).term (numeral n)) (numeral (formulaBit (state S (Term.decode n)))) :=
  (recognizer_computes S 7).2 n

end EffectiveGrammar
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
