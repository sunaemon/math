module

public import PolishSpaceBook.FirstOrderEffectiveSignature

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
abbrev P := FirstOrderLambdaEncoding.Grammar.Program

def field : ℕ → ℕ → ℕ
  | 0, s => s.unpair.1
  | i + 1, s => field i s.unpair.2

def pack (c tag t args fp rp tp f bf qf : ℕ) :=
  Nat.pair c (Nat.pair tag (Nat.pair t (Nat.pair args (Nat.pair fp
    (Nat.pair rp (Nat.pair tp (Nat.pair f (Nat.pair bf (Nat.pair qf 0)))))))))

def code := field 0
def tagIndexPlus1 := field 1
def termBit := field 2
def argsLenPlus1 := field 3
def functionPayloadBit := field 4
def relationPayloadBit := field 5
def termPairBit := field 6
def formulaBit := field 7
def binaryFormulaBit := field 8
def quantFormulaBit := field 9

@[simp] theorem code_pack (c tag t args fp rp tp f bf qf : ℕ) : code (pack c tag t args fp rp tp f bf qf) = c := by simp [code, field, pack]
@[simp] theorem tagIndexPlus1_pack (c tag t args fp rp tp f bf qf : ℕ) : tagIndexPlus1 (pack c tag t args fp rp tp f bf qf) = tag := by simp [tagIndexPlus1, field, pack]
@[simp] theorem termBit_pack (c tag t args fp rp tp f bf qf : ℕ) : termBit (pack c tag t args fp rp tp f bf qf) = t := by simp [termBit, field, pack]
@[simp] theorem argsLenPlus1_pack (c tag t args fp rp tp f bf qf : ℕ) : argsLenPlus1 (pack c tag t args fp rp tp f bf qf) = args := by simp [argsLenPlus1, field, pack]
@[simp] theorem functionPayloadBit_pack (c tag t args fp rp tp f bf qf : ℕ) : functionPayloadBit (pack c tag t args fp rp tp f bf qf) = fp := by simp [functionPayloadBit, field, pack]
@[simp] theorem relationPayloadBit_pack (c tag t args fp rp tp f bf qf : ℕ) : relationPayloadBit (pack c tag t args fp rp tp f bf qf) = rp := by simp [relationPayloadBit, field, pack]
@[simp] theorem termPairBit_pack (c tag t args fp rp tp f bf qf : ℕ) : termPairBit (pack c tag t args fp rp tp f bf qf) = tp := by simp [termPairBit, field, pack]
@[simp] theorem formulaBit_pack (c tag t args fp rp tp f bf qf : ℕ) : formulaBit (pack c tag t args fp rp tp f bf qf) = f := by simp [formulaBit, field, pack]
@[simp] theorem binaryFormulaBit_pack (c tag t args fp rp tp f bf qf : ℕ) : binaryFormulaBit (pack c tag t args fp rp tp f bf qf) = bf := by simp [binaryFormulaBit, field, pack]
@[simp] theorem quantFormulaBit_pack (c tag t args fp rp tp f bf qf : ℕ) : quantFormulaBit (pack c tag t args fp rp tp f bf qf) = qf := by simp [quantFormulaBit, field, pack]

def lambdaTag (x s : ℕ) :=
  if code s = (Term.var x).code then 1 else
    if tagIndexPlus1 s = 0 then 0 else tagIndexPlus1 s + 1

def symbolPayload (arity : ℕ → ℕ) (a b : ℕ) :=
  if tagIndexPlus1 a = 0 then 0 else
    if arity (tagIndexPlus1 a - 1) = 0 then 0 else
      if arity (tagIndexPlus1 a - 1) = argsLenPlus1 b then 1 else 0

def appFormula (a b : ℕ) :=
  if tagIndexPlus1 a = 1 then (if tagIndexPlus1 b = 1 then 1 else 0) else
  if tagIndexPlus1 a = 2 then termPairBit b else
  if tagIndexPlus1 a = 3 then relationPayloadBit b else
  if tagIndexPlus1 a = 4 then binaryFormulaBit b else
  if tagIndexPlus1 a = 5 then binaryFormulaBit b else
  if tagIndexPlus1 a = 6 then binaryFormulaBit b else
  if tagIndexPlus1 a = 7 then quantFormulaBit b else
  if tagIndexPlus1 a = 8 then quantFormulaBit b else 0

def state (S : EffectiveSignature L) : LTerm → ℕ
  | .var x => pack (Term.var x).code 0 1 0 0 0 0 0 0 0
  | .app A B =>
    let a := state S A
    let b := state S B
    pack (Term.app A B).code 0
      (if tagIndexPlus1 a = 9 then functionPayloadBit b else 0)
      (if termBit a = 0 then 0 else if argsLenPlus1 b = 0 then 0 else argsLenPlus1 b + 1)
      (symbolPayload S.functionArityProgram.value a b)
      (symbolPayload S.relationArityProgram.value a b)
      (termBit a * termBit b) (appFormula a b) (formulaBit a * formulaBit b) 0
  | .lam x A =>
    let a := state S A
    let t := lambdaTag x a
    pack (Term.lam x A).code t 0 (if t = 10 then 1 else 0) 0 0 0 0 0 (formulaBit a)

@[simp] theorem code_state (S : EffectiveSignature L) (A : LTerm) : code (state S A) = A.code := by
  cases A <;> simp [state]

end EffectiveGrammar
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
