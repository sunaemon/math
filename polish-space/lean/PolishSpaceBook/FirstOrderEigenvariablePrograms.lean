module

public import PolishSpaceBook.FirstOrderEigenvariableBounds
public import PolishSpaceBook.FirstOrderLambdaContextClasses

@[expose] public section

/-! # Total lambda eigenvariable searches

The bound is computed from the numerical premise data. The programs test the
printed free-variable restrictions and compare inserted hypotheses as alpha
sets, including when the substitution output has renamed its binders.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm NamedFirstOrder
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace EigenvariablePrograms
open TemplatePrograms

namespace Program
open Grammar

def add (a b : Program) : Program := ⟨addNumerical a.term b.term,
  fun n => a.value n + b.value n, a.computes.add b.computes⟩
def isZero (a : Program) : Program := a.ifZero (Program.const 1) (Program.const 0)
def contextFree (c x : Program) : Program := TemplatePrograms.Program.binary ContextPrograms.freeTerm
  (fun x c => if ContextPrograms.hasFree x c then 1 else 0)
  ContextPrograms.freeTerm_closed ContextPrograms.freeTerm_apply x c
def formulaFree (a x : Program) : Program := TemplatePrograms.Program.binary freeVariableTerm
  (fun a x => if x ∈ (Term.decode a).fv then 1 else 0)
  freeVariableTerm_closed freeVariableTerm_apply a x

def substitute (a x t : Program) : Program :=
  ⟨numericalApply3 substitutionTerm a.term x.term t.varCode.term,
    fun n => ((Term.decode (a.value n)).subst (x.value n) (.var (t.value n))).code, by
      have h := a.computes.apply3 x.computes t.varCode.computes substitutionTerm_closed
        (fun e i d => ((Term.decode e).subst i (Term.decode d)).code) substitutionTerm_apply
      simpa only [Grammar.Program.varCode, Term.decode_code] using h⟩

def contextEqual (a b : Program) : Program := TemplatePrograms.Program.binary ContextPrograms.equalTerm
  (fun a b => if ContextPrograms.equalBit a b then 1 else 0)
  ContextPrograms.equalTerm_closed ContextPrograms.equalTerm_apply a b

def quant (k : ℕ) (x a : Program) : Program :=
  (Program.const (tag k).code).application (x.abstraction a)

@[simp] theorem quant_value (k : ℕ) (x a : Program) (n : ℕ) :
    (quant k x a).value n = (node k (.lam (x.value n) (Term.decode (a.value n)))).code := by
  simp only [quant, Grammar.Program.application, Grammar.Program.abstraction,
    Grammar.Program.const, node, Term.code, Term.code_decode]

private theorem firstValue (p : Program) (n : ℕ) : p.first.value n = (p.value n).unpair.1 := rfl
private theorem secondValue (p : Program) (n : ℕ) : p.second.value n = (p.value n).unpair.2 := rfl
private theorem identValue (n : ℕ) : Grammar.Program.ident.value n = n := rfl
private theorem mulValue (p q : Program) (n : ℕ) : (p.mul q).value n = p.value n * q.value n := rfl
private theorem zeroValue (p : Program) (n : ℕ) : (isZero p).value n = if p.value n = 0 then 1 else 0 := rfl
private theorem contextFreeValue (c x : Program) (n : ℕ) :
    (contextFree c x).value n = if ContextPrograms.hasFree (x.value n) (c.value n) then 1 else 0 := rfl
private theorem formulaFreeValue (a x : Program) (n : ℕ) :
    (formulaFree a x).value n = if x.value n ∈ (Term.decode (a.value n)).fv then 1 else 0 := rfl
private theorem contextEqualValue (a b : Program) (n : ℕ) :
    (contextEqual a b).value n = if ContextPrograms.equalBit (a.value n) (b.value n) then 1 else 0 := rfl
private theorem substituteValue (a x t : Program) (n : ℕ) :
    (substitute a x t).value n = ((Term.decode (a.value n)).subst (x.value n) (.var (t.value n))).code := rfl
private theorem consValue (a b : Program) (n : ℕ) :
    (TemplatePrograms.Program.cons a b).value n = Nat.pair (a.value n) (b.value n) + 1 := rfl

end Program

def allInput (c a b : ℕ) := Nat.pair c (Nat.pair a b)

def allTest : Grammar.Program :=
  let p := Grammar.Program.ident.first
  let x := Grammar.Program.ident.second
  let c := p.first
  let a := p.second.first
  let b := p.second.second
  (Program.isZero (Program.contextFree c x)).mul ((Program.quant 6 x a).alpha b)

theorem allTest_formula (Γ : List FOL) (φ ψ : FOL) (x : ℕ) :
    allTest.value (Nat.pair (allInput (ContextPrograms.listCode Γ) (encode φ).code (encode ψ).code) x) ≠ 0 ↔
      allIntroWitness Γ φ ψ x := by
  simp only [allTest, Grammar.Program.mul, Program.isZero, Grammar.Program.ifZero,
    Grammar.Program.const, Program.contextFree, TemplatePrograms.Program.binary,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq,
    allInput, Nat.unpair_pair, Grammar.Program.alpha, Program.quant_value, Term.decode_code]
  have hq : (node 6 (.lam x (encode φ))).Alpha (encode ψ) ↔ (Formula.quant .all x φ).Alpha ψ :=
    by simpa only [encode, quantifierCode] using encode_alpha_iff (Formula.quant .all x φ) ψ
  simp only [ContextPrograms.hasFree_listCode, hq, allIntroWitness]
  by_cases hc : x ∈ (ContextPrograms.context Γ).fv <;>
    by_cases h : (Formula.quant .all x φ).Alpha ψ <;> simp [hc, h]

def allBound : Grammar.Program :=
  Program.add (Program.add Grammar.Program.ident.first Grammar.Program.ident.second.first)
    (Grammar.Program.const 2)

def allSearchTerm : AlphaTerm := numericalAnyProgram allTest.term allBound.term

def allSearchValue (p : ℕ) := boundedAnyBit allTest.value p (p.unpair.1 + p.unpair.2.unpair.1 + 2)

theorem allSearchTerm_computes : NumericalComputes allSearchTerm allSearchValue :=
  numericalAnyProgram_computes allTest.computes allBound.computes

theorem allSearch_formula_iff (Γ : List FOL) (φ ψ : FOL) :
    allSearchValue (allInput (ContextPrograms.listCode Γ) (encode φ).code (encode ψ).code) ≠ 0 ↔
      ∃ x, allIntroWitness Γ φ ψ x := by
  rw [allSearchValue, boundedAnyBit_ne_zero]
  simp only [allTest_formula]
  simpa only [allInput, Nat.unpair_pair, allIntroBound] using (allIntro_witness_bounded Γ φ ψ).symm

/-- Inputs are `(base-context,(second-context,(body,(conclusion,binder))))`. -/
def exInput (c d a b x : ℕ) := Nat.pair c (Nat.pair d (Nat.pair a (Nat.pair b x)))

def exTest : Grammar.Program :=
  let p := Grammar.Program.ident.first
  let y := Grammar.Program.ident.second
  let c := p.first
  let d := p.second.first
  let a := p.second.second.first
  let b := p.second.second.second.first
  let x := p.second.second.second.second
  let instanceCode := Program.substitute a x y
  let inserted := TemplatePrograms.Program.cons instanceCode c
  (Program.contextEqual d inserted).mul
    (((Program.isZero (Program.contextFree c y)).mul (Program.isZero (Program.formulaFree b y))).mul
      (Program.isZero (Program.formulaFree (Program.quant 7 x a) y)))

theorem exTest_formula (Γ Δ : List FOL) (φ χ : FOL) (x y : ℕ) :
    exTest.value (Nat.pair (exInput (ContextPrograms.listCode Γ) (ContextPrograms.listCode Δ)
      (encode φ).code (encode χ).code x) y) ≠ 0 ↔ exElimWitness Γ Δ φ χ x y := by
  simp only [exTest, Program.mulValue, Program.zeroValue, Program.contextFreeValue,
    Program.formulaFreeValue, Program.contextEqualValue, Program.substituteValue,
    Program.consValue, Program.firstValue, Program.secondValue, Program.identValue,
    exInput, Nat.unpair_pair, Program.quant_value, Term.decode_code]
  have hf : (node 7 (.lam x (encode φ))).fv = (Formula.quant .ex x φ).fv := by simpa only [encode, quantifierCode] using encode_fv (Formula.quant .ex x φ)
  simp only [ContextPrograms.equalBit_substitution, ContextPrograms.hasFree_listCode,
    encode_fv, hf, exElimWitness, Finset.mem_union, not_or]
  by_cases hc : ContextPrograms.context Δ = insert (AlphaFormula.mk (φ.subst x (.var y))) (ContextPrograms.context Γ) <;>
    by_cases hΓ : y ∈ (ContextPrograms.context Γ).fv <;>
    by_cases hχ : y ∈ χ.fv <;>
    by_cases hφ : y ∈ (Formula.quant .ex x φ).fv <;> simp [hc, hΓ, hχ, hφ, ContextPrograms.equalBit_substitution]

def exBound : Grammar.Program :=
  let c := Grammar.Program.ident.first
  let d := Grammar.Program.ident.second.first
  let a := Grammar.Program.ident.second.second.first
  let b := Grammar.Program.ident.second.second.second.first
  let x := Grammar.Program.ident.second.second.second.second
  Program.add (Program.add (Program.add (Program.add c d) b) (Program.quant 7 x a)) (Grammar.Program.const 2)

def exSearchTerm : AlphaTerm := numericalAnyProgram exTest.term exBound.term

def exSearchValue (p : ℕ) := boundedAnyBit exTest.value p (exBound.value p)

theorem exSearchTerm_computes : NumericalComputes exSearchTerm exSearchValue :=
  numericalAnyProgram_computes exTest.computes exBound.computes

theorem exSearch_formula_iff (Γ Δ : List FOL) (φ χ : FOL) (x : ℕ) :
    exSearchValue (exInput (ContextPrograms.listCode Γ) (ContextPrograms.listCode Δ)
      (encode φ).code (encode χ).code x) ≠ 0 ↔ ∃ y, exElimWitness Γ Δ φ χ x y := by
  rw [exSearchValue, boundedAnyBit_ne_zero]
  simp only [exTest_formula]
  have hb : exBound.value (exInput (ContextPrograms.listCode Γ) (ContextPrograms.listCode Δ)
      (encode φ).code (encode χ).code x) = exElimBound Γ Δ φ χ x := by
    simp only [exBound, Program.add, Program.quant_value, Grammar.Program.first, Grammar.Program.second,
      Grammar.Program.ident, Grammar.Program.const, id_eq, exInput, Nat.unpair_pair, Term.decode_code,
      exElimBound]
    rfl
  rw [hb]
  exact (exElim_witness_bounded Γ Δ φ χ x).symm

end EigenvariablePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
