module

public import PolishSpaceBook.FirstOrderEffectiveEqualityBounds
public import PolishSpaceBook.FirstOrderEffectiveGrammarTests
public import PolishSpaceBook.FirstOrderEffectiveContexts
public import PolishSpaceBook.LambdaCompactCovers

@[expose] public section

/-! # A total lambda search for general equality-elimination templates

The input supplies the two formulas and two replacement terms, but no template
or distinguished variable. The source fixes both the fresh name and the finite
search bound. Every candidate is checked by the actual formula grammar and the
two capture-avoiding substitution/alpha programs.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EqualityPrograms
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm
open FirstOrderLambdaEncoding (LTerm)
open FirstOrderLambdaEncoding.Grammar
open EqualityBounds QuantifierBounds
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency.types false

def input (a b u v : ℕ) := Nat.pair a (Nat.pair b (Nat.pair u v))

def substitute (a x t : Program) : Program :=
  ⟨numericalApply3 substitutionTerm a.term x.term t.term,
    fun n => ((Term.decode (a.value n)).subst (x.value n) (Term.decode (t.value n))).code,
    a.computes.apply3 x.computes t.computes substitutionTerm_closed _ substitutionTerm_apply⟩

def boundProgram : Program :=
  let a := Program.ident.first
  let k := QuantifierBounds.Program.add ((Program.const 3).mul a) (Program.const 3)
  let n := QuantifierBounds.Program.add ((Program.const 2).mul a) (Program.const 1)
  QuantifierBounds.Program.add (QuantifierBounds.Program.call codeBoundProgram (k.pair n)) (Program.const 1)

theorem boundProgram_value (p : ℕ) : boundProgram.value p = templateBound p.unpair.1 + 1 := by
  simp [boundProgram, QuantifierBounds.Program.add, QuantifierBounds.Program.call,
    codeBoundProgram, Program.first, Program.ident, Program.mul, Program.const, Program.pair, templateBound]

def testProgram : Program :=
  let p := Program.ident.first
  let c := Program.ident.second
  let a := p.first
  let b := p.second.first
  let u := p.second.second.first
  let v := p.second.second.second
  let z := QuantifierBounds.Program.add a (Program.const 1)
  let grammar := (QuantifierBounds.Program.call (EffectiveGrammar.formulaRecognizer S) c).equal (Program.const 1)
  grammar.mul (((substitute c z u).alpha a).mul ((substitute c z v).alpha b))

theorem testProgram_ne_zero (a b u v c : ℕ) :
    (testProgram S).value (Nat.pair (input a b u v) c) ≠ 0 ↔
      EffectiveGrammar.IsFormulaCode S c ∧
      ((Term.decode c).subst (freshName a) (Term.decode u)).Alpha (Term.decode a) ∧
      ((Term.decode c).subst (freshName a) (Term.decode v)).Alpha (Term.decode b) := by
  simp only [testProgram, Program.mul, Program.equal, Program.alpha, substitute,
    QuantifierBounds.Program.call, QuantifierBounds.Program.add, Program.first, Program.second,
    Program.ident, Program.const, input, id_eq, Nat.unpair_pair, Term.decode_code]
  have bit (p : Prop) [Decidable p] : (if p then 1 else 0 : ℕ) ≠ 0 ↔ p := by by_cases hp : p <;> simp [hp]
  simp only [Nat.mul_ne_zero_iff, bit, EffectiveGrammar.formulaRecognizer_correct, freshName]

def searchProgram : Program :=
  ⟨numericalAnyProgram (testProgram S).term boundProgram.term,
    fun p => boundedAnyBit (testProgram S).value p (boundProgram.value p),
    numericalAnyProgram_computes (testProgram S).computes boundProgram.computes⟩

theorem searchProgram_bounded_iff (a b u v : ℕ) :
    (searchProgram S).value (input a b u v) ≠ 0 ↔
      ∃ c ≤ templateBound a, EffectiveGrammar.IsFormulaCode S c ∧
      ((Term.decode c).subst (freshName a) (Term.decode u)).Alpha (Term.decode a) ∧
      ((Term.decode c).subst (freshName a) (Term.decode v)).Alpha (Term.decode b) := by
  change boundedAnyBit _ _ _ ≠ 0 ↔ _
  rw [boundedAnyBit_ne_zero, boundProgram_value]
  simp only [input, Nat.unpair_pair]
  change (∃ c < templateBound a + 1, (testProgram S).value (Nat.pair (input a b u v) c) ≠ 0) ↔ _
  simp only [Nat.lt_succ_iff, testProgram_ne_zero]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Search this finite range, check the formula grammar, and compare both actual
    substitutions with the two displayed instances. A successful candidate supplies the required rule instance;
    the bound proves that every possible rule instance is found. This includes vacuous templates and equal replacement
    terms. The existence of a bounded representative justifies the exhaustive search and does not require selecting
    an unknown template in advance.
-/
theorem searchProgram_iff {a b u v : ℕ} {A B : AlphaFormula L} {t r : L.Term ℕ}
    (ha : S.FormulaRep a A) (hb : S.FormulaRep b B)
    (hu : (Term.decode u).Alpha (S.encodeTerm t)) (hv : (Term.decode v).Alpha (S.encodeTerm r)) :
    (searchProgram S).value (input a b u v) ≠ 0 ↔
      ∃ (φ : AlphaFormula L) (x : ℕ), A = φ.subst x t ∧ B = φ.subst x r := by
  rw [searchProgram_bounded_iff]
  constructor
  · rintro ⟨c, _, ⟨φ, hφ⟩, hleft, hright⟩
    have hc : S.FormulaRep c (AlphaFormula.mk φ) := (S.formulaRep_mk_iff c φ).mpr hφ
    have hlt := S.formulaRep_substitute hc hu (freshName a)
    have hrt := S.formulaRep_substitute hc hv (freshName a)
    refine ⟨AlphaFormula.mk φ, freshName a, ?_, ?_⟩
    · exact ((S.formulaRep_alpha_iff hlt ha).mp (by simpa only [Term.decode_code] using hleft)).symm
    · exact ((S.formulaRep_alpha_iff hrt hb).mp (by simpa only [Term.decode_code] using hright)).symm
  · rintro ⟨φ, x, hA, hB⟩
    induction φ using Quotient.inductionOn with
    | _ φ =>
      change A = (AlphaFormula.mk φ).subst x t at hA
      change B = (AlphaFormula.mk φ).subst x r at hB
      have ha' : (Term.decode a).Alpha (S.encodeFormula (φ.subst x t)) :=
        (S.formulaRep_mk_iff a _).mp (by simpa only [hA, AlphaFormula.subst_mk] using ha)
      have hb' : (Term.decode b).Alpha (S.encodeFormula (φ.subst x r)) :=
        (S.formulaRep_mk_iff b _).mp (by simpa only [hB, AlphaFormula.subst_mk] using hb)
      have hleft := ((Term.Alpha.refl (S.encodeFormula φ)).subst hu x).trans
        ((S.encodeFormula_subst_alpha φ x t).trans ha'.symm)
      have hright := ((Term.Alpha.refl (S.encodeFormula φ)).subst hv x).trans
        ((S.encodeFormula_subst_alpha φ x r).trans hb'.symm)
      obtain ⟨E, hE, hbound, hEU, hEV⟩ := bounded_template x hleft hright
      have hE' : ((S.encodeFormula φ).subst x (.var (freshName a))).Alpha E := by
        simpa only [Term.code_decode] using hE
      have hf : E.Alpha (S.encodeFormula (φ.subst x (.var (freshName a)))) :=
        hE'.symm.trans (S.encodeFormula_subst_alpha φ x (.var (freshName a)))
      refine ⟨E.code, ?_, ⟨φ.subst x (.var (freshName a)), ?_⟩, ?_, ?_⟩
      · simpa only [Term.code_decode] using hbound
      · simpa only [Term.decode_code] using hf
      · simpa only [Term.code_decode, Term.decode_code] using hEU
      · simpa only [Term.code_decode, Term.decode_code] using hEV

/-- Totality is proved for every natural input, including malformed formulas. -/
theorem searchProgram_apply (p : ℕ) : Relation.ReflTransGen Beta
    (app (searchProgram S).term (numeral p)) (numeral ((searchProgram S).value p)) :=
  (searchProgram S).computes.2 p

theorem searchProgram_closed : (searchProgram S).term.Closed := (searchProgram S).computes.1

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EqualityPrograms
