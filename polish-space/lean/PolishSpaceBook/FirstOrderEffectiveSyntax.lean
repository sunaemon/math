module

public import PolishSpaceBook.FirstOrderEffectiveSignature
public import PolishSpaceBook.FirstOrderLambdaTests

@[expose] public section

/-! # Binding-preserving syntax over an effective first-order signature

Function and relation symbols are closed rigid tags. Only source variables
are free lambda variables, and each source quantifier is an actual lambda
binder. The argument spine retains the arity, including nullary symbols.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language
open FirstOrderLambdaEncoding (LTerm tag node connectiveCode quantifierCode)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Use the named lambda syntax codes of §{sec:lambda-syntax-codes} as finite data. Encode a source variable by the
    corresponding lambda variable and a quantifier by a tagged lambda abstraction with the same binder. Function and
    relation applications carry a constructor tag, a closed tag for the symbol code, and a finite argument list.
    Logical constructors have fixed closed tags. All binders inside canonical tags have index zero.
-/
/-- A finite argument spine ends in the closed tag nine. -/
def encodeVector : {n : ℕ} → (Fin n → LTerm) → LTerm
  | 0, _ => tag 9
  | n + 1, ts => .app (ts 0) (encodeVector (fun i : Fin n => ts i.succ))

def encodeTerm : L.Term ℕ → LTerm
  | .var x => .var x
  | .func (l := n) f ts => node 8 (.app (tag (S.functionCode ⟨n, f⟩))
      (encodeVector (fun i => encodeTerm (ts i))))

def encodeFormula : Formula L → LTerm
  | .falsum => node 0 (tag 0)
  | .equal s t => node 1 (.app (S.encodeTerm s) (S.encodeTerm t))
  | .rel (n := n) r ts => node 2 (.app (tag (S.relationCode ⟨n, r⟩))
      (encodeVector (fun i => S.encodeTerm (ts i))))
  | .binary c φ ψ => node (connectiveCode c) (.app (encodeFormula φ) (encodeFormula ψ))
  | .quant q x φ => node (quantifierCode q) (.lam x (encodeFormula φ))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Comparison of names through corresponding binders shows
    that this encoding preserves and reflects $\alpha$-equivalence, preserves free variables, and commutes with
    capture-avoiding substitution up to $\alpha$-equivalence. Thus the lambda programs for these operations in
    §{sec:appendix-lambda-computability} apply to the encoded first-order syntax.
-/
@[simp] theorem encodeVector_fv {n : ℕ} (ts : Fin n → LTerm) :
    (encodeVector ts).fv = Finset.univ.biUnion (fun i => (ts i).fv) := by
  induction n with
  | zero => simp [encodeVector]
  | succ n ih =>
    simp only [encodeVector, NamedLambda.Term.fv, ih]
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun h => h.elim (fun h => ⟨0, h⟩) (fun ⟨i, h⟩ => ⟨i.succ, h⟩),
      fun ⟨i, h⟩ => Fin.cases (fun h => Or.inl h) (fun j h => Or.inr ⟨j, h⟩) i h⟩

@[simp] theorem encodeTerm_fv (t : L.Term ℕ) : (S.encodeTerm t).fv = t.varFinset := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [encodeTerm, NamedLambda.Term.fv, Term.varFinset, ih]

@[simp] theorem encodeFormula_fv (φ : Formula L) : (S.encodeFormula φ).fv = φ.fv := by
  induction φ with
  | falsum => simp [encodeFormula, Formula.fv]
  | equal s t => simp [encodeFormula, NamedLambda.Term.fv, Formula.fv]
  | rel r ts => simp [encodeFormula, NamedLambda.Term.fv, Formula.fv]
  | binary c φ ψ ihφ ihψ => simp [encodeFormula, NamedLambda.Term.fv, Formula.fv, ihφ, ihψ]
  | quant q x φ ih => simp [encodeFormula, NamedLambda.Term.fv, Formula.fv, ih]

theorem encodeVector_nameRel_iff {n : ℕ} (R : ℕ → ℕ → Prop) (ts us : Fin n → LTerm) :
    NamedLambda.Term.NameRel R (encodeVector ts) (encodeVector us) ↔
      ∀ i, NamedLambda.Term.NameRel R (ts i) (us i) := by
  induction n with
  | zero => simp [encodeVector]
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | app hh ht =>
        intro i
        exact Fin.cases hh (fun j => (ih _ _).mp ht j) i
    · intro h
      exact .app (h 0) ((ih _ _).mpr (fun i => h i.succ))

theorem encodeTerm_nameRel {R : ℕ → ℕ → Prop} {t r : L.Term ℕ}
    (h : TermRel R t r) : NamedLambda.Term.NameRel R (S.encodeTerm t) (S.encodeTerm r) := by
  induction h with
  | var h => exact .var h
  | func f h ih =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr ⟨rfl,
      .app ((FirstOrderLambdaEncoding.tag_nameRel_iff _ _ _).mpr rfl)
        ((encodeVector_nameRel_iff _ _ _).mpr ih)⟩

theorem encodeTerm_nameRel_iff (R : ℕ → ℕ → Prop) (t r : L.Term ℕ) :
    NamedLambda.Term.NameRel R (S.encodeTerm t) (S.encodeTerm r) ↔ TermRel R t r := by
  refine ⟨?_, S.encodeTerm_nameRel⟩
  induction t generalizing r with
  | var x =>
    intro h
    cases r with
    | var y => cases h with | var hh => exact .var hh
    | func f rs => cases h
  | @func n f ts ih =>
    intro h
    cases r with
    | var y => cases h
    | @func m g rs =>
      obtain ⟨_, hp⟩ := (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mp h
      cases hp with
      | app hc ht =>
        have hs := S.functionCode_injective ((FirstOrderLambdaEncoding.tag_nameRel_iff _ _ _).mp hc)
        cases hs
        exact .func f (fun i => ih i _ ((encodeVector_nameRel_iff _ _ _).mp ht i))

theorem encodeFormula_nameRel {R : ℕ → ℕ → Prop} {φ ψ : Formula L}
    (h : Formula.NameRel R φ ψ) :
    NamedLambda.Term.NameRel R (S.encodeFormula φ) (S.encodeFormula ψ) := by
  induction h with
  | falsum =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr
        ⟨rfl, (FirstOrderLambdaEncoding.tag_nameRel_iff _ _ _).mpr rfl⟩
  | equal ht hr =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr
        ⟨rfl, .app (S.encodeTerm_nameRel ht) (S.encodeTerm_nameRel hr)⟩
  | rel r ht =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr
        ⟨rfl, .app ((FirstOrderLambdaEncoding.tag_nameRel_iff _ _ _).mpr rfl)
          ((encodeVector_nameRel_iff _ _ _).mpr (fun i => S.encodeTerm_nameRel (ht i)))⟩
  | binary c _ _ ihφ ihψ =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr
        ⟨rfl, .app ihφ ihψ⟩
  | quant q _ ih =>
    exact (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mpr ⟨rfl, .lam ih⟩

theorem encodeFormula_nameRel_iff (R : ℕ → ℕ → Prop) (φ ψ : Formula L) :
    NamedLambda.Term.NameRel R (S.encodeFormula φ) (S.encodeFormula ψ) ↔ Formula.NameRel R φ ψ := by
  refine ⟨?_, S.encodeFormula_nameRel⟩
  induction φ generalizing R ψ with
  | falsum =>
    intro h
    cases ψ with
    | falsum => exact .falsum _
    | equal => simp [encodeFormula] at h
    | rel => simp [encodeFormula] at h
    | binary c => cases c <;> simp [encodeFormula, connectiveCode] at h
    | quant q => cases q <;> simp [encodeFormula, quantifierCode] at h
  | equal s t =>
    intro h
    cases ψ with
    | falsum => simp [encodeFormula] at h
    | equal s' t' =>
      have hp := (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mp h
      cases hp.2 with
      | app hs ht =>
        exact .equal ((S.encodeTerm_nameRel_iff _ _ _).mp hs)
          ((S.encodeTerm_nameRel_iff _ _ _).mp ht)
    | rel => simp [encodeFormula] at h
    | binary c => cases c <;> simp [encodeFormula, connectiveCode] at h
    | quant q => cases q <;> simp [encodeFormula, quantifierCode] at h
  | @rel n r ts =>
    intro h
    cases ψ with
    | falsum => simp [encodeFormula] at h
    | equal => simp [encodeFormula] at h
    | @rel m r' us =>
      have hp := (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mp h
      cases hp.2 with
      | app hc ht =>
        have hs := S.relationCode_injective ((FirstOrderLambdaEncoding.tag_nameRel_iff _ _ _).mp hc)
        cases hs
        exact .rel r (fun i => (S.encodeTerm_nameRel_iff _ _ _).mp
          ((encodeVector_nameRel_iff _ _ _).mp ht i))
    | binary c => cases c <;> simp [encodeFormula, connectiveCode] at h
    | quant q => cases q <;> simp [encodeFormula, quantifierCode] at h
  | binary c φ₁ φ₂ ih₁ ih₂ =>
    intro h
    cases ψ with
    | falsum => cases c <;> simp [encodeFormula, connectiveCode] at h
    | equal => cases c <;> simp [encodeFormula, connectiveCode] at h
    | rel => cases c <;> simp [encodeFormula, connectiveCode] at h
    | binary d ψ₁ ψ₂ =>
      obtain ⟨hc, hp⟩ := (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mp h
      have := FirstOrderLambdaEncoding.connectiveCode_injective hc
      subst d
      cases hp with
      | app h₁ h₂ => exact .binary c (ih₁ _ _ h₁) (ih₂ _ _ h₂)
    | quant q => cases c <;> cases q <;> simp [encodeFormula, connectiveCode, quantifierCode] at h
  | quant q x φ ih =>
    intro h
    cases ψ with
    | falsum => cases q <;> simp [encodeFormula, quantifierCode] at h
    | equal => cases q <;> simp [encodeFormula, quantifierCode] at h
    | rel => cases q <;> simp [encodeFormula, quantifierCode] at h
    | binary c => cases q <;> cases c <;> simp [encodeFormula, connectiveCode, quantifierCode] at h
    | quant q' y ψ =>
      obtain ⟨hq, hp⟩ := (FirstOrderLambdaEncoding.node_nameRel_iff _ _ _ _ _).mp h
      have := FirstOrderLambdaEncoding.quantifierCode_injective hq
      subst q'
      cases hp with
      | lam hb => exact .quant q (ih _ _ hb)

theorem encodeFormula_alpha_iff (φ ψ : Formula L) :
    (S.encodeFormula φ).Alpha (S.encodeFormula ψ) ↔ φ.Alpha ψ := by
  rw [NamedLambda.Term.alpha_iff_renameEq, NamedLambda.Term.renameEq_iff_nameRel,
    Formula.alpha_iff_nameRel, S.encodeFormula_nameRel_iff]

theorem encodeTerm_alpha_iff (t r : L.Term ℕ) :
    (S.encodeTerm t).Alpha (S.encodeTerm r) ↔ t = r := by
  rw [NamedLambda.Term.alpha_iff_renameEq, NamedLambda.Term.renameEq_iff_nameRel,
    S.encodeTerm_nameRel_iff]
  exact ⟨TermRel.eq_eq, fun h => h ▸ TermRel.refl t⟩

theorem node_subst_renameEq {k x : ℕ} {t u r : LTerm}
    (h : NamedLambda.Term.RenameEq (t.subst x r) u) :
    NamedLambda.Term.RenameEq ((node k t).subst x r) (node k u) := by
  rw [node, NamedLambda.Term.subst_app]
  exact .app (NamedLambda.Term.renameEq_subst_not_free (tag k) r x (by simp)) h

theorem encodeVector_subst_renameEq {n : ℕ} {ts us : Fin n → LTerm} {x : ℕ} {r : LTerm}
    (h : ∀ i, NamedLambda.Term.RenameEq ((ts i).subst x r) (us i)) :
    NamedLambda.Term.RenameEq ((encodeVector ts).subst x r) (encodeVector us) := by
  induction n with
  | zero => exact NamedLambda.Term.renameEq_subst_not_free (tag 9) r x (by simp)
  | succ n ih =>
    simp only [encodeVector, NamedLambda.Term.subst_app]
    exact .app (h 0) (ih (fun i => h i.succ))

theorem encodeTerm_subst_renameEq (t r : L.Term ℕ) (x : ℕ) :
    NamedLambda.Term.RenameEq ((S.encodeTerm t).subst x (S.encodeTerm r))
      (S.encodeTerm (termSubst t x r)) := by
  induction t with
  | var y =>
    by_cases hy : y = x <;>
      simp only [encodeTerm, termSubst, Term.subst, NamedLambda.Term.subst_var, hy, ite_true, ite_false] <;>
      exact .refl _
  | func f ts ih =>
    apply node_subst_renameEq
    rw [NamedLambda.Term.subst_app]
    exact .app (NamedLambda.Term.renameEq_subst_not_free _ _ x (by simp))
      (encodeVector_subst_renameEq ih)

/-- Arbitrary compound-term substitution commutes with the binding encoding.
The fresh-name choices agree because the free-variable sets agree exactly. -/
theorem encodeFormula_subst_renameEq (φ : Formula L) (x : ℕ) (r : L.Term ℕ) :
    NamedLambda.Term.RenameEq ((S.encodeFormula φ).subst x (S.encodeTerm r))
      (S.encodeFormula (φ.subst x r)) := by
  have bounded : ∀ k (φ : Formula L) x (r : L.Term ℕ), φ.nodes ≤ k →
      NamedLambda.Term.RenameEq ((S.encodeFormula φ).subst x (S.encodeTerm r))
        (S.encodeFormula (φ.subst x r)) := by
    intro k
    induction k with
    | zero => intro φ x r h; have := φ.nodes_pos; omega
    | succ k ih =>
      intro φ x r hk
      cases φ with
      | falsum =>
        apply node_subst_renameEq
        exact NamedLambda.Term.renameEq_subst_not_free (tag 0) _ x (by simp)
      | equal s t =>
        rw [Formula.subst_equal]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app]
        exact .app (S.encodeTerm_subst_renameEq s r x) (S.encodeTerm_subst_renameEq t r x)
      | rel r' ts =>
        rw [Formula.subst_rel]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app]
        exact .app (NamedLambda.Term.renameEq_subst_not_free _ _ x (by simp))
          (encodeVector_subst_renameEq (fun i => S.encodeTerm_subst_renameEq (ts i) r x))
      | binary c φ ψ =>
        have hφ : φ.nodes ≤ k := by simp only [Formula.nodes] at hk; omega
        have hψ : ψ.nodes ≤ k := by simp only [Formula.nodes] at hk; omega
        rw [Formula.subst_binary]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app]
        exact .app (ih φ x r hφ) (ih ψ x r hψ)
      | quant q z φ =>
        have hφ : φ.nodes ≤ k := by simpa only [Formula.nodes, Nat.add_le_add_iff_right] using hk
        rw [Formula.subst_quant]
        by_cases hzx : z = x
        · rw [ite_eq_left hzx]
          apply node_subst_renameEq
          rw [NamedLambda.Term.subst_lam, ite_eq_left hzx]
          exact .refl _
        · rw [ite_eq_right hzx]
          by_cases hzr : z ∉ r.varFinset
          · rw [ite_eq_left hzr]
            apply node_subst_renameEq
            rw [NamedLambda.Term.subst_lam, ite_eq_right hzx, S.encodeTerm_fv, ite_eq_left hzr]
            exact .lam z (ih φ x r hφ)
          · rw [ite_eq_right hzr]
            apply node_subst_renameEq
            rw [NamedLambda.Term.subst_lam, ite_eq_right hzx, S.encodeTerm_fv, ite_eq_right hzr]
            simp only [encodeFormula_fv]
            let w := NamedLambda.Term.fresh (φ.fv ∪ r.varFinset ∪ {x})
            apply NamedLambda.Term.RenameEq.lam w
            exact ((ih φ z (.var w) hφ).subst_named (.refl (S.encodeTerm r)) x).trans
              (ih (φ.subst z (.var w)) x r (by simpa only [Formula.nodes_subst] using hφ))
  exact bounded φ.nodes φ x r le_rfl

theorem encodeFormula_subst_alpha (φ : Formula L) (x : ℕ) (r : L.Term ℕ) :
    ((S.encodeFormula φ).subst x (S.encodeTerm r)).Alpha (S.encodeFormula (φ.subst x r)) :=
  (NamedLambda.Term.alpha_iff_renameEq _ _).mpr (S.encodeFormula_subst_renameEq φ x r)

open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open FirstOrderLambdaEncoding.Grammar (Program)

/-- The decision is inherited from the actual lambda syntax comparator. -/
def formulaAlphaDecidable (φ ψ : Formula L) : Decidable (φ.Alpha ψ) :=
  decidable_of_iff ((S.encodeFormula φ).Alpha (S.encodeFormula ψ)) (S.encodeFormula_alpha_iff φ ψ)

theorem alphaDecisionTerm_formula (φ ψ : Formula L) :
    letI := S.formulaAlphaDecidable φ ψ
    Relation.ReflTransGen Beta
      (app (app alphaDecisionTerm (numeral (S.encodeFormula φ).code))
        (numeral (S.encodeFormula ψ).code)) (numeral (if φ.Alpha ψ then 1 else 0)) := by
  let := S.formulaAlphaDecidable φ ψ
  simpa only [S.encodeFormula_alpha_iff] using
    alphaDecisionTerm_code (S.encodeFormula φ) (S.encodeFormula ψ)

theorem freeVariableTerm_formula (φ : Formula L) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app freeVariableTerm (numeral (S.encodeFormula φ).code)) (numeral x))
      (numeral (if x ∈ φ.fv then 1 else 0)) := by
  simpa only [S.encodeFormula_fv] using freeVariableTerm_code (S.encodeFormula φ) x

theorem freeVariableTerm_term (t : L.Term ℕ) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app freeVariableTerm (numeral (S.encodeTerm t).code)) (numeral x))
      (numeral (if x ∈ t.varFinset then 1 else 0)) := by
  simpa only [S.encodeTerm_fv] using freeVariableTerm_code (S.encodeTerm t) x

/-- The explicit output is a representative of the substituted formula.
This covers arbitrary compound replacement terms and all capture cases. -/
theorem substitutionTerm_formula (φ : Formula L) (x : ℕ) (r : L.Term ℕ) :
    ∃ c : ℕ,
      Relation.ReflTransGen Beta
        (app (app (app substitutionTerm (numeral (S.encodeFormula φ).code)) (numeral x))
          (numeral (S.encodeTerm r).code)) (numeral c) ∧
      (Term.decode c).Alpha (S.encodeFormula (φ.subst x r)) := by
  refine ⟨((S.encodeFormula φ).subst x (S.encodeTerm r)).code,
    substitutionTerm_code _ _ _, ?_⟩
  simpa only [Term.decode_code] using S.encodeFormula_subst_alpha φ x r

/-- These are total programs on raw numerical codes, including ill-formed
first-order inputs. Grammar tests are separate from the binding operations. -/
theorem syntax_programs_closed :
    alphaDecisionTerm.Closed ∧ freeVariableTerm.Closed ∧ substitutionTerm.Closed :=
  ⟨alphaDecisionTerm_closed, freeVariableTerm_closed, substitutionTerm_closed⟩

theorem alphaDecisionTerm_all (m n : ℕ) : Relation.ReflTransGen Beta
    (app (app alphaDecisionTerm (numeral m)) (numeral n))
    (numeral (if (Term.decode m).Alpha (Term.decode n) then 1 else 0)) :=
  alphaDecisionTerm_apply m n

theorem substitutionTerm_all (m x r : ℕ) : Relation.ReflTransGen Beta
    (app (app (app substitutionTerm (numeral m)) (numeral x)) (numeral r))
    (numeral (((Term.decode m).subst x (Term.decode r)).code)) :=
  substitutionTerm_apply m x r

/-- The tag constructor is itself computed by a closed lambda recursor. -/
def tagStep : Program := Program.abstraction (Program.const 0) (Program.second Program.ident)

def tagCodeTerm : AlphaTerm := app (app recursorTerm (curryNumerical tagStep.term))
  (numeral (tag 0).code)

theorem tagCodeTerm_computes : NumericalComputes tagCodeTerm (fun n => (tag n).code) := by
  have hc := curryNumerical_closed tagStep.computes.1
  refine ⟨closed_app (closed_app recursorTerm_closed hc) (numeral_closed _), fun n => ?_⟩
  apply recursorTerm_apply hc (fun k => numeral (tag k).code) (fun _ => numeral_closed _)
  intro k
  exact (curryNumerical_apply tagStep.computes.1 _ _).trans
    (by simpa [tagStep, Program.abstraction, Program.const, Program.second, Program.ident,
      FirstOrderLambdaEncoding.tag, Term.code] using
      tagStep.computes.2 (Nat.pair k (tag k).code))

def tagProgram : Program := ⟨tagCodeTerm, fun n => (tag n).code, tagCodeTerm_computes⟩

namespace Coding
open FirstOrderLambdaEncoding.Grammar.Program

/-- Input is a pair of a symbol code and an already encoded argument spine. -/
def symbolPayload : Program :=
  application ⟨numericalCompose tagProgram.term (first ident).term,
    fun n => (tag n.unpair.1).code, tagProgram.computes.comp (first ident).computes⟩
    (second ident)

def nodeProgram (k : ℕ) (p : Program) : Program := application (const (tag k).code) p

def functionTerm : Program := nodeProgram 8 symbolPayload
def relationFormula : Program := nodeProgram 2 symbolPayload
def equalityFormula : Program := nodeProgram 1 (application (first ident) (second ident))
def binaryFormula (c : Connective) : Program :=
  nodeProgram (connectiveCode c) (application (first ident) (second ident))
def quantifiedFormula (q : Quantifier) : Program :=
  nodeProgram (quantifierCode q) (abstraction (first ident) (second ident))

@[simp] theorem symbolPayload_value (a b : ℕ) :
    symbolPayload.value (Nat.pair a b) = (Term.app (tag a) (Term.decode b)).code := by
  simp [symbolPayload, Program.application, first, second, ident, Term.code]

@[simp] theorem nodeProgram_value (k : ℕ) (p : Program) (n : ℕ) :
    (nodeProgram k p).value n = (node k (Term.decode (p.value n))).code := by
  simp [nodeProgram, Program.application, const, node, Term.code]

theorem functionTerm_apply (n : ℕ) (f : L.Functions n) (ts : Fin n → L.Term ℕ) :
    Relation.ReflTransGen Beta
      (app functionTerm.term (numeral (Nat.pair (S.functionCode ⟨n, f⟩)
        (encodeVector (fun i => S.encodeTerm (ts i))).code)))
      (numeral (S.encodeTerm (.func f ts)).code) := by
  simpa only [functionTerm, nodeProgram_value, symbolPayload_value, Term.decode_code, encodeTerm]
    using functionTerm.computes.2 (Nat.pair (S.functionCode ⟨n, f⟩)
      (encodeVector (fun i => S.encodeTerm (ts i))).code)

theorem relationFormula_apply (n : ℕ) (r : L.Relations n) (ts : Fin n → L.Term ℕ) :
    Relation.ReflTransGen Beta
      (app relationFormula.term (numeral (Nat.pair (S.relationCode ⟨n, r⟩)
        (encodeVector (fun i => S.encodeTerm (ts i))).code)))
      (numeral (S.encodeFormula (.rel r ts)).code) := by
  simpa only [relationFormula, nodeProgram_value, symbolPayload_value, Term.decode_code, encodeFormula]
    using relationFormula.computes.2 (Nat.pair (S.relationCode ⟨n, r⟩)
      (encodeVector (fun i => S.encodeTerm (ts i))).code)

end Coding

namespace MembershipTranslation
open ForcingFormulas (membershipLanguage)

/-- A total raw-syntax translation of the earlier membership encoding.
On its valid inputs it inserts the closed relation-symbol tag and argument
terminator required by the general effective-signature representation. -/
def translate : LTerm → LTerm
  | .var x => .var x
  | .lam x t => .lam x (translate t)
  | .app a b => if a.code = (tag 2).code then
      node 2 (.app (tag 0) (.app (Term.decode (b.code / 3).unpair.1)
        (.app (Term.decode (b.code / 3).unpair.2) (tag 9))))
    else .app (translate a) (translate b)

@[simp] theorem translate_tag (n : ℕ) : translate (tag n) = tag n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FirstOrderLambdaEncoding.tag, translate, ih]

private theorem tag_code_ne {n : ℕ} (hn : n ≠ 2) : (tag n).code ≠ (tag 2).code := by
  intro h
  have he := congrArg Term.nodes (Term.code_injective h)
  simp only [FirstOrderLambdaEncoding.tag_nodes] at he
  omega

@[simp] theorem translate_node {n : ℕ} (hn : n ≠ 2) (t : LTerm) :
    translate (node n t) = node n (translate t) := by
  simp only [node, translate, ite_eq_right (tag_code_ne hn), translate_tag]

@[simp] theorem translate_encoded_term (t : membershipLanguage.Term ℕ) :
    translate (.var (FirstOrderLambdaEncoding.termName t)) =
      membershipEffectiveSignature.encodeTerm t := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

@[simp] theorem encodeTerm_membership (t : membershipLanguage.Term ℕ) :
    membershipEffectiveSignature.encodeTerm t = .var (FirstOrderLambdaEncoding.termName t) := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

private theorem var_code_ne (x n : ℕ) : (NamedLambda.Term.var x).code ≠ (tag n).code := by
  intro h
  have he := Term.code_injective h
  cases n <;> cases he

private theorem encoded_code_ne (φ : Formula membershipLanguage) (n : ℕ) :
    (FirstOrderLambdaEncoding.encode φ).code ≠ (tag n).code := by
  intro h
  have he := Term.code_injective h
  cases φ with
  | falsum => cases n <;> cases he
  | equal => cases n <;> cases he
  | rel r ts => cases r; cases n <;> cases he
  | binary => cases n <;> cases he
  | quant => cases n <;> cases he

/-- The old encoding is connected by an explicit translation, rather than
silently identifying its binary membership payload with the new argument spine. -/
theorem translate_encode (φ : Formula membershipLanguage) :
    translate (FirstOrderLambdaEncoding.encode φ) = membershipEffectiveSignature.encodeFormula φ := by
  induction φ with
  | falsum => simp [FirstOrderLambdaEncoding.encode, encodeFormula]
  | equal s t =>
    rw [FirstOrderLambdaEncoding.encode, translate_node (by decide : 1 ≠ 2)]
    simp only [translate, ite_eq_right (var_code_ne _ _), encodeFormula, encodeTerm_membership]
  | rel r ts =>
    cases r
    change translate (node 2 (.app (.var (FirstOrderLambdaEncoding.termName (ts 0)))
      (.var (FirstOrderLambdaEncoding.termName (ts 1))))) =
      node 2 (.app (tag 0) (encodeVector (fun i => membershipEffectiveSignature.encodeTerm (ts i))))
    have hdiv (n : ℕ) : (3 * n + 1) / 3 = n := by omega
    have hvar (x : ℕ) : Term.decode (3 * x) = NamedLambda.Term.var x := Term.decode_code (.var x)
    simp only [node, translate, ite_true, encodeVector, encodeTerm_membership,
      Term.code, hdiv, Nat.unpair_pair, hvar]
    rfl
  | binary c φ ψ ihφ ihψ =>
    have hc : connectiveCode c ≠ 2 := by cases c <;> decide
    rw [FirstOrderLambdaEncoding.encode, translate_node hc]
    simp only [translate, ite_eq_right (encoded_code_ne φ 2), ihφ, ihψ, encodeFormula]
  | quant q x φ ih =>
    have hq : quantifierCode q ≠ 2 := by cases q <;> decide
    simp only [FirstOrderLambdaEncoding.encode, translate_node hq, translate, ih, encodeFormula]

open FirstOrderLambdaEncoding.Grammar.Program

def variableHandler : Program := (varCode ident).pair (varCode ident)
def field (b : Bool) (p : Program) : Program :=
  ⟨numericalCompose (syntaxFieldTerm b) p.term,
    fun n => if b then (p.value n / 3).unpair.1 else (p.value n / 3).unpair.2,
    (show NumericalComputes (syntaxFieldTerm b)
      (fun n => if b then (n / 3).unpair.1 else (n / 3).unpair.2) from
      ⟨syntaxFieldTerm_closed b, syntaxFieldTerm_apply b⟩).comp p.computes⟩

def applicationHandler : Program :=
  let a := first ident
  let b := second ident
  let old := Program.application a.first b.first
  let new := (equal a.first (const (tag 2).code)).ifZero
    (Program.application a.second b.second)
    (Coding.nodeProgram 2 (Program.application (const (tag 0).code)
      (Program.application (field true b.first)
        (Program.application (field false b.first) (const (tag 9).code)))))
  old.pair new

def abstractionHandler : Program :=
  (abstraction (first ident) (second ident).first).pair
    (abstraction (first ident) (second ident).second)

def state (t : LTerm) : ℕ := Nat.pair t.code (translate t).code

@[simp] theorem variableHandler_value (x : ℕ) : variableHandler.value x = state (.var x) := rfl
@[simp] theorem applicationHandler_value (a b : LTerm) :
    applicationHandler.value (Nat.pair (state a) (state b)) = state (.app a b) := by
  by_cases h : a.code = (tag 2).code <;>
    simp [applicationHandler, state, translate, h, first, second, ident, Program.application,
      pair, equal, ifZero, const, Coding.nodeProgram, field, node, Term.code]
@[simp] theorem abstractionHandler_value (x : ℕ) (a : LTerm) :
    abstractionHandler.value (Nat.pair x (state a)) = state (.lam x a) := by
  simp [abstractionHandler, state, translate, first, second, ident, pair, abstraction, Term.code]

def translationStateTerm : AlphaTerm := syntaxFold variableHandler.term
  (curryNumerical applicationHandler.term) (curryNumerical abstractionHandler.term)

theorem translationStateTerm_computes :
    NumericalComputes translationStateTerm (fun n => state (Term.decode n)) := by
  refine ⟨syntaxFold_closed variableHandler.computes.1
    (curryNumerical_closed applicationHandler.computes.1)
    (curryNumerical_closed abstractionHandler.computes.1), ?_⟩
  have hc (t : LTerm) : Relation.ReflTransGen Beta
      (app translationStateTerm (numeral t.code)) (numeral (state t)) := by
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
  intro n
  simpa only [Term.code_decode] using hc (Term.decode n)

def translationProgram : Program :=
  (⟨translationStateTerm, fun n => state (Term.decode n), translationStateTerm_computes⟩ : Program).second

theorem translationProgram_value (n : ℕ) :
    translationProgram.value n = (translate (Term.decode n)).code := by
  simp [translationProgram, second, state]

theorem translationProgram_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app translationProgram.term (numeral n)) (numeral (translate (Term.decode n)).code) := by
  simpa only [translationProgram_value] using translationProgram.computes.2 n

theorem translationProgram_encode (φ : Formula membershipLanguage) : Relation.ReflTransGen Beta
    (app translationProgram.term (numeral (FirstOrderLambdaEncoding.encode φ).code))
    (numeral (membershipEffectiveSignature.encodeFormula φ).code) := by
  simpa only [Term.decode_code, translate_encode] using
    translationProgram_apply (FirstOrderLambdaEncoding.encode φ).code

end MembershipTranslation

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
