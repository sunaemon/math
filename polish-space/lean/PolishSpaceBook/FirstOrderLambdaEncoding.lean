module

public import PolishSpaceBook.ForcingFormulas
public import PolishSpaceBook.FirstOrderFormulaCorrespondence
public import PolishSpaceBook.LambdaBindingCodes
public import PolishSpaceBook.LambdaCodeSubstitution

@[expose] public section

/-! # Membership formulas as binding-preserving lambda syntax data

Rigid closed constructor tags are compared as syntax, never by beta equivalence.
Formula names remain lambda variable names and quantifiers become tagged lambda
binders. This is infrastructure for checking finite sequent-labelled trees; it
does not yet decide the unannotated local inference-rule relation.
-/

namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder
open ForcingFormulas (membershipLanguage MembershipSymbol)
abbrev FOL := NamedFirstOrder.Formula membershipLanguage
abbrev LTerm := NamedLambda.Term

/-- Every constructor tag is closed and has its own number of lambda nodes. -/
def tag : ℕ → LTerm
  | 0 => .lam 0 (.var 0)
  | n + 1 => .lam 0 (tag n)

@[simp] theorem tag_fv (n : ℕ) : (tag n).fv = ∅ := by
  induction n with
  | zero => simp [tag, NamedLambda.Term.fv]
  | succ n ih => simp [tag, NamedLambda.Term.fv, ih]

@[simp] theorem tag_nodes (n : ℕ) : (tag n).nodes = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tag, NamedLambda.Term.nodes, ih]

theorem lambda_nameRel_nodes {R : ℕ → ℕ → Prop} {s t : LTerm}
    (h : NamedLambda.Term.NameRel R s t) : s.nodes = t.nodes := by
  induction h with
  | var => rfl
  | app _ _ ih₁ ih₂ => simp only [NamedLambda.Term.nodes, ih₁, ih₂]
  | lam _ ih => simp only [NamedLambda.Term.nodes, ih]

@[simp] theorem tag_nameRel_iff (R : ℕ → ℕ → Prop) (n m : ℕ) :
    NamedLambda.Term.NameRel R (tag n) (tag m) ↔ n = m := by
  constructor
  · intro h
    have := lambda_nameRel_nodes h
    simpa using this
  · rintro rfl
    exact (NamedLambda.Term.NameRel.refl (tag n)).congr (by simp)

def node (k : ℕ) (t : LTerm) : LTerm := .app (tag k) t

@[simp] theorem node_fv (k : ℕ) (t : LTerm) : (node k t).fv = t.fv := by
  simp [node, NamedLambda.Term.fv]

@[simp] theorem node_nameRel_iff (R : ℕ → ℕ → Prop) (k l : ℕ) (s t : LTerm) :
    NamedLambda.Term.NameRel R (node k s) (node l t) ↔
      k = l ∧ NamedLambda.Term.NameRel R s t := by
  constructor
  · intro h
    cases h with
    | app ht hs => exact ⟨(tag_nameRel_iff _ _ _).mp ht, hs⟩
  · rintro ⟨rfl, h⟩
    exact .app ((tag_nameRel_iff _ _ _).mpr rfl) h

def termName : membershipLanguage.Term ℕ → ℕ
  | .var x => x
  | .func f _ => nomatch f

@[simp] theorem term_var_name (t : membershipLanguage.Term ℕ) : .var (termName t) = t := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

@[simp] theorem term_varFinset (t : membershipLanguage.Term ℕ) : t.varFinset = {termName t} := by
  cases t with
  | var => rfl
  | func f _ => exact isEmptyElim f

theorem termRel_iff (R : ℕ → ℕ → Prop) (s t : membershipLanguage.Term ℕ) :
    TermRel R s t ↔ R (termName s) (termName t) := by
  rw [← term_var_name s, ← term_var_name t]
  constructor
  · intro h; cases h with | var h => exact h
  · exact TermRel.var

def connectiveCode : Connective → ℕ
  | .conj => 3
  | .disj => 4
  | .imp => 5

def quantifierCode : Quantifier → ℕ
  | .all => 6
  | .ex => 7

/-- The encoding retains the full named binding structure. -/
def encode : FOL → LTerm
  | .falsum => node 0 (tag 0)
  | .equal s t => node 1 (.app (.var (termName s)) (.var (termName t)))
  | .rel .mem ts => node 2 (.app (.var (termName (ts 0))) (.var (termName (ts 1))))
  | .binary c φ ψ => node (connectiveCode c) (.app (encode φ) (encode ψ))
  | .quant q x φ => node (quantifierCode q) (.lam x (encode φ))

/-- Closed tags add no free names, and binders remove exactly the source names. -/
@[simp] theorem encode_fv (φ : FOL) : (encode φ).fv = φ.fv := by
  induction φ with
  | falsum => simp [encode, Formula.fv]
  | equal s t => simp [encode, Formula.fv, NamedLambda.Term.fv]
  | rel r ts =>
    cases r
    simp [encode, Formula.fv, NamedLambda.Term.fv, Finset.univ_fin2]
  | binary c φ ψ ihφ ihψ => simp [encode, Formula.fv, NamedLambda.Term.fv, ihφ, ihψ]
  | quant q x φ ih => simp [encode, Formula.fv, NamedLambda.Term.fv, ih]

theorem encode_nameRel {R : ℕ → ℕ → Prop} {φ ψ : FOL}
    (h : Formula.NameRel R φ ψ) : NamedLambda.Term.NameRel R (encode φ) (encode ψ) := by
  induction h with
  | falsum => exact (node_nameRel_iff _ _ _ _ _).mpr ⟨rfl, (tag_nameRel_iff _ _ _).mpr rfl⟩
  | equal ht hr =>
    exact (node_nameRel_iff _ _ _ _ _).mpr ⟨rfl,
      .app (.var ((termRel_iff _ _ _).mp ht)) (.var ((termRel_iff _ _ _).mp hr))⟩
  | rel r ht =>
    cases r
    exact (node_nameRel_iff _ _ _ _ _).mpr ⟨rfl,
      .app (.var ((termRel_iff _ _ _).mp (ht 0))) (.var ((termRel_iff _ _ _).mp (ht 1)))⟩
  | binary c _ _ ihφ ihψ => exact (node_nameRel_iff _ _ _ _ _).mpr ⟨rfl, .app ihφ ihψ⟩
  | quant q _ ih => exact (node_nameRel_iff _ _ _ _ _).mpr ⟨rfl, .lam ih⟩

theorem connectiveCode_injective : Function.Injective connectiveCode := by
  intro c d h
  cases c <;> cases d <;> simp_all [connectiveCode]

theorem quantifierCode_injective : Function.Injective quantifierCode := by
  intro c d h
  cases c <;> cases d <;> simp_all [quantifierCode]

/-- Rigid tags reflect constructors, and the lambda binder relation is exactly
the relation used by the first-order alpha comparison. -/
theorem nameRel_of_encode {R : ℕ → ℕ → Prop} {φ ψ : FOL}
    (h : NamedLambda.Term.NameRel R (encode φ) (encode ψ)) : Formula.NameRel R φ ψ := by
  induction φ generalizing R ψ with
  | falsum =>
    cases ψ with
    | falsum => exact .falsum _
    | equal => simp [encode] at h
    | rel r ts => cases r; simp [encode] at h
    | binary c => cases c <;> simp [encode, connectiveCode] at h
    | quant q => cases q <;> simp [encode, quantifierCode] at h
  | equal s t =>
    cases ψ with
    | falsum => simp [encode] at h
    | equal s' t' =>
      have hp := (node_nameRel_iff _ _ _ _ _).mp h
      cases hp.2 with
      | app hs ht =>
        cases hs with
        | var hs =>
          cases ht with
          | var ht => exact .equal ((termRel_iff _ _ _).mpr hs) ((termRel_iff _ _ _).mpr ht)
    | rel r ts => cases r; simp [encode] at h
    | binary c => cases c <;> simp [encode, connectiveCode] at h
    | quant q => cases q <;> simp [encode, quantifierCode] at h
  | rel r ts =>
    cases r
    cases ψ with
    | falsum => simp [encode] at h
    | equal => simp [encode] at h
    | rel r us =>
      cases r
      have hp := (node_nameRel_iff _ _ _ _ _).mp h
      cases hp.2 with
      | app hs ht =>
        cases hs with
        | var hs =>
          cases ht with
          | var ht =>
            apply Formula.NameRel.rel (L := membershipLanguage) MembershipSymbol.mem
            intro i
            fin_cases i
            · exact (termRel_iff _ _ _).mpr hs
            · exact (termRel_iff _ _ _).mpr ht
    | binary c => cases c <;> simp [encode, connectiveCode] at h
    | quant q => cases q <;> simp [encode, quantifierCode] at h
  | binary c φ₁ φ₂ ih₁ ih₂ =>
    cases ψ with
    | falsum => cases c <;> simp [encode, connectiveCode] at h
    | equal => cases c <;> simp [encode, connectiveCode] at h
    | rel r ts => cases r; cases c <;> simp [encode, connectiveCode] at h
    | binary d ψ₁ ψ₂ =>
      obtain ⟨hc, hp⟩ := (node_nameRel_iff _ _ _ _ _).mp h
      have := connectiveCode_injective hc
      subst d
      cases hp with
      | app h₁ h₂ => exact .binary c (ih₁ h₁) (ih₂ h₂)
    | quant q => cases c <;> cases q <;> simp [encode, connectiveCode, quantifierCode] at h
  | quant q x φ ih =>
    cases ψ with
    | falsum => cases q <;> simp [encode, quantifierCode] at h
    | equal => cases q <;> simp [encode, quantifierCode] at h
    | rel r ts => cases r; cases q <;> simp [encode, quantifierCode] at h
    | binary c => cases q <;> cases c <;> simp [encode, connectiveCode, quantifierCode] at h
    | quant q' y ψ =>
      obtain ⟨hq, hp⟩ := (node_nameRel_iff _ _ _ _ _).mp h
      have := quantifierCode_injective hq
      subst q'
      cases hp with
      | lam hb => exact .quant q (ih hb)

theorem encode_nameRel_iff (R : ℕ → ℕ → Prop) (φ ψ : FOL) :
    NamedLambda.Term.NameRel R (encode φ) (encode ψ) ↔ Formula.NameRel R φ ψ :=
  ⟨nameRel_of_encode, encode_nameRel⟩

/-- The representation preserves and reflects alpha equivalence, not merely
semantic equivalence or beta conversion. -/
theorem encode_alpha_iff (φ ψ : FOL) : (encode φ).Alpha (encode ψ) ↔ φ.Alpha ψ := by
  rw [NamedLambda.Term.alpha_iff_renameEq, NamedLambda.Term.renameEq_iff_nameRel,
    Formula.alpha_iff_nameRel, encode_nameRel_iff]

theorem node_subst_renameEq {k x y : ℕ} {t u : LTerm}
    (h : NamedLambda.Term.RenameEq (t.subst x (.var y)) u) :
    NamedLambda.Term.RenameEq ((node k t).subst x (.var y)) (node k u) := by
  rw [node, NamedLambda.Term.subst_app]
  exact .app (NamedLambda.Term.renameEq_subst_not_free (tag k) (.var y) x (by simp)) h

theorem encode_term_subst (t : membershipLanguage.Term ℕ) (x y : ℕ) :
    (NamedLambda.Term.var (termName t)).subst x (.var y) =
      .var (termName (termSubst t x (.var y))) := by
  cases t with
  | var z =>
    by_cases hz : z = x <;>
      simp [termName, NamedLambda.Term.subst_var, termSubst, FirstOrder.Language.Term.subst, hz]
  | func f _ => exact isEmptyElim f

set_option backward.isDefEq.respectTransparency.types false in
/-- Capture-avoiding substitution commutes with the encoding up to alpha.
Both substitution algorithms choose the same least fresh name, because the
encoding preserves free variables. Closed tags need only be preserved up to alpha. -/
theorem encode_subst_renameEq (φ : FOL) (x y : ℕ) :
    NamedLambda.Term.RenameEq ((encode φ).subst x (.var y)) (encode (φ.subst x (.var y))) := by
  have bounded : ∀ k (φ : FOL) x y, φ.nodes ≤ k →
      NamedLambda.Term.RenameEq ((encode φ).subst x (.var y)) (encode (φ.subst x (.var y))) := by
    intro k
    induction k with
    | zero => intro φ x y h; have := φ.nodes_pos; omega
    | succ k ih =>
      intro φ x y hk
      cases φ with
      | falsum =>
        apply node_subst_renameEq
        exact NamedLambda.Term.renameEq_subst_not_free (tag 0) (.var y) x (by simp)
      | equal s t =>
        rw [Formula.subst_equal]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app, encode_term_subst, encode_term_subst]
        exact .refl _
      | rel r ts =>
        cases r
        rw [Formula.subst_rel (L := membershipLanguage)]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app, encode_term_subst, encode_term_subst]
        exact .refl _
      | binary c φ ψ =>
        have hφ : φ.nodes ≤ k := by simp only [Formula.nodes] at hk; omega
        have hψ : ψ.nodes ≤ k := by simp only [Formula.nodes] at hk; omega
        rw [Formula.subst_binary]
        apply node_subst_renameEq
        rw [NamedLambda.Term.subst_app]
        exact .app (ih φ x y hφ) (ih ψ x y hψ)
      | quant q z φ =>
        have hφ : φ.nodes ≤ k := by simpa only [Formula.nodes, Nat.add_le_add_iff_right] using hk
        rw [Formula.subst_quant]
        simp only [FirstOrder.Language.Term.varFinset]
        by_cases hzx : z = x
        · rw [ite_eq_left hzx]
          apply node_subst_renameEq
          rw [NamedLambda.Term.subst_lam, ite_eq_left hzx]
          exact .refl _
        · rw [ite_eq_right hzx]
          by_cases hzy : z ∉ ({y} : Finset ℕ)
          · rw [ite_eq_left hzy]
            apply node_subst_renameEq
            rw [NamedLambda.Term.subst_lam, ite_eq_right hzx]
            simp only [NamedLambda.Term.fv]
            rw [ite_eq_left hzy]
            exact .lam z (ih φ x y hφ)
          · rw [ite_eq_right hzy]
            apply node_subst_renameEq
            rw [NamedLambda.Term.subst_lam, ite_eq_right hzx]
            simp only [NamedLambda.Term.fv]
            rw [ite_eq_right hzy]
            simp only [encode_fv]
            let w := NamedLambda.Term.fresh (φ.fv ∪ {y} ∪ {x})
            apply NamedLambda.Term.RenameEq.lam w
            exact ((ih φ z w hφ).subst_named (.refl (.var y)) x).trans
              (ih (φ.subst z (.var w)) x y (by simpa only [Formula.nodes_subst] using hφ))
  exact bounded φ.nodes φ x y le_rfl

theorem encode_subst_alpha (φ : FOL) (x y : ℕ) :
    ((encode φ).subst x (.var y)).Alpha (encode (φ.subst x (.var y))) :=
  (NamedLambda.Term.alpha_iff_renameEq _ _).mpr (encode_subst_renameEq φ x y)

end PolishSpaceBook.FirstOrderLambdaEncoding
