module

public import PolishSpaceBook.FirstOrderRelationElimination

@[expose] public section

/-!
# Literal substitution after choosing fresh binders

This is a syntactic normal form for capture-avoiding substitution. The free
term algebra reflects term substitution as term equality; no equivalence of
formula truth values is used to identify alpha-classes.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}

/-- The free algebra of terms, used only to reflect term substitution. -/
abbrev syntaxStructure : L.Structure (L.Term ℕ) where
  funMap := Term.func
  RelMap := fun _ _ => False

section TermSyntax
local instance : L.Structure (L.Term ℕ) := syntaxStructure

theorem realize_syntax (t : L.Term ℕ) (σ : ℕ → L.Term ℕ) : t.realize σ = t.subst σ := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.realize_func, Term.subst, ih]; rfl

@[simp] theorem term_subst_var (t : L.Term ℕ) : t.subst Term.var = t := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.subst, ih]

theorem term_subst_comp (t : L.Term ℕ) (σ τ : ℕ → L.Term ℕ) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.subst, ih]

theorem term_subst_congr (t : L.Term ℕ) (σ τ : ℕ → L.Term ℕ)
    (h : ∀ x ∈ t.varFinset, σ x = τ x) : t.subst σ = t.subst τ := by
  simpa only [realize_syntax] using term_realize_congr t σ τ h

end TermSyntax

namespace Formula

/-- Literal term replacement; safe under binders only with the stated freshness conditions. -/
def literalSubst (σ : ℕ → L.Term ℕ) : Formula L → Formula L
  | .falsum => .falsum
  | .equal t r => .equal (t.subst σ) (r.subst σ)
  | .rel R ts => .rel R (fun i => (ts i).subst σ)
  | .binary c φ ψ => .binary c (literalSubst σ φ) (literalSubst σ ψ)
  | .quant q x φ => .quant q x (literalSubst σ φ)

@[simp] theorem boundNames_literalSubst (φ : Formula L) (σ : ℕ → L.Term ℕ) :
    (φ.literalSubst σ).boundNames = φ.boundNames := by
  induction φ <;> simp_all [literalSubst, boundNames]

@[simp] theorem literalSubst_var (φ : Formula L) : φ.literalSubst Term.var = φ := by
  induction φ <;> simp_all [literalSubst, term_subst_var]

theorem literalSubst_comp (φ : Formula L) (σ τ : ℕ → L.Term ℕ) :
    (φ.literalSubst σ).literalSubst τ = φ.literalSubst (fun x => (σ x).subst τ) := by
  induction φ <;> simp_all [literalSubst, term_subst_comp]

/-- If binders avoid the target and the replacement, single substitution is literal. -/
theorem subst_eq_literal (φ : Formula L) (x : ℕ) (t : L.Term ℕ)
    (h : Disjoint φ.boundNames (insert x t.varFinset)) :
    φ.subst x t = φ.literalSubst (fun y => if y = x then t else .var y) := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | binary c φ ψ ihφ ihψ =>
    have hd : Disjoint φ.boundNames (insert x t.varFinset) ∧
        Disjoint ψ.boundNames (insert x t.varFinset) := by simpa only [boundNames, Finset.disjoint_union_left] using h
    simp only [subst_binary, literalSubst, ihφ hd.1, ihψ hd.2]
  | quant q y φ ih =>
    have hd : y ∉ insert x t.varFinset ∧ Disjoint φ.boundNames (insert x t.varFinset) := by
      simpa only [boundNames, Finset.disjoint_insert_left] using h
    have hy : y ≠ x ∧ y ∉ t.varFinset := by simpa using hd.1
    simp only [subst_quant, ite_eq_right hy.1, ite_eq_left hy.2, literalSubst, ih hd.2]

/-- Literal substitution depends on all occurring names, including bound names. -/
theorem literalSubst_congr (φ : Formula L) (σ τ : ℕ → L.Term ℕ)
    (h : ∀ x ∈ φ.fv ∪ φ.boundNames, σ x = τ x) : φ.literalSubst σ = φ.literalSubst τ := by
  induction φ with
  | falsum => rfl
  | equal t r =>
    rw [literalSubst, literalSubst]
    congr 1
    · apply term_subst_congr; intro x hx
      exact h x (by simp [fv, boundNames, hx])
    · apply term_subst_congr; intro x hx
      exact h x (by simp [fv, boundNames, hx])
  | rel R ts =>
    rw [literalSubst, literalSubst]
    congr 1
    funext i
    apply term_subst_congr
    intro x hx
    apply h
    simp only [fv, boundNames, Finset.union_empty]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  | binary c φ ψ ihφ ihψ =>
    rw [literalSubst, literalSubst, ihφ, ihψ]
    · intro x hx; apply h; simp only [fv, boundNames, Finset.mem_union] at hx ⊢; tauto
    · intro x hx; apply h; simp only [fv, boundNames, Finset.mem_union] at hx ⊢; tauto
  | quant q y φ ih =>
    rw [literalSubst, literalSubst, ih]
    intro x hx
    apply h
    simp only [fv, boundNames, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
    by_cases hxy : x = y <;> tauto

end Formula
namespace AlphaFormula
local instance : L.Structure (L.Term ℕ) := syntaxStructure

/-- Fresh binders let an entire sequence be evaluated as a literal term substitution. -/
theorem substSequence_mk_literal (φ : Formula L) (xs : List (ℕ × L.Term ℕ))
    (h : Disjoint φ.boundNames (sequenceKeys xs ∪ sequenceVars xs)) :
    (mk φ).substSequence xs = mk (φ.literalSubst (sequenceAssignment xs Term.var)) := by
  induction xs generalizing φ with
  | nil => simp [substSequence, sequenceAssignment]
  | cons p ps ih =>
    rcases p with ⟨x,t⟩
    have hhead : Disjoint φ.boundNames (insert x t.varFinset) := by
      apply h.mono_right
      intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hy)
    have hrest : Disjoint φ.boundNames (sequenceKeys ps ∪ sequenceVars ps) := by
      apply h.mono_right
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hy)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hy)
    rw [substSequence, subst_mk, Formula.subst_eq_literal φ x t hhead,
      ih _ (by simpa using hrest), Formula.literalSubst_comp]
    congr 2
    funext y
    by_cases hy : y = x
    · subst y; simp [sequenceAssignment, realize_syntax]
    · simp [sequenceAssignment, hy]


@[simp] theorem substSequence_append (φ : AlphaFormula L) (xs ys : List (ℕ × L.Term ℕ)) :
    φ.substSequence (xs ++ ys) = (φ.substSequence xs).substSequence ys := by
  induction xs generalizing φ with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨x,t⟩; exact ih (φ.subst x t)

@[simp] theorem sequenceKeys_append (xs ys : List (ℕ × L.Term ℕ)) :
    sequenceKeys (xs ++ ys) = sequenceKeys xs ∪ sequenceKeys ys := by
  induction xs with
  | nil => simp [sequenceKeys]
  | cons p ps ih => rcases p with ⟨x,t⟩; simp [sequenceKeys, ih]

@[simp] theorem sequenceVars_append (xs ys : List (ℕ × L.Term ℕ)) :
    sequenceVars (xs ++ ys) = sequenceVars xs ∪ sequenceVars ys := by
  induction xs with
  | nil => simp [sequenceVars]
  | cons p ps ih => rcases p with ⟨x,t⟩; simp [sequenceVars, ih, Finset.union_assoc]

theorem sequenceAssignment_append {M : Type*} [L.Structure M] (xs ys : List (ℕ × L.Term ℕ)) (s : ℕ → M) :
    sequenceAssignment (xs ++ ys) s = sequenceAssignment xs (sequenceAssignment ys s) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨x,t⟩; simp only [List.cons_append, sequenceAssignment, ih]

/-- On a representative with fresh binders, the two-pass construction is a literal simultaneous replacement. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    First compare two instances of one defining formula $\varphi$, whose free variables lie among $\vec{x}$.
    Choose a representative of $\varphi$ whose bound names avoid the input variables, all variables in both argument
    lists, and the temporary names in both two-pass substitutions. Such a representative exists by fresh renaming.
    On this representative, every substitution step is literal term replacement: no binder is a target or captures
    an inserted variable. Composing the steps sends each $x_i$ to its argument term and fixes every other name
    occurring in the representative. Thus both constructions are represented by literal simultaneous replacement,
    even if their temporary names differ.
-/
theorem simultaneousAt_mk_literal {n : ℕ} (φ : Formula L) (ts : Fin n → L.Term ℕ) (B : ℕ)
    (hn : n ≤ B) (hf : ∀ x ∈ φ.fv, x < B) (ht : ∀ i x, x ∈ (ts i).varFinset → x < B)
    (hb : Disjoint φ.boundNames (Finset.range n ∪ temporaryNames n B ∪ argumentVars ts)) :
    (mk φ).simultaneousAt ts B =
      mk (φ.literalSubst (fun x => if h : x < n then ts ⟨x,h⟩ else .var x)) := by
  have hseq : Disjoint φ.boundNames
      (sequenceKeys (renameInputs (L := L) n B ++ fillInputs ts B) ∪
        sequenceVars (renameInputs n B ++ fillInputs ts B)) := by
    simpa only [sequenceKeys_append, sequenceVars_append, keys_renameInputs, vars_renameInputs,
      keys_fillInputs, vars_fillInputs, Finset.union_assoc, Finset.union_left_idem] using hb
  rw [simultaneousAt, ← substSequence_append, substSequence_mk_literal φ _ hseq,
    sequenceAssignment_append]
  congr 1
  apply φ.literalSubst_congr
  intro x hx
  have hxt : x ∉ temporaryNames n B := by
    rcases Finset.mem_union.mp hx with hx | hx
    · intro hk
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
      have := hf x hx
      omega
    · exact fun hk => Finset.disjoint_left.mp hb hx
        (Finset.mem_union_left _ (Finset.mem_union_right _ hk))
  have h := sequenceInputs_apply ts B hn ht (Term.var : ℕ → L.Term ℕ) x hxt
  simpa only [realize_syntax, term_subst_var] using h

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
