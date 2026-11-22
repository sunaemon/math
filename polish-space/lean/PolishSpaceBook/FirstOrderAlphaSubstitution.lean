module

public import PolishSpaceBook.FirstOrderFormulaCorrespondence

@[expose] public section

/-!
# First-order substitution is compatible with alpha-equivalence

Prepare the actual binders chosen by capture-avoiding substitution on both sides,
then substitute corresponding terms under the transported name correspondence.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v
variable {L : Language.{u,v}}
namespace Formula
namespace NameRel

/-- Expose the binder and body selected by the existing substitution clauses. -/
theorem prepare_subst_quant (q : Quantifier) (M : Formula L) (u x : ℕ)
    (T : L.Term ℕ) (hux : u ≠ x) :
    ∃ (z : ℕ) (B : Formula L),
      (Formula.quant q u M).subst x T = Formula.quant q z (B.subst x T) ∧ B.nodes = M.nodes ∧
      z ≠ x ∧ z ∉ T.varFinset ∧
      ∀ (R : ℕ → ℕ → Prop) y N, NameRel (bindNames R u y) M N →
        NameRel (bindNames R z y) B N := by
  by_cases hu : u ∉ T.varFinset
  · refine ⟨u, M, ?_, rfl, hux, hu, ?_⟩
    · rw [subst_quant, ite_eq_right hux, ite_eq_left hu]
    · intro R y N h; exact h
  · let z := NamedLambda.Term.fresh (M.fv ∪ T.varFinset ∪ {x})
    have hz : z ∉ M.fv ∧ z ∉ T.varFinset ∧ z ≠ x := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using NamedLambda.Term.fresh_not_mem (M.fv ∪ T.varFinset ∪ {x})
    refine ⟨z, M.subst u (.var z), ?_, nodes_subst M u (.var z), hz.2.2, hz.2.1, ?_⟩
    · rw [subst_quant, ite_eq_right hux, ite_eq_right hu]
    · intro R y N h; exact h.rebind_left z hz.1

theorem symm_bind {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Formula L}
    (h : NameRel (bindNames R x y) M N) :
    NameRel (bindNames (fun b a => R a b) y x) N M := by
  apply h.symm.mono
  intro b a hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
  · exact Or.inl ⟨hb, ha⟩
  · exact Or.inr ⟨hb, ha, hab⟩

/-- Corresponding substitutions preserve the comparison of named formulas. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Prove the following stronger assertion about comparison. Suppose
    $\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ and $\FirstOrderNameCorrespondence{S}{t}{t'}$, and assume that
    $$\begin{aligned}
    R(a,b)&\ \Longrightarrow\ (a=x\Longleftrightarrow b=y),\\
    R(a,b)\land a\ne x&\ \Longrightarrow\ S(a,b).
    \end{aligned}$$
    Then $\FirstOrderNameCorrespondence{S}{\varphi\subst{x}{t}}{\psi\subst{y}{t'}}$.
    Induct on the number of formula constructors. If $x$ is not free on the left, the correspondence of free names
    shows that $y$ is not free on the right. Substitution for these absent variables changes each formula only up to
    $\alpha$-equivalence, as proved above. Comparison with equality on each side and the second hypothesis
    then give the required comparison under $S$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Otherwise both variables occur freely. The term cases follow by structural induction, using the comparison of
    the replacements at the variables being replaced and the second hypothesis at all other variables.
    Atomic formulas and binary connectives follow componentwise.
    Under quantifiers, neither binder is the variable being replaced. On each side use the binder prescribed by
    the substitution rule: keep it if it is absent from the replacement's free variables, and otherwise rename it.
    The preceding renaming fact transports the body comparison to this pair of binders.
    The replacement terms still compare under the extended relation because the new binders are absent from them.
    The two hypotheses on the relations also hold under this extension: the bound names correspond and are not replaced,
    and every remaining pair satisfies the original hypotheses. Apply induction to the prepared bodies and restore
    the quantifiers. The bodies have unchanged size, so the induction applies.
-/
theorem subst {R S : ℕ → ℕ → Prop} {M N : Formula L} {T U : L.Term ℕ}
    (h : NameRel R M N) (x y : ℕ) (ht : TermRel S T U)
    (hkeys : ∀ a b, R a b → (a = x ↔ b = y))
    (hkeep : ∀ a b, R a b → a ≠ x → S a b) :
    NameRel S (M.subst x T) (N.subst y U) := by
  have bounded : ∀ k (M N : Formula L) (T U : L.Term ℕ) (R S : ℕ → ℕ → Prop) x y,
      M.nodes ≤ k → NameRel R M N → TermRel S T U →
      (∀ a b, R a b → (a = x ↔ b = y)) →
      (∀ a b, R a b → a ≠ x → S a b) →
      NameRel S (M.subst x T) (N.subst y U) := by
    intro k
    induction k with
    | zero => intro M N T U R S x y hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N T U R S x y hk h ht hkeys hkeep
      by_cases hx : x ∈ M.fv
      · have hy : y ∈ N.fv := by
          obtain ⟨b, hb, hr⟩ := h.fv_left hx
          have he := (hkeys x b hr).mp rfl
          simpa only [he] using hb
        cases h with
        | falsum => exact .falsum _
        | equal ha hb =>
          rw [subst_equal, subst_equal]
          exact .equal (ha.subst x y ht hkeys hkeep) (hb.subst x y ht hkeys hkeep)
        | rel r hts =>
          rw [subst_rel, subst_rel]
          exact .rel r (fun i => (hts i).subst x y ht hkeys hkeep)
        | @binary c _ A B C D hab hcd =>
          rw [subst_binary, subst_binary]
          exact .binary c (ih A B T U R S x y (by simp only [nodes] at hk; omega) hab ht hkeys hkeep)
            (ih C D T U R S x y (by simp only [nodes] at hk; omega) hcd ht hkeys hkeep)
        | @quant q _ u v A B hab =>
          have hux : u ≠ x := (Finset.mem_erase.mp hx).1.symm
          have hvy : v ≠ y := (Finset.mem_erase.mp hy).1.symm
          obtain ⟨u', A', heA, hnA, hux', huT, hA⟩ := prepare_subst_quant q A u x T hux
          obtain ⟨v', B', heB, hnB, hvy', hvU, hB⟩ := prepare_subst_quant q B v y U hvy
          rw [heA, heB]
          apply NameRel.quant q
          have hAB : NameRel (bindNames R u' v') A' B' :=
            (hB (fun b a => R a b) u' A' ((hA R v B hab).symm_bind)).symm_bind
          have hTU : TermRel (bindNames S u' v') T U := by
            apply ht.congr
            intro a ha b hb hr
            have hau : a ≠ u' := by intro he; subst a; exact huT ha
            have hbv : b ≠ v' := by intro he; subst b; exact hvU hb
            exact Or.inr ⟨hau, hbv, hr⟩
          apply ih A' B' T U (bindNames R u' v') (bindNames S u' v') x y
            (by rw [hnA]; simp only [nodes] at hk; omega) hAB hTU
          · intro a b hr
            rcases hr with ⟨rfl, rfl⟩ | ⟨_, _, hr⟩
            · simp only [hux', hvy']
            · exact hkeys a b hr
          · intro a b hr hax
            rcases hr with ⟨rfl, rfl⟩ | ⟨hau, hbv, hr⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨hau, hbv, hkeep a b hr hax⟩
      · have hy : y ∉ N.fv := by
          intro hy
          obtain ⟨a, ha, hr⟩ := h.symm.fv_left hy
          have he := (hkeys a y hr).mpr rfl
          exact hx (by simpa only [he] using ha)
        have hMN : NameRel S M N := by
          apply h.congr
          intro a ha b hb hr
          exact hkeep a b hr (by intro he; subst a; exact hx ha)
        have hleft := (alpha_subst_not_free M x T hx).nameRel
        have hright := (alpha_subst_not_free N y U hy).nameRel.eq_symm
        exact (hleft.trans hMN (by intro a b c he hr; subst b; exact hr)).trans hright
          (by intro a b c hr he; subst c; exact hr)
  exact bounded M.nodes M N T U R S x y le_rfl h ht hkeys hkeep

end NameRel

/-- The appendix's capture-avoiding substitution descends to alpha-classes. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Substitution and bound-variable names
-/
theorem Alpha.subst {φ ψ : Formula L} (h : Alpha φ ψ) (x : ℕ) (t : L.Term ℕ) :
    Alpha (φ.subst x t) (ψ.subst x t) := by
  apply NameRel.eq_alpha
  apply h.nameRel.subst x x (TermRel.refl t)
  · intro a b hab; subst b; rfl
  · intro a b hab _; exact hab

/-- Instantiating a quantified body is independent of its bound variable's name. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Substitution and bound-variable names
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the first assertion, take both relations to be equality, use the same variable on both sides, and set $t'=t$.
    For the second, the bodies compare under $\FirstOrderBoundNames{=}{x}{y}$.
    Take this as the input relation and equality as the output relation, again with $t'=t$.
    The two hypotheses hold by the definition of the binder correspondence.
    The comparison lemma converts both conclusions to $\alpha$-equivalence.
-/
theorem Alpha.instantiate {q : Quantifier} {x y : ℕ} {φ ψ : Formula L}
    (h : Alpha (Formula.quant q x φ) (Formula.quant q y ψ)) (t : L.Term ℕ) :
    Alpha (φ.subst x t) (ψ.subst y t) := by
  cases h.nameRel with
  | quant _ hb =>
    apply NameRel.eq_alpha
    apply hb.subst x y (TermRel.refl t)
    · intro a b hr
      rcases hr with ⟨rfl, rfl⟩ | ⟨hax, hby, _⟩
      · simp
      · simp only [hax, hby]
    · intro a b hr hax
      rcases hr with ⟨ha, _⟩ | ⟨_, _, hab⟩
      · exact (hax ha).elim
      · exact hab

end Formula

def formulaAlphaSetoid : Setoid (Formula L) where
  r := Formula.Alpha
  iseqv := ⟨Formula.Alpha.refl, Formula.Alpha.symm, Formula.Alpha.trans⟩

/-- First-order formulas with bound-variable names identified. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, substitution and the free-variable operation are well defined on $\alpha$-equivalence classes.
    From here on, we identify $\alpha$-equivalent formulas: "the formula $\varphi$" means its $\alpha$-class, and a
    bound variable can always be renamed to any fresh choice without changing $\varphi$.
-/
def AlphaFormula (L : Language.{u,v}) := Quotient (formulaAlphaSetoid (L := L))

namespace AlphaFormula

def mk (φ : Formula L) : AlphaFormula L := Quotient.mk formulaAlphaSetoid φ

def binary (c : Connective) : AlphaFormula L → AlphaFormula L → AlphaFormula L :=
  Quotient.map₂ (Formula.binary c) (by intro a b h c d h'; exact .binary _ h h')

def quant (q : Quantifier) (x : ℕ) : AlphaFormula L → AlphaFormula L :=
  Quotient.map (Formula.quant q x) (by intro a b h; exact .quant q x h)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, substitution and the free-variable operation are well defined on $\alpha$-equivalence classes.
    From here on, we identify $\alpha$-equivalent formulas: "the formula $\varphi$" means its $\alpha$-class, and a
    bound variable can always be renamed to any fresh choice without changing $\varphi$.
-/
def subst (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) : AlphaFormula L :=
  Quotient.map (fun A => Formula.subst A x t) (by intro a b h; exact h.subst x t) φ

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, substitution and the free-variable operation are well defined on $\alpha$-equivalence classes.
    From here on, we identify $\alpha$-equivalent formulas: "the formula $\varphi$" means its $\alpha$-class, and a
    bound variable can always be renamed to any fresh choice without changing $\varphi$.
-/
def fv : AlphaFormula L → Finset ℕ :=
  Quotient.lift Formula.fv (fun _ _ h => h.fv_eq)

def Realize {M : Type*} [L.Structure M] (φ : AlphaFormula L) (s : ℕ → M) : Prop :=
  Quotient.lift (fun A => Formula.Realize A s)
    (fun _ _ h => propext (Formula.Alpha.realize h s)) φ

theorem mk_eq_iff (φ ψ : Formula L) : mk φ = mk ψ ↔ Formula.Alpha φ ψ := Quotient.eq

@[simp] theorem subst_mk (φ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    subst (mk φ) x t = mk (φ.subst x t) := rfl

@[simp] theorem fv_mk (φ : Formula L) : (mk φ).fv = φ.fv := rfl

@[simp] theorem realize_mk {M : Type*} [L.Structure M] (φ : Formula L) (s : ℕ → M) :
    (mk φ).Realize s ↔ φ.Realize s := Iff.rfl

theorem realize_subst {M : Type*} [L.Structure M]
    (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (s : ℕ → M) :
    (φ.subst x t).Realize s ↔ φ.Realize (Function.update s x (t.realize s)) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.realize_subst φ x t s

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
