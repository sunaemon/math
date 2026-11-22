module

public import Mathlib.Data.W.Cardinal
public import PolishSpaceBook.FirstOrderAlphaSubstitution

@[expose] public section

/-!
# Counting the actual named syntax

A finite-arity constructor grammar includes both terms and named formulas.
Its evaluation covers every named formula. Thus the cardinal bound applies to
the syntax used by Henkin requests, and then to its alpha-quotient, rather than
to a different formula representation alone.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language Cardinal
universe u v
variable {L : Language.{u,v}}

abbrev SyntaxAux := ℕ ⊕ (Fin 5 ⊕ (Bool × ℕ))
abbrev SyntaxHead (L : Language.{u,v}) := L.Symbols ⊕ SyntaxAux

abbrev SyntaxOperands : SyntaxHead L → Type
  | .inl (.inl f) => Fin f.1
  | .inl (.inr R) => Fin R.1
  | .inr (.inl _) => Empty
  | .inr (.inr (.inl 0)) => Empty
  | .inr (.inr (.inl 1)) => Bool
  | .inr (.inr (.inl 2)) => Bool
  | .inr (.inr (.inl 3)) => Bool
  | .inr (.inr (.inl 4)) => Bool
  | .inr (.inr (.inr _)) => Unit

instance (h : SyntaxHead L) : Finite (SyntaxOperands h) := by
  rcases h with (f | R) | (x | (k | q))
  · infer_instance
  · infer_instance
  · infer_instance
  · fin_cases k <;> infer_instance
  · infer_instance

def syntaxOperate : (Σ h : SyntaxHead L, SyntaxOperands h → L.Term ℕ × Formula L) → L.Term ℕ × Formula L
  | ⟨.inl (.inl f), a⟩ => ⟨.func f.2 (fun i => (a i).1), .falsum⟩
  | ⟨.inl (.inr R), a⟩ => ⟨.var 0, .rel R.2 (fun i => (a i).1)⟩
  | ⟨.inr (.inl x), _⟩ => ⟨.var x, .falsum⟩
  | ⟨.inr (.inr (.inl 0)), _⟩ => ⟨.var 0, .falsum⟩
  | ⟨.inr (.inr (.inl 1)), a⟩ => ⟨.var 0, .equal (a false).1 (a true).1⟩
  | ⟨.inr (.inr (.inl 2)), a⟩ => ⟨.var 0, .binary .conj (a false).2 (a true).2⟩
  | ⟨.inr (.inr (.inl 3)), a⟩ => ⟨.var 0, .binary .disj (a false).2 (a true).2⟩
  | ⟨.inr (.inr (.inl 4)), a⟩ => ⟨.var 0, .binary .imp (a false).2 (a true).2⟩
  | ⟨.inr (.inr (.inr (false, x))), a⟩ => ⟨.var 0, .quant .all x (a ()).2⟩
  | ⟨.inr (.inr (.inr (true, x))), a⟩ => ⟨.var 0, .quant .ex x (a ()).2⟩

abbrev SyntaxExpression (L : Language.{u,v}) := WType (SyntaxOperands (L := L))
def syntaxValue : SyntaxExpression L → L.Term ℕ × Formula L := WType.elim _ syntaxOperate

theorem term_in_syntaxValue (t : L.Term ℕ) : ∃ c : SyntaxExpression L, (syntaxValue c).1 = t := by
  induction t with
  | var x => exact ⟨.mk (.inr (.inl x)) Empty.elim, rfl⟩
  | @func n f ts ih =>
    choose cs hcs using ih
    refine ⟨.mk (.inl (.inl ⟨n, f⟩)) cs, ?_⟩
    change Term.func f (fun i => (syntaxValue (cs i)).1) = _
    simp only [hcs]

theorem formula_in_syntaxValue (φ : Formula L) : ∃ c : SyntaxExpression L, (syntaxValue c).2 = φ := by
  induction φ with
  | falsum => exact ⟨.mk (.inr (.inr (.inl 0))) Empty.elim, rfl⟩
  | equal t r =>
    obtain ⟨a, ha⟩ := term_in_syntaxValue t
    obtain ⟨b, hb⟩ := term_in_syntaxValue r
    refine ⟨.mk (.inr (.inr (.inl 1))) (Bool.rec a b), ?_⟩
    change Formula.equal (syntaxValue a).1 (syntaxValue b).1 = _
    rw [ha, hb]
  | @rel n R ts =>
    choose cs hcs using (fun i => term_in_syntaxValue (ts i))
    refine ⟨.mk (.inl (.inr ⟨n, R⟩)) cs, ?_⟩
    change Formula.rel R (fun i => (syntaxValue (cs i)).1) = _
    simp only [hcs]
  | binary c φ ψ ihφ ihψ =>
    obtain ⟨a, ha⟩ := ihφ
    obtain ⟨b, hb⟩ := ihψ
    cases c with
    | conj =>
      refine ⟨.mk (.inr (.inr (.inl 2))) (Bool.rec a b), ?_⟩
      change Formula.binary .conj (syntaxValue a).2 (syntaxValue b).2 = _
      rw [ha, hb]
    | disj =>
      refine ⟨.mk (.inr (.inr (.inl 3))) (Bool.rec a b), ?_⟩
      change Formula.binary .disj (syntaxValue a).2 (syntaxValue b).2 = _
      rw [ha, hb]
    | imp =>
      refine ⟨.mk (.inr (.inr (.inl 4))) (Bool.rec a b), ?_⟩
      change Formula.binary .imp (syntaxValue a).2 (syntaxValue b).2 = _
      rw [ha, hb]
  | quant q x φ ih =>
    obtain ⟨a, ha⟩ := ih
    cases q with
    | all => exact ⟨.mk (.inr (.inr (.inr (false, x)))) (fun _ => a), congrArg (Formula.quant .all x) ha⟩
    | ex => exact ⟨.mk (.inr (.inr (.inr (true, x)))) (fun _ => a), congrArg (Formula.quant .ex x) ha⟩

/-- Named binders and logical constructors add at most countably many labels. -/
theorem card_namedFormula_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    #(Formula L) ≤ κ := by
  have hhead : #(SyntaxHead L) ≤ κ := by
    have ha : lift.{max u v} #SyntaxAux ≤ ℵ₀ := lift_le_aleph0.mpr mk_le_aleph0
    change #(L.Symbols ⊕ SyntaxAux) ≤ κ
    rw [mk_sum, lift_uzero]
    exact (add_le_add hL (ha.trans hκ)).trans (le_of_eq (add_eq_self hκ))
  apply (mk_le_of_surjective (formula_in_syntaxValue (L := L))).trans
  exact WType.cardinalMk_le_max_aleph0_of_finite'.trans (by
    simpa only [lift_uzero] using max_le hhead hκ)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    At a stage with $|L_n|\le\kappa$, there are at most $\kappa$ formulas with named variables, by the same finite-syntax
    count. Passing to $\alpha$-classes cannot increase this number.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Taking $\kappa=\max(|L|,|X|,\alephNull)$ gives the general downward bound. For a consistent $L$-theory,
    $\kappa=\max(|L|,\alephNull)$ already suffices. A separate factor for $|T|$ is unnecessary: a theory is a set of
    sentences, and the total number of $L$-sentences is at most this same bound.
-/
theorem card_alphaFormula_le (κ : Cardinal.{max u v}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) :
    #(AlphaFormula L) ≤ κ :=
  mk_quotient_le.trans (card_namedFormula_le κ hκ hL)

end PolishSpaceBook.NamedFirstOrder
