module

public import PolishSpaceBook.FirstOrderRelationDerivations

@[expose] public section

/-!
# Syntactic conservativity of relation definitions

Erasure fixes old formulas. A defining axiom erases to the universal closure of
two identity implications. Translate a derivation and replace those translated
axioms by their proofs; no model existence or completeness is used.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace RelationDefinitions
variable (D : RelationDefinitions L ι)

@[simp] theorem eraseTerm_inclusion (t : L.Term ℕ) :
    eraseTerm ((inclusion (ι := ι)).onTerm t) = t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    change Term.func f (fun i => eraseTerm (inclusion.onTerm (ts i))) = Term.func f ts
    simp only [ih]

theorem eraseFormula_inclusion (φ : Formula L) :
    D.eraseFormula (φ.mapLanguage inclusion) = AlphaFormula.mk φ := by
  induction φ with
  | falsum => rfl
  | equal t r => simp only [Formula.mapLanguage, eraseFormula, eraseTerm_inclusion]; rfl
  | rel R ts =>
    change rel R (fun i => eraseTerm (inclusion.onTerm (ts i))) = _
    simp only [eraseTerm_inclusion]; rfl
  | binary c φ ψ ihφ ihψ => simp only [Formula.mapLanguage, eraseFormula, ihφ, ihψ]; rfl
  | quant q x φ ih => simp only [Formula.mapLanguage, eraseFormula, ih]; rfl

@[simp] theorem eliminate_inclusion (φ : AlphaFormula L) :
    D.eliminate (φ.mapLanguage inclusion) = φ := by
  induction φ using Quotient.inductionOn with | _ φ => exact D.eraseFormula_inclusion φ

@[simp] theorem eliminate_closeAll (n : ℕ) (φ : AlphaFormula (L.sum (relationSymbols ι))) :
    D.eliminate (closeAll n φ) = closeAll n (D.eliminate φ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [closeAll, eliminate_quant, ih]

@[simp] theorem eliminate_atom {n : ℕ} (r : ι n) : D.eliminate (atom r) = D.formula r := by
  change (D.formula r).simultaneous (fun i : Fin n => .var i.val) = _
  exact simultaneous_vars _ n

/-- The translated defining axiom is a theorem of pure logic. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Elimination fixes old-language formulas by structural induction. It also fixes a defining formula instantiated
    at its own input variables: on a representative with fresh binders, the literal replacement is the identity.
    Consequently, the defining axiom for a relation translates to the universal closure of
    $$(\varphi\to\varphi)\land(\varphi\to\varphi).$$
    Each implication follows by discharging its own hypothesis, and conjunction introduction combines them.
    Universal introduction closes the variables because the context is empty. Hence the translated defining axiom
    has a proof without assumptions.
-/
theorem derives_eliminate_axiom {n : ℕ} (r : ι n) :
    Derives ∅ (D.eliminate (D.definingAxiom r)) := by
  rw [definingAxiom, eliminate_closeAll]
  simp only [body, eliminate_binary, eliminate_atom, eliminate_inclusion]
  have hb : Derives (∅ : Context L)
      (binary .conj (binary .imp (D.formula r) (D.formula r))
        (binary .imp (D.formula r) (D.formula r))) :=
    .andIntro (.impIntro (.hyp ∅ _)) (.impIntro (.hyp ∅ _))
  have close : ∀ (k : ℕ) (φ : AlphaFormula L), Derives ∅ φ → Derives ∅ (closeAll k φ) := by
    intro k φ h
    induction k with
    | zero => exact h
    | succ k ih => exact .allIntro k ih (by simp [Context.fv])
  exact close n _ hb

/-- Translate the proof, then discharge the translated definition axioms. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Apply proof translation to the given derivation. Its finitely many translated assumptions are either old axioms
    of $T$ or translated defining axioms. Replace the latter by the proofs just constructed, using the hypothesis
    substitution proved earlier. The resulting derivation uses only assumptions from $T$. An old-language conclusion
    is unchanged by elimination, which proves conservativity directly.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: corollary
  title: Syntactic conservativity
-/
theorem eliminate_theory_proof {T : Set (AlphaFormula L)}
    {φ : AlphaFormula (L.sum (relationSymbols ι))} (h : ProvesFrom (D.theory T) φ) :
    ProvesFrom T (D.eliminate φ) := by
  apply (D.eliminate_proof h).cut
  rintro ψ ⟨χ, hχ, rfl⟩
  rcases hχ with hχ | ⟨n, r, rfl⟩
  · obtain ⟨θ, hθ, rfl⟩ := hχ
    rw [eliminate_inclusion]
    exact ProvesFrom.hyp hθ
  · exact ⟨∅, by simp, D.derives_eliminate_axiom r⟩

/-- The proof transformation establishes conservativity even for open assumptions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For relation definitions, \termuse{syntactic conservativity of relation definitions} gives a direct transformation
    of proofs. The model argument above also covers the function and constant definitions.
-/
theorem conservative_syntactic {T : Set (AlphaFormula L)} {φ : AlphaFormula L}
    (h : ProvesFrom (D.theory T) (φ.mapLanguage inclusion)) : ProvesFrom T φ := by
  simpa only [eliminate_inclusion] using D.eliminate_theory_proof h

end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
