module

public import PolishSpaceBook.FirstOrderHenkinFamilies

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The successive Henkin languages and theories

A request is a formula with at most one specified free variable. Each stage
adds a separate constant for every request from the preceding stage. Repeated
requests are harmless; their constants are distinguished by their birth stage.
The empty constant extension at stage zero merely puts function symbols and
formulas in one common universe, and is conservative.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v

/-- A formula for which a new witness is requested. -/
structure HenkinRequest (L : Language.{u,v}) where
  name : ℕ
  formula : AlphaFormula L
  free : formula.fv ⊆ {name}

/-- The stages, with an empty conservative extension to stabilize universes. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Let $L_0=L$ and $T_0=T$. Given $L_n$ and $T_n$, add a distinct new constant $c_{n,\psi,x}$ for every pair
    consisting of a variable $x$ and an $L_n$-formula $\psi$ with $\FreeVars{\psi}\IncludedIn\{x\}$.
    Let $L_{n+1}$ be the resulting language and obtain $T_{n+1}$ from $T_n$ by adjoining all corresponding Henkin axioms.
    A formula may receive another constant at a later stage; the stage number keeps these symbols distinct.
    Set $L_H=\bigcup_n L_n$ and $S=\bigcup_n T_n$, identifying symbols and formulas with their images under inclusion.
-/
def henkinStage (L : Language.{u,v}) : ℕ → Language.{max u v,v}
  | 0 => L[[PEmpty.{max u v + 1}]]
  | n + 1 => (henkinStage L n)[[HenkinRequest (henkinStage L n)]]

variable (L : Language.{u,v})

def henkinStep (n : ℕ) : henkinStage L n →ᴸ henkinStage L (n + 1) :=
  (henkinStage L n).lhomWithConstants _

/-- Include a stage into any later stage. -/
def henkinStageMap {n m : ℕ} (h : n ≤ m) : henkinStage L n →ᴸ henkinStage L m :=
  Nat.leRecOn h (fun {k} f => (henkinStep L k).comp f) (LHom.id _)

@[simp] theorem henkinStageMap_self (n : ℕ) : henkinStageMap L (Nat.le_refl n) = LHom.id _ := by
  exact Nat.leRecOn_self _

theorem henkinStageMap_succ {n m : ℕ} (h : n ≤ m) :
    henkinStageMap L (Nat.le_succ_of_le h) = (henkinStep L m).comp (henkinStageMap L h) := by
  exact Nat.leRecOn_succ h _

theorem henkinStageMap_step {n m : ℕ} (h : n + 1 ≤ m) :
    (henkinStageMap L h).comp (henkinStep L n) = henkinStageMap L (Nat.le_trans (Nat.le_succ n) h) := by
  induction m, h using Nat.le_induction with
  | base => simp [henkinStageMap_succ]
  | @succ m h ih =>
    rw [henkinStageMap_succ L h, henkinStageMap_succ L (Nat.le_trans (Nat.le_succ n) h)]
    rw [LHom.comp_assoc, ih]

/-- The theory at each stage includes the preceding theory and all its requests. -/
def henkinStageTheory (T : Set (AlphaFormula L)) : (n : ℕ) → Set (AlphaFormula (henkinStage L n))
  | 0 => AlphaFormula.mapLanguage (L.lhomWithConstants _) '' T
  | n + 1 => henkinTheory (henkinStageTheory T n) HenkinRequest.name HenkinRequest.formula Set.univ

variable {L}

theorem henkinStageTheory_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L) (n : ℕ) :
    henkinStageTheory L T n ⊆ Sentences (henkinStage L n) := by
  induction n with
  | zero =>
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [Sentences] using hT hφ
  | succ n ih => exact henkinTheory_sentences ih _ _ HenkinRequest.free _

theorem Consistent.henkinStageTheory {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (n : ℕ) : Consistent (henkinStageTheory L T n) := by
  induction n with
  | zero => exact hT.withConstants
  | succ n ih =>
    exact ih.adjoin_henkinFamily (henkinStageTheory_sentences hclosed n) _ _ HenkinRequest.free _

theorem henkinStageTheory_step {T : Set (AlphaFormula L)} {n : ℕ}
    {φ : AlphaFormula (henkinStage L n)} (hφ : φ ∈ henkinStageTheory L T n) :
    φ.mapLanguage (henkinStep L n) ∈ henkinStageTheory L T (n + 1) :=
  Or.inl ⟨φ, hφ, rfl⟩

theorem henkinStageTheory_witness (T : Set (AlphaFormula L)) (n : ℕ)
    (r : HenkinRequest (henkinStage L n)) :
    henkinAxiom r r.name r.formula ∈ henkinStageTheory L T (n + 1) :=
  Or.inr ⟨r, Set.mem_univ _, rfl⟩

end PolishSpaceBook.NamedFirstOrder
