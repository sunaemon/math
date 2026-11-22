module

public import PolishSpaceBook.FirstOrderHenkinTheory

@[expose] public section

/-!
# Provable equality of closed terms

Closed terms are mathlib terms over the empty variable type. Equality symmetry
and transitivity are derived from the printed substitution rule, using a single
variable as a hole; the fixed terms are closed, so no freshness choice is needed.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

/-- Regard a closed term as a term in the named-variable syntax. -/
def namedClosedTerm (t : L.Term Empty) : L.Term ℕ := t.relabel Empty.elim

@[simp] theorem namedClosedTerm_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term Empty) :
    namedClosedTerm (.func f ts) = .func f (fun i => namedClosedTerm (ts i)) := rfl

@[simp] theorem fv_namedClosedTerm (t : L.Term Empty) : (namedClosedTerm t).varFinset = ∅ := by
  induction t with
  | var x => exact x.elim
  | func f ts ih =>
    simp only [namedClosedTerm_func, Term.varFinset, ih]
    ext x
    simp

@[simp] theorem termSubst_namedClosedTerm (t : L.Term Empty) (x : ℕ) (r : L.Term ℕ) :
    termSubst (namedClosedTerm t) x r = namedClosedTerm t :=
  termSubst_not_free _ _ _ (by simp)

@[simp] theorem termSubst_var_self (x : ℕ) (r : L.Term ℕ) : termSubst (.var x) x r = r := by
  simp [termSubst, Term.subst]

namespace AlphaFormula

def rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ) : AlphaFormula L := mk (.rel R ts)

@[simp] theorem subst_equal (t r : L.Term ℕ) (x : ℕ) (s : L.Term ℕ) :
    (equal t r).subst x s = equal (termSubst t x s) (termSubst r x s) := rfl

@[simp] theorem subst_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ) (x : ℕ) (s : L.Term ℕ) :
    (rel R ts).subst x s = rel R (fun i => termSubst (ts i) x s) := rfl

end AlphaFormula

def closedEq (t r : L.Term Empty) : AlphaFormula L := equal (namedClosedTerm t) (namedClosedTerm r)
def closedRel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term Empty) : AlphaFormula L :=
  rel R (fun i => namedClosedTerm (ts i))

@[simp] theorem fv_closedEq (t r : L.Term Empty) : (closedEq t r).fv = ∅ := by
  change (namedClosedTerm t).varFinset ∪ (namedClosedTerm r).varFinset = ∅
  simp

@[simp] theorem fv_closedRel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term Empty) :
    (closedRel R ts).fv = ∅ := by
  change Finset.univ.biUnion (fun i => (namedClosedTerm (ts i)).varFinset) = ∅
  ext x
  simp

namespace ProvesFrom

/-- Combine two finite derivations before applying a two-premise rule. -/
theorem map₂ {T : Set (AlphaFormula L)} {φ ψ χ : AlphaFormula L}
    (hφ : ProvesFrom T φ) (hψ : ProvesFrom T ψ)
    (f : ∀ {Γ}, Derives Γ φ → Derives Γ ψ → Derives Γ χ) : ProvesFrom T χ := by
  obtain ⟨Γ, hΓ, hdφ⟩ := hφ
  obtain ⟨Δ, hΔ, hdψ⟩ := hψ
  refine ⟨Γ ∪ Δ, ?_, f (hdφ.weaken Finset.subset_union_left) (hdψ.weaken Finset.subset_union_right)⟩
  intro θ hθ
  exact (Finset.mem_union.mp hθ).elim (hΓ θ) (hΔ θ)

theorem eqIntro (T : Set (AlphaFormula L)) (t : L.Term ℕ) : ProvesFrom T (equal t t) :=
  ⟨∅, by simp, .eqIntro ∅ t⟩

theorem eqElim {T : Set (AlphaFormula L)} (φ : AlphaFormula L) (x : ℕ) (t r : L.Term ℕ)
    (hφ : ProvesFrom T (φ.subst x t)) (heq : ProvesFrom T (equal t r)) :
    ProvesFrom T (φ.subst x r) :=
  hφ.map₂ heq (Derives.eqElim φ x t r)

theorem closedEq_refl (T : Set (AlphaFormula L)) (t : L.Term Empty) : ProvesFrom T (closedEq t t) :=
  eqIntro T _

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Equality introduction gives reflexivity. To derive symmetry from $t=u$, apply equality elimination to the
    formula $z=t$, starting from $t=t$ and replacing $z$ by $u$. To derive transitivity from $t=u$ and $u=v$,
    use the formula $t=z$ and replace $z$ by $v$ in the instance with $z$ replaced by $u$.
    The fixed terms are closed, so the variable $z$ is fresh for them. Thus provable equality is an equivalence relation.
    For a closed equality, deductive closure gives
    $$\TermModelClass{t}=\TermModelClass{u}
    \quad\Longleftrightarrow\quad T^*\vdash t=u
    \quad\Longleftrightarrow\quad (t=u)\in T^*.$$
-/
theorem closedEq_symm {T : Set (AlphaFormula L)} {t r : L.Term Empty} (h : ProvesFrom T (closedEq t r)) :
    ProvesFrom T (closedEq r t) := by
  have hs := eqElim (equal (.var 0) (namedClosedTerm t)) 0 (namedClosedTerm t) (namedClosedTerm r)
    (by simpa [closedEq] using closedEq_refl T t) h
  simpa [closedEq] using hs

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Equality introduction gives reflexivity. To derive symmetry from $t=u$, apply equality elimination to the
    formula $z=t$, starting from $t=t$ and replacing $z$ by $u$. To derive transitivity from $t=u$ and $u=v$,
    use the formula $t=z$ and replace $z$ by $v$ in the instance with $z$ replaced by $u$.
    The fixed terms are closed, so the variable $z$ is fresh for them. Thus provable equality is an equivalence relation.
    For a closed equality, deductive closure gives
    $$\TermModelClass{t}=\TermModelClass{u}
    \quad\Longleftrightarrow\quad T^*\vdash t=u
    \quad\Longleftrightarrow\quad (t=u)\in T^*.$$
-/
theorem closedEq_trans {T : Set (AlphaFormula L)} {t r s : L.Term Empty}
    (htr : ProvesFrom T (closedEq t r)) (hrs : ProvesFrom T (closedEq r s)) :
    ProvesFrom T (closedEq t s) := by
  have hs := eqElim (equal (namedClosedTerm t) (.var 0)) 0 (namedClosedTerm r) (namedClosedTerm s)
    (by simpa [closedEq] using htr) hrs
  simpa [closedEq] using hs

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
