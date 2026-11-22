module

public import PolishSpaceBook.FirstOrderClosedCongruence
public import Mathlib.ModelTheory.Quotients

@[expose] public section

/-!
# The term structure and the atomic truth lemma

Closed terms are quotiented by provable equality. The derived congruence lemmas
supply mathlib's canonical quotient structure. Interpretation of terms follows
by induction, and the atomic clauses are exactly provability, or membership
when the theory is maximally consistent. No full truth lemma is assumed.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

/-- The equivalence relation used to form the term structure. -/
def provableTermSetoid (T : Set (AlphaFormula L)) : Setoid (L.Term Empty) where
  r t r := ProvesFrom T (closedEq t r)
  iseqv := ⟨ProvesFrom.closedEq_refl T, ProvesFrom.closedEq_symm, ProvesFrom.closedEq_trans⟩

instance termPrestructure (T : Set (AlphaFormula L)) : L.Prestructure (provableTermSetoid T) where
  toStructure := {
    funMap := fun f ts => Term.func f ts
    RelMap := fun R ts => ProvesFrom T (closedRel R ts) }
  fun_equiv := fun ts rs h => ProvesFrom.closedFunction_congr _ ts rs h
  rel_equiv := fun ts rs h => propext (ProvesFrom.closedRelation_congr _ ts rs h)

/-- The domain of the term structure. -/
abbrev TermModel (T : Set (AlphaFormula L)) := Quotient (provableTermSetoid T)

def termClass (T : Set (AlphaFormula L)) (t : L.Term Empty) : TermModel T := Quotient.mk _ t

@[simp] theorem termClass_eq_iff (T : Set (AlphaFormula L)) (t r : L.Term Empty) :
    termClass T t = termClass T r ↔ ProvesFrom T (closedEq t r) := Quotient.eq

@[simp] theorem funMap_termClass (T : Set (AlphaFormula L)) {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L.Term Empty) :
    Structure.funMap f (fun i => termClass T (ts i)) = termClass T (.func f ts) :=
  funMap_quotient_mk' (provableTermSetoid T) f ts

@[simp] theorem relMap_termClass (T : Set (AlphaFormula L)) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term Empty) :
    Structure.RelMap R (fun i => termClass T (ts i)) ↔ ProvesFrom T (closedRel R ts) :=
  relMap_quotient_mk' (provableTermSetoid T) R ts

/-- Substituting representatives evaluates a term to the class of the resulting closed term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induction on terms shows that a term evaluated at classes of closed terms is the class of the closed term
    obtained by substitution. The variable case is the assignment itself, and the function case is the defining
    clause above applied after the induction hypotheses for the arguments.
    For an equality, the displayed equivalences now give the atomic truth clause.
    For a relation, use its defining membership clause after the same evaluation of its arguments.
    \end{proof}
-/
theorem realize_termClass (T : Set (AlphaFormula L)) (t : L.Term ℕ) (s : ℕ → L.Term Empty) :
    t.realize (fun x => termClass T (s x)) = termClass T (t.subst s) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.realize, Term.subst, ih, funMap_termClass]

@[simp] theorem realize_namedClosedTerm (T : Set (AlphaFormula L)) (t : L.Term Empty)
    (s : ℕ → TermModel T) : (namedClosedTerm t).realize s = termClass T t := by
  induction t with
  | var x => exact x.elim
  | func f ts ih => simp only [namedClosedTerm_func, Term.realize, ih, funMap_termClass]

theorem realize_equal_termClass (T : Set (AlphaFormula L)) (t r : L.Term ℕ) (s : ℕ → L.Term Empty) :
    (equal t r).Realize (fun x => termClass T (s x)) ↔ ProvesFrom T (closedEq (t.subst s) (r.subst s)) := by
  simp only [realize_equal, realize_termClass, termClass_eq_iff]

theorem realize_rel_termClass (T : Set (AlphaFormula L)) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term ℕ) (s : ℕ → L.Term Empty) :
    (rel R ts).Realize (fun x => termClass T (s x)) ↔ ProvesFrom T (closedRel R (fun i => (ts i).subst s)) := by
  change Structure.RelMap R (fun i => (ts i).realize (fun x => termClass T (s x))) ↔ _
  simp only [realize_termClass, relMap_termClass]

theorem realize_closedEq (T : Set (AlphaFormula L)) (t r : L.Term Empty) (s : ℕ → TermModel T) :
    (closedEq t r).Realize s ↔ ProvesFrom T (closedEq t r) := by
  simp only [closedEq, realize_equal, realize_namedClosedTerm, termClass_eq_iff]

theorem realize_closedRel (T : Set (AlphaFormula L)) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term Empty) (s : ℕ → TermModel T) :
    (closedRel R ts).Realize s ↔ ProvesFrom T (closedRel R ts) := by
  change Structure.RelMap R (fun i => (namedClosedTerm (ts i)).realize s) ↔ _
  simp only [realize_namedClosedTerm, relMap_termClass]

namespace MaximallyConsistent

theorem termClass_eq_iff_mem {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T) (t r : L.Term Empty) :
    termClass T t = termClass T r ↔ closedEq t r ∈ T :=
  (termClass_eq_iff T t r).trans (hT.mem_iff_proves (by simp [Sentences])).symm

theorem relMap_termClass_iff_mem {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T) {n : ℕ}
    (R : L.Relations n) (ts : Fin n → L.Term Empty) :
    Structure.RelMap R (fun i => termClass T (ts i)) ↔ closedRel R ts ∈ T :=
  (relMap_termClass T R ts).trans (hT.mem_iff_proves (by simp [Sentences])).symm

theorem realize_equal_iff_mem {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (t r : L.Term ℕ) (s : ℕ → L.Term Empty) :
    (equal t r).Realize (fun x => termClass T (s x)) ↔ closedEq (t.subst s) (r.subst s) ∈ T :=
  (realize_equal_termClass T t r s).trans (hT.mem_iff_proves (by simp [Sentences])).symm

theorem realize_rel_iff_mem {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T) {n : ℕ}
    (R : L.Relations n) (ts : Fin n → L.Term ℕ) (s : ℕ → L.Term Empty) :
    (rel R ts).Realize (fun x => termClass T (s x)) ↔ closedRel R (fun i => (ts i).subst s) ∈ T :=
  (realize_rel_termClass T R ts s).trans (hT.mem_iff_proves (by simp [Sentences])).symm

end MaximallyConsistent

/-- Witness completeness supplies a constant even when the original language had none. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The domain is nonempty: the Henkin axiom for $\existsbind{x}{\bot}$ includes a constant, whose class is an element.
    Its existence does not require the existential sentence to hold.
-/
theorem HasHenkinWitnesses.nonempty_termModel {T : Set (AlphaFormula L)} (hT : HasHenkinWitnesses T) :
    Nonempty (TermModel T) := by
  obtain ⟨c, _⟩ := hT 0 falsum (by simp)
  exact ⟨termClass T c.term⟩

/-- The quotient construction, including nonemptiness and all atomic clauses. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Term-model construction
-/
theorem term_model_construction {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) :
    Nonempty (TermModel T) ∧
    (∀ t r, termClass T t = termClass T r ↔ closedEq t r ∈ T) ∧
    (∀ n (f : L.Functions n) ts,
      Structure.funMap f (fun i => termClass T (ts i)) = termClass T (.func f ts)) ∧
    (∀ n (R : L.Relations n) ts, Structure.RelMap R (fun i => termClass T (ts i)) ↔ closedRel R ts ∈ T) ∧
    (∀ t r s, (equal t r).Realize (fun x => termClass T (s x)) ↔ closedEq (t.subst s) (r.subst s) ∈ T) ∧
    (∀ n (R : L.Relations n) ts s, (rel R ts).Realize (fun x => termClass T (s x)) ↔
      closedRel R (fun i => (ts i).subst s) ∈ T) :=
  ⟨hH.nonempty_termModel, hT.termClass_eq_iff_mem, fun _ => funMap_termClass T,
    fun _ => hT.relMap_termClass_iff_mem, hT.realize_equal_iff_mem, fun _ => hT.realize_rel_iff_mem⟩

end PolishSpaceBook.NamedFirstOrder
