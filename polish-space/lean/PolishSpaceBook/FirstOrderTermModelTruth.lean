module

public import PolishSpaceBook.FirstOrderSentenceTruth

@[expose] public section

/-!
# The assignment form of the term-model truth lemma

Substitute closed representatives successively for a finite list covering all
free variables. The free-variable formula proves closure. The substitution
lemma and term evaluation identify the resulting sentence's truth with truth
under the original assignment. This derives the assignment form from the
already proved sentence form, without a circular use at quantifiers.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}

namespace AlphaFormula

/-- Successively substitute closed terms for a finite list of named variables. -/
def closeAlong (σ : ℕ → L.Term Empty) : AlphaFormula L → List ℕ → AlphaFormula L
  | φ, [] => φ
  | φ, x :: xs => closeAlong σ (φ.subst x (namedClosedTerm (σ x))) xs

theorem fv_closeAlong (σ : ℕ → L.Term Empty) (φ : AlphaFormula L) (xs : List ℕ) :
    (closeAlong σ φ xs).fv = φ.fv \ xs.toFinset := by
  induction xs generalizing φ with
  | nil => simp [closeAlong]
  | cons x xs ih =>
    rw [closeAlong, ih, fv_subst, fv_namedClosedTerm]
    simp only [ite_self, Finset.union_empty]
    ext y
    simp [and_comm, and_left_comm, and_assoc]

/-- The assignment after all variables in the list have received their representatives. -/
def closeAssignment (T : Set (AlphaFormula L)) (σ : ℕ → L.Term Empty) (xs : List ℕ)
    (a : ℕ → TermModel T) : ℕ → TermModel T :=
  fun x => if x ∈ xs then termClass T (σ x) else a x

theorem closeAssignment_cons (T : Set (AlphaFormula L)) (σ : ℕ → L.Term Empty) (x : ℕ)
    (xs : List ℕ) (a : ℕ → TermModel T) :
    Function.update (closeAssignment T σ xs a) x (termClass T (σ x)) = closeAssignment T σ (x :: xs) a := by
  funext y
  by_cases hy : y = x <;> simp [closeAssignment, hy]

theorem closeAlong_realize (T : Set (AlphaFormula L)) (σ : ℕ → L.Term Empty) (φ : AlphaFormula L)
    (xs : List ℕ) (a : ℕ → TermModel T) :
    (closeAlong σ φ xs).Realize a ↔ φ.Realize (closeAssignment T σ xs a) := by
  induction xs generalizing φ with
  | nil => rfl
  | cons x xs ih =>
    rw [closeAlong, ih, realize_subst, realize_namedClosedTerm, closeAssignment_cons]

theorem closeAlong_realize_of_cover (T : Set (AlphaFormula L)) (σ : ℕ → L.Term Empty)
    (φ : AlphaFormula L) (xs : List ℕ) (hxs : φ.fv ⊆ xs.toFinset) (a : ℕ → TermModel T) :
    (closeAlong σ φ xs).Realize a ↔ φ.Realize (fun x => termClass T (σ x)) := by
  apply (closeAlong_realize T σ φ xs a).trans
  apply φ.realize_congr
  intro x hx
  have hm : x ∈ xs := by simpa using hxs hx
  simp [closeAssignment, hm]

/-- Any finite list covering the free variables gives the assignment truth clause. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally, substitute the chosen closed terms successively for all free variables of $\psi$.
    The free-variable formula for substitution shows that the result is a sentence. Repeated semantic substitution
    identifies its truth with the truth of $\psi$ under the assignment of those term classes. Assignment locality
    allows any assignment agreeing on the free variables, including $s$. The sentence case just proved therefore
    gives the stated assignment version.
-/
theorem termModel_truth_closeAlong {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) (φ : AlphaFormula L) (σ : ℕ → L.Term Empty) (xs : List ℕ)
    (hxs : φ.fv ⊆ xs.toFinset) :
    φ.Realize (fun x => termClass T (σ x)) ↔ closeAlong σ φ xs ∈ T := by
  have hc : closeAlong σ φ xs ∈ Sentences L := by
    change (closeAlong σ φ xs).fv = ∅
    rw [fv_closeAlong]
    exact Finset.sdiff_eq_empty_iff_subset.mpr hxs
  exact (closeAlong_realize_of_cover T σ φ xs hxs (fun x => termClass T (σ x))).symm.trans
    (termModel_truth_sentence hT hH _ hc _)

/-- Representatives need only agree with the assignment on the formula's free variables. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Truth lemma for the term model
-/
theorem termModel_truth_assignment {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) (φ : AlphaFormula L) (a : ℕ → TermModel T)
    (σ : ℕ → L.Term Empty) (xs : List ℕ) (hxs : φ.fv ⊆ xs.toFinset)
    (hσ : ∀ x ∈ φ.fv, termClass T (σ x) = a x) :
    φ.Realize a ↔ closeAlong σ φ xs ∈ T :=
  (φ.realize_congr a _ (fun x hx => (hσ x hx).symm)).trans
    (termModel_truth_closeAlong hT hH φ σ xs hxs)

/-- A fixed enumeration gives a canonical closed instance for a total representative assignment. -/
def closedInstance (φ : AlphaFormula L) (σ : ℕ → L.Term Empty) : AlphaFormula L :=
  closeAlong σ φ φ.fv.toList

@[simp] theorem fv_closedInstance (φ : AlphaFormula L) (σ : ℕ → L.Term Empty) :
    (closedInstance φ σ).fv = ∅ := by simp [closedInstance, fv_closeAlong]

theorem termModel_truth_closedInstance {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) (φ : AlphaFormula L) (σ : ℕ → L.Term Empty) :
    φ.Realize (fun x => termClass T (σ x)) ↔ closedInstance φ σ ∈ T :=
  termModel_truth_closeAlong hT hH φ σ φ.fv.toList (by simp)

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
