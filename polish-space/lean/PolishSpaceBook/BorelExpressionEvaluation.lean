module

public import PolishSpaceBook.BorelStructure

@[expose] public section

/-!
# Evaluation of externally labelled Borel expression trees

A natural-number label at each finite word means absent (0), union (1),
complement (2), or basic set n (n + 3). Validity is a condition on this
external tree, not built into an inductive type. Well-founded recursion
gives its semantics and proves existence and uniqueness of truth assignments.
The witness certificate additionally chooses a true child at every true
union node. Relative computability of the certificate tests and the
coanalytic classification of validity are separate obligations.
-/

namespace PolishSpaceBook
open Set

abbrev BorelExpression := List ℕ → ℕ

namespace BorelExpression

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    To use a Borel code as a real parameter, record its constructors in a sequence of natural numbers.
    A finite sequence $s$ specifies a position in the data: $\emptyset$ denotes the whole code, and $s\concat(k)$
    denotes the position of the $k$-th immediate subcode of the code at $s$.
-/
def Child (c : BorelExpression) (t s : List ℕ) : Prop :=
  c s ≠ 0 ∧ ∃ k, t = s ++ [k] ∧ c t ≠ 0

/-- The book's syntax, including nonempty union nodes and unique complement
children. No restriction on the height other than well-foundedness is made. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Use numerical labels $c(s)$ on finite words: zero means absent, one means union, two means complement,
    and $k+3$ means the basic cylinder $U_k:=\cyl{\LambdaListDecode{k}}$.
    A valid expression has a present root, a prefix-closed set of present nodes, no children at a leaf,
    at least one child at a union, exactly one child at a complement, and no infinite branch.
    These are the expression trees of §{sec:borel-codes}, with numerical labels and the list coding of
    §{sec:lambda-finite-lists}.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an actual Borel code, each complement node has exactly one child. The construction below also allows
    arbitrary child sets, with a complement node negating the disjunction of its children.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The labels are zero for an absent node, one for a union, two for a complement, and numbers at least
    three for basic-cylinder leaves. The structural conditions require a present root, prefix closure of
    present nodes, no children at a leaf, a present child at a union, and exactly one present child at a
    complement. Well-foundedness means that there is no infinite chain of present children. In this section,
    the label program is total jointly in the family index and the word code at the fixed parameter.
-/
def Valid (c : BorelExpression) : Prop :=
  c [] ≠ 0 ∧
  (∀ s k, c (s ++ [k]) ≠ 0 → c s ≠ 0) ∧
  (∀ s, 3 ≤ c s → ∀ k, c (s ++ [k]) = 0) ∧
  (∀ s, c s = 1 → ∃ k, c (s ++ [k]) ≠ 0) ∧
  (∀ s, c s = 2 → ∃! k, c (s ++ [k]) ≠ 0) ∧
  WellFounded c.Child

/-- Nodewise clauses, formulated for arbitrary candidate set assignments. -/
def SetEvaluation {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (A : List ℕ → Set X) : Prop :=
  ∀ s, A s = if c s = 0 then ∅ else
    if c s = 1 then ⋃ (k : ℕ) (_ : c (s ++ [k]) ≠ 0), A (s ++ [k]) else
    if c s = 2 then (⋃ (k : ℕ) (_ : c (s ++ [k]) ≠ 0), A (s ++ [k]))ᶜ else U (c s - 3)

def evalStep {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (s : List ℕ) (rec : ∀ t, c.Child t s → Set X) : Set X :=
  if hs : c s = 0 then ∅ else
    if c s = 1 then ⋃ (k : ℕ) (hk : c (s ++ [k]) ≠ 0), rec (s ++ [k]) ⟨hs, k, rfl, hk⟩ else
    if c s = 2 then (⋃ (k : ℕ) (hk : c (s ++ [k]) ≠ 0), rec (s ++ [k]) ⟨hs, k, rfl, hk⟩)ᶜ else U (c s - 3)

noncomputable def evaluate {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) : List ℕ → Set X := hw.fix (evalStep c U)

theorem evaluate_isEvaluation {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) : c.SetEvaluation U (c.evaluate hw U) := by
  intro s
  rw [evaluate, hw.fix_eq]
  unfold evalStep
  by_cases hs : c s = 0 <;> simp only [hs, dite_true, dite_false, ite_true, ite_false]

theorem SetEvaluation.unique {X : Type*} {c : BorelExpression} (hw : WellFounded c.Child)
    {U : ℕ → Set X} {A B : List ℕ → Set X}
    (hA : c.SetEvaluation U A) (hB : c.SetEvaluation U B) : A = B := by
  funext s
  induction s using hw.induction with
  | h s ih =>
    rw [hA s, hB s]
    by_cases hs : c s = 0
    · simp [hs]
    · have hchildren : (⋃ (k : ℕ) (_ : c (s ++ [k]) ≠ 0), A (s ++ [k])) =
          ⋃ (k : ℕ) (_ : c (s ++ [k]) ≠ 0), B (s ++ [k]) := by
        apply iUnion_congr
        intro k
        apply iUnion_congr
        intro hk
        exact ih (s ++ [k]) ⟨hs, k, rfl, hk⟩
      simp only [hs, ite_false, hchildren]

theorem existsUnique_setEvaluation {X : Type*} (c : BorelExpression)
    (hw : WellFounded c.Child) (U : ℕ → Set X) : ∃! A, c.SetEvaluation U A :=
  ⟨c.evaluate hw U, c.evaluate_isEvaluation hw U,
    fun _ hA => hA.unique hw (c.evaluate_isEvaluation hw U)⟩

/-- The external tree evaluates to Borel sets whenever its leaves do. -/
theorem measurableSet_evaluate {X : Type*} [MeasurableSpace X]
    (c : BorelExpression) (hw : WellFounded c.Child) (U : ℕ → Set X)
    (hU : ∀ n, MeasurableSet (U n)) (s : List ℕ) : MeasurableSet (c.evaluate hw U s) := by
  induction s using hw.induction with
  | h s ih =>
    rw [c.evaluate_isEvaluation hw U s]
    by_cases h0 : c s = 0
    · simp [h0]
    · have hu : MeasurableSet (⋃ (k : ℕ) (_ : c (s ++ [k]) ≠ 0), c.evaluate hw U (s ++ [k])) :=
        MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk =>
          ih (s ++ [k]) ⟨h0, k, rfl, hk⟩
      simp only [h0, ite_false]
      split_ifs
      · exact hu
      · exact hu.compl
      · exact hU _

/-- Real-coded evaluations will use a Boolean at every finite word. -/
def TruthAssignment {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (x : X) (v : List ℕ → Bool) : Prop :=
  ∀ s, (v s = true ↔ if c s = 0 then False else
    if c s = 1 then ∃ k, c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true else
    if c s = 2 then ¬ ∃ k, c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true else x ∈ U (c s - 3))

noncomputable def truthValues {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) (x : X) : List ℕ → Bool := by
  classical
  exact fun s => decide (x ∈ c.evaluate hw U s)

theorem truthValues_isAssignment {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) (x : X) : c.TruthAssignment U x (c.truthValues hw U x) := by
  classical
  intro s
  simp only [truthValues, decide_eq_true_eq]
  rw [c.evaluate_isEvaluation hw U s]
  by_cases h0 : c s = 0 <;> by_cases h1 : c s = 1 <;> by_cases h2 : c s = 2 <;>
    simp [h0, h1, h2]


theorem TruthAssignment.unique {X : Type*} {c : BorelExpression} (hw : WellFounded c.Child)
    {U : ℕ → Set X} {x : X} {v w : List ℕ → Bool}
    (hv : c.TruthAssignment U x v) (hw' : c.TruthAssignment U x w) : v = w := by
  funext s
  induction s using hw.induction with
  | h s ih =>
    apply Bool.eq_iff_iff.mpr
    rw [hv s, hw' s]
    by_cases h0 : c s = 0
    · simp [h0]
    · have he : (∃ k, c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true) ↔
          ∃ k, c (s ++ [k]) ≠ 0 ∧ w (s ++ [k]) = true := by
        apply exists_congr
        intro k
        apply and_congr_right
        intro hk
        rw [ih (s ++ [k]) ⟨h0, k, rfl, hk⟩]
      simp only [h0, ite_false]
      split_ifs <;> simp [he]

theorem truthAssignment_iff {X : Type*} (c : BorelExpression) (hw : WellFounded c.Child)
    (U : ℕ → Set X) (x : X) (v : List ℕ → Bool) :
    c.TruthAssignment U x v ↔ v = c.truthValues hw U x :=
  ⟨fun h => h.unique hw (c.truthValues_isAssignment hw U x),
    fun h => h ▸ c.truthValues_isAssignment hw U x⟩

/-- Union truth carries a chosen true child; every true child forces its
parent true. These universal clauses remove the existential child search
from the eventual finite certificate tests. -/
def EvaluationCertificate {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (x : X) (v : List ℕ → Bool) (choice : List ℕ → ℕ) : Prop :=
  ∀ s,
    (c s = 0 → v s = false) ∧
    (c s = 1 → (v s = true → c (s ++ [choice s]) ≠ 0 ∧ v (s ++ [choice s]) = true) ∧
      (∀ k, c (s ++ [k]) ≠ 0 → v (s ++ [k]) = true → v s = true)) ∧
    (c s = 2 → ∀ k, c (s ++ [k]) ≠ 0 → v s = !v (s ++ [k])) ∧
    (3 ≤ c s → (v s = true ↔ x ∈ U (c s - 3)))

theorem certificate_iff_assignment {X : Type*} (c : BorelExpression) (hc : c.Valid)
    (U : ℕ → Set X) (x : X) (v : List ℕ → Bool) :
    (∃ choice, c.EvaluationCertificate U x v choice) ↔ c.TruthAssignment U x v := by
  classical
  constructor
  · rintro ⟨choice, h⟩ s
    rcases h s with ⟨h0, h1, h2, hleaf⟩
    by_cases hs0 : c s = 0
    · simp [hs0, h0 hs0]
    by_cases hs1 : c s = 1
    · simp only [hs1, ite_true]
      exact ⟨fun hv => ⟨choice s, (h1 hs1).1 hv⟩, fun ⟨k, hk, hv⟩ => (h1 hs1).2 k hk hv⟩
    by_cases hs2 : c s = 2
    · simp only [hs2, ite_true]
      obtain ⟨k, hk, hku⟩ := hc.2.2.2.2.1 s hs2
      rw [h2 hs2 k hk]
      have he : (∃ j, c (s ++ [j]) ≠ 0 ∧ v (s ++ [j]) = true) ↔ v (s ++ [k]) = true := by
        constructor
        · rintro ⟨j, hj, hv⟩
          simpa only [hku j hj] using hv
        · exact fun hv => ⟨k, hk, hv⟩
      rw [he]
      cases v (s ++ [k]) <;> simp
    · simpa [hs0, hs1, hs2] using hleaf (by omega)
  · intro hv
    have hex : ∀ s, ∃ k, c s = 1 → v s = true →
        c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true := by
      intro s
      by_cases hs : c s = 1 ∧ v s = true
      · obtain ⟨k, hk⟩ := (hv s).mp hs.2 |> (by simpa [hs.1] using ·)
        exact ⟨k, fun _ _ => hk⟩
      · exact ⟨0, fun h1 ht => (hs ⟨h1, ht⟩).elim⟩
    choose choice hchoice using hex
    refine ⟨choice, fun s => ⟨?_, ?_, ?_, ?_⟩⟩
    · intro h0
      have hn : v s ≠ true := by simpa [h0] using (hv s).mp
      cases hvs : v s <;> simp_all
    · intro h1
      refine ⟨hchoice s h1, ?_⟩
      intro k hk htk
      exact (hv s).mpr (by simpa [h1] using (show ∃ k, c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true from ⟨k, hk, htk⟩))
    · intro h2 k hk
      apply Bool.eq_iff_iff.mpr
      have he : (∃ j, c (s ++ [j]) ≠ 0 ∧ v (s ++ [j]) = true) ↔ v (s ++ [k]) = true := by
        obtain ⟨j, hj, hju⟩ := hc.2.2.2.2.1 s h2
        constructor
        · rintro ⟨i, hi, hvi⟩
          have hik : i = k := (hju i hi).trans (hju k hk).symm
          simpa [hik] using hvi
        · exact fun ht => ⟨k, hk, ht⟩
      rw [hv s]
      simp [h2, he]
    · intro hleaf
      simpa [show c s ≠ 0 by omega, show c s ≠ 1 by omega, show c s ≠ 2 by omega] using hv s

/-- Membership and nonmembership are witnessed by the same local clauses;
only the requested root bit changes. -/
theorem certificate_root_iff {X : Type*} (c : BorelExpression) (hc : c.Valid)
    (U : ℕ → Set X) (x : X) (b : Bool) :
    (∃ v choice, c.EvaluationCertificate U x v choice ∧ v [] = b) ↔
      (c.truthValues hc.2.2.2.2.2 U x) [] = b := by
  constructor
  · rintro ⟨v, choice, hv, hb⟩
    have ha := (c.certificate_iff_assignment hc U x v).mp ⟨choice, hv⟩
    rwa [(c.truthAssignment_iff hc.2.2.2.2.2 U x v).mp ha] at hb
  · intro hb
    obtain ⟨choice, hv⟩ := (c.certificate_iff_assignment hc U x _).mpr
      (c.truthValues_isAssignment hc.2.2.2.2.2 U x)
    exact ⟨_, choice, hv, hb⟩

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    For a candidate code, assign a truth bit $u_s$ to every finite word $s$, with value $0$ at unused positions.
    At a leaf specifying $U_n$, require $u_s=1$ exactly when $x\in U_n$.
    At a complement position, require opposite bits at that position and each present immediate subcode.
    At a union position with bit $1$, store a selected subcode number $j_s$ and require that the subcode is present and
    has bit $1$.
    Conversely, any present subcode with bit $1$ must force its containing union to have bit $1$.
    The numbers $j_s$ at all other positions are immaterial. These conditions define a certificate relation on all candidate
    codes, without first testing validity.
-/
/-- Each clause uses only finitely many coordinates; all child and leaf
indices are universally quantified. This form is suitable for closed-tree
presentations and for effective finite tests. -/
def LocalCertificate {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (x : X) (v : List ℕ → Bool) (choice : List ℕ → ℕ) : Prop :=
  ∀ s,
    (c s = 0 → v s = false) ∧
    (∀ k, c s = 1 → v s = true → choice s = k →
      c (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) = true) ∧
    (∀ k, c s = 1 → c (s ++ [k]) ≠ 0 → v (s ++ [k]) = true → v s = true) ∧
    (∀ k, c s = 2 → c (s ++ [k]) ≠ 0 → v s = !v (s ++ [k])) ∧
    (∀ n, c s = n + 3 → (v s = true ↔ x ∈ U n))

theorem certificate_iff_local {X : Type*} (c : BorelExpression) (U : ℕ → Set X)
    (x : X) (v : List ℕ → Bool) (choice : List ℕ → ℕ) :
    c.EvaluationCertificate U x v choice ↔ c.LocalCertificate U x v choice := by
  constructor
  · intro h s
    rcases h s with ⟨h0, hu, hn, hl⟩
    refine ⟨h0, ?_, fun k h1 hk ht => (hu h1).2 k hk ht, fun k h2 => hn h2 k, ?_⟩
    · rintro k h1 ht rfl
      exact (hu h1).1 ht
    · intro n heq
      simpa [heq] using hl (by omega)
  · intro h s
    rcases h s with ⟨h0, hu, hd, hn, hl⟩
    refine ⟨h0, fun h1 => ⟨fun ht => hu (choice s) h1 ht rfl,
      fun k hk ht => hd k h1 hk ht⟩, fun h2 k => hn k h2, ?_⟩
    intro hs
    exact hl (c s - 3) (by omega)

end BorelExpression
end PolishSpaceBook
