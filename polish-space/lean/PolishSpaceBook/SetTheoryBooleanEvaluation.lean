module

public import PolishSpaceBook.SetTheoryRelationFormulas

@[expose] public section

/-! # Partial Boolean evaluations on a well-founded set-coded relation

The true nodes form a subset of a downward closed domain. Union nodes use
existential quantification over their children; complement nodes negate it.
For a Borel expression a complement node has exactly one child. Other nodes
use the prescribed leaf truth set. No internal evaluation is assumed.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.BooleanEvaluation
open ZFSet
open scoped Classical
universe u

/-- Children are related to their parent by the set-coded relation R. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $T$ be a set of nodes and $R\IncludedIn T\times T$ a well-founded child relation, with
    $\langle t,s\rangle\in R$ meaning that $t$ is a child of $s$. Let $U,C,L\IncludedIn T$ be parameters.
    The sets $U$ and $C$ specify union and complement nodes; $L$ specifies the true leaves. Define
    $$\begin{aligned}
    \eta(E,s)&:\equiv\exists t\in T\;(\langle t,s\rangle\in R\land t\in E),\\
    \theta(E,s)&:\equiv
    \begin{cases}
    \eta(E,s),&s\in U,\\
    \neg\eta(E,s),&s\notin U,\ s\in C,\\
    s\in L,&s\notin U,\ s\notin C.
    \end{cases}
    \end{aligned}$$
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For an actual Borel code, each complement node has exactly one child. The construction below also allows
    arbitrary child sets, with a complement node negating the disjunction of its children.
-/
def Step (T R U C L E s : ZFSet.{u}) : Prop :=
  if s ∈ U then ∃ t ∈ T, pair t s ∈ R ∧ t ∈ E
  else if s ∈ C then ¬ ∃ t ∈ T, pair t s ∈ R ∧ t ∈ E
  else s ∈ L

/-- A partial assignment includes every child of every node in its domain. -/
def Partial (T R U C L D E : ZFSet.{u}) : Prop :=
  D ⊆ T ∧ E ⊆ D ∧
    (∀ s ∈ D, ∀ t ∈ T, pair t s ∈ R → t ∈ D) ∧
    ∀ s ∈ D, (s ∈ E ↔ Step T R U C L E s)

lemma step_congr {T R U C L E F s : ZFSet.{u}}
    (h : ∀ t ∈ T, pair t s ∈ R → (t ∈ E ↔ t ∈ F)) :
    Step T R U C L E s ↔ Step T R U C L F s := by
  have he : (∃ t ∈ T, pair t s ∈ R ∧ t ∈ E) ↔ ∃ t ∈ T, pair t s ∈ R ∧ t ∈ F := by
    constructor
    · rintro ⟨t, ht, hr, he⟩
      exact ⟨t, ht, hr, (h t ht hr).mp he⟩
    · rintro ⟨t, ht, hr, he⟩
      exact ⟨t, ht, hr, (h t ht hr).mpr he⟩
  unfold Step
  split_ifs <;> simp only [he]

/-- Two partial assignments agree on their common domain, by induction on children. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Agreement of partial Boolean evaluations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Induct on the well-founded child relation. Every child of a node in both domains belongs to both domains.
    The induction hypothesis therefore identifies its truth value in the two evaluations, so it also identifies
    the existential child test $\eta$. Negation preserves this agreement, and a leaf uses the same parameter $L$.
    The defining equations for the two partial evaluations now give the assertion at the parent.
-/
theorem Partial.agree {T R U C L D E D' E' : ZFSet.{u}}
    (hw : WellFounded (fun t s : T => pair t.val s.val ∈ R))
    (h : Partial T R U C L D E) (h' : Partial T R U C L D' E') :
    ∀ s ∈ D, s ∈ D' → (s ∈ E ↔ s ∈ E') := by
  have aux : ∀ s : T, s.val ∈ D → s.val ∈ D' → (s.val ∈ E ↔ s.val ∈ E') := by
    intro s
    induction s using hw.induction with
    | h s ih =>
      intro hs hs'
      rw [h.2.2.2 s.val hs, h'.2.2.2 s.val hs']
      apply step_congr
      intro t ht hr
      exact ih ⟨t, ht⟩ hr (h.2.2.1 s.val hs t ht hr) (h'.2.2.1 s.val hs' t ht hr)
  exact fun s hs hs' => aux ⟨s, h.1 hs⟩ hs hs'

/-- Agreement identifies complete assignments as actual sets. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The agreement lemma gives uniqueness even among external complete evaluations.
-/
theorem Partial.unique {T R U C L E F : ZFSet.{u}}
    (hw : WellFounded (fun t s : T => pair t.val s.val ∈ R))
    (hE : Partial T R U C L T E) (hF : Partial T R U C L T F) : E = F := by
  apply ZFSet.ext
  intro s
  by_cases hs : s ∈ T
  · exact hE.agree hw hF s hs hs
  · exact iff_of_false (fun he => hs (hE.2.1 he)) (fun hf => hs (hF.2.1 hf))

/-- Add a node once all its children are already evaluated. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Old nodes retain their values, since their children already lie
    in $D_*$; the new node satisfies its equation by construction. Thus $\sigma(D',E')$ holds.
-/
theorem Partial.extend {T R U C L D E s : ZFSet.{u}}
    (h : Partial T R U C L D E) (hs : s ∈ T) (hsD : s ∉ D)
    (hchildren : ∀ t ∈ T, pair t s ∈ R → t ∈ D) :
    Partial T R U C L (insert s D) (if Step T R U C L E s then insert s E else E) := by
  let F := if Step T R U C L E s then insert s E else E
  have hagree {t} (ht : t ∈ D) : t ∈ F ↔ t ∈ E := by
    have hne : t ≠ s := fun he => hsD (he ▸ ht)
    dsimp [F]
    split_ifs <;> simp [ZFSet.mem_insert_iff, hne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases ZFSet.mem_insert_iff.mp ht with rfl | ht
    · exact hs
    · exact h.1 ht
  · intro t ht
    change t ∈ F at ht
    by_cases he : Step T R U C L E s
    · simp only [F, he, ite_true, ZFSet.mem_insert_iff] at ht
      exact ZFSet.mem_insert_iff.mpr (ht.imp_right (fun ht => h.2.1 ht))
    · simp only [F, he, ite_false] at ht
      exact ZFSet.mem_insert_iff.mpr (Or.inr (h.2.1 ht))
  · intro a ha t ht hr
    rcases ZFSet.mem_insert_iff.mp ha with rfl | ha
    · exact ZFSet.mem_insert_iff.mpr (Or.inr (hchildren t ht hr))
    · exact ZFSet.mem_insert_iff.mpr (Or.inr (h.2.2.1 a ha t ht hr))
  · intro a ha
    rcases ZFSet.mem_insert_iff.mp ha with heq | ha
    · subst a
      have he := step_congr (T := T) (R := R) (U := U) (C := C) (L := L)
        (s := s) (E := F) (F := E) (fun t ht hr => hagree (hchildren t ht hr))
      change s ∈ F ↔ Step T R U C L F s
      rw [he]
      have hsE : s ∉ E := fun he => hsD (h.2.1 he)
      dsimp [F]
      split_ifs <;> simp_all [ZFSet.mem_insert_iff]
    · change a ∈ F ↔ Step T R U C L F a
      rw [hagree ha, step_congr (fun t ht hr => hagree (h.2.2.1 a ha t ht hr)), h.2.2.2 a ha]

end PolishSpaceBook.SetTheoryModels.BooleanEvaluation
