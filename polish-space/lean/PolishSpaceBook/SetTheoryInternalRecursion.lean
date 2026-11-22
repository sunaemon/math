module

public import PolishSpaceBook.SetTheoryHullSolutions

@[expose] public section

/-! # Internal existence for membership recursion on a transitive set

The model hypotheses are actual first-order axiom instances. Canonical domains
make the previously defined partial-solution formula single-valued, so that
Replacement collects the graphs before Union and one-point extension are used.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma subset_hullUnion {M A X : ZFSet.{u}} (hXA : X ⊆ A) : X ⊆ hullUnion M A X := by
  intro a ha
  exact ZFSet.mem_iUnion.mpr ⟨⟨a, ha⟩, mem_internalHull (hXA ha)⟩

lemma hullUnion_subset {M A X : ZFSet.{u}} : hullUnion M A X ⊆ A := by
  intro z hz
  obtain ⟨a, ha⟩ := ZFSet.mem_iUnion.mp hz
  exact internalHull_subset M A a.val ha

lemma hullUnion_subset_of_transitive {M A X D : ZFSet.{u}} (hD : D ∈ M) (hDA : D ⊆ A)
    (hDt : D.IsTransitive) (hXD : X ⊆ D) : hullUnion M A X ⊆ D := by
  intro z hz
  obtain ⟨a, ha⟩ := ZFSet.mem_iUnion.mp hz
  exact internalHull_minimal hD hDA hDt (hXD a.property) ha

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Finally apply the same collection formula to all $a\in A$ and take the union of the graphs.
    Since $a\in D_a\IncludedIn A$ for every input, $\bigcup_{a\in A}D_a=A$.
    The resulting graph $F\in M$ is therefore a solution on $A$, and the agreement lemma proves uniqueness.
    \end{proof}
-/
lemma hullUnion_self (M A : ZFSet.{u}) : hullUnion M A A = A := by
  apply ZFSet.ext
  intro z
  exact ⟨fun h => hullUnion_subset h, fun h => subset_hullUnion (fun _ h => h) h⟩

/-- Membership induction constructs a solution on each canonical internal domain. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    We now prove by membership induction on $a\in A$ that a solution on $D_a$ belongs to $M$.
    For every $b\in a$, the induction hypothesis supplies the unique solution $f_b\in M$ on $D_b$.
    Since $a\in M$, the preceding collection and gluing argument gives
    $$U:=\bigcup_{b\in a}D_b\in M,\qquad f:=\bigcup_{b\in a}f_b\in M,$$
    where $f$ is a partial solution on $U$. Each $b\in a$ lies in $D_b$, so $a\IncludedIn U$.
    Also $U\IncludedIn D_a$: transitivity of $D_a$ puts each such $b$ in $D_a$, and minimality gives
    $D_b\IncludedIn D_a$.

    If $a\in U$, minimality gives $D_a\IncludedIn U$, so $U=D_a$ and $f$ is the required solution.
    Otherwise, the restriction belongs to $M$, and the step-rule closure assumption gives
    $$v:=H(a,\restrict{f}{a})\in M.$$
    The one-point extension lemma puts a solution on $W:=U\cup\{a\}$ in $M$.
    Here $W$ is transitive, belongs to $M$, contains $a$, and satisfies
    $W\IncludedIn D_a\IncludedIn A$. Minimality gives $D_a\IncludedIn W$, hence $W=D_a$.
    This completes the induction, including the case of an empty predecessor set.
-/
theorem internal_solution_on_hull {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (hclosed : ∀ a g : M, H a.val g.val ∈ M) (A : M) (hA : A.val.IsTransitive) :
    ∀ a ∈ A.val, ∃ f ∈ M, IsRecursiveSolution H (internalHull M A.val a) f := by
  intro a
  induction a using ZFSet.inductionOn with
  | h a ih =>
    intro haA
    have haM : a ∈ M := hM.mem_trans haA A.property
    have hlocal : ∀ b : a, ∃ f : M, IsRecursiveSolution H (internalHull M A.val b.val) f.val := by
      intro b
      obtain ⟨f, hfM, hf⟩ := ih b.val b.property (hA.mem_trans b.property haA)
      exact ⟨⟨f, hfM⟩, hf⟩
    obtain ⟨hU, f, hfM, hf⟩ := collect_hull_solutions hM hunion hpower hsep hrep ψ ps H hH A haM hlocal
    let U := hullUnion M A.val a
    have hHullM : internalHull M A.val a ∈ M := internalHull_mem hM hpower (hsep _) A.property haM
    have haHull : a ∈ internalHull M A.val a := mem_internalHull haA
    have hUt : U.IsTransitive := hf.domain_transitive
    have hcover : a ⊆ U := subset_hullUnion (hA.subset_of_mem haA)
    have hUsub : U ⊆ internalHull M A.val a :=
      hullUnion_subset_of_transitive hHullM (internalHull_subset M A.val a)
        (internalHull_transitive hA) ((internalHull_transitive hA).subset_of_mem haHull)
    by_cases haU : a ∈ U
    · have hHullSub : internalHull M A.val a ⊆ U :=
        internalHull_minimal hU hullUnion_subset hUt haU
      have he : U = internalHull M A.val a := ZFSet.ext (fun _ => ⟨fun hz => hUsub hz, fun hz => hHullSub hz⟩)
      exact ⟨f, hfM, he ▸ hf⟩
    · have hgM : restrictGraph f a ∈ M := restrictGraph_mem hM hunion (hsep _) hfM haM
      have hvM : H a (restrictGraph f a) ∈ M := hclosed ⟨a, haM⟩ ⟨_, hgM⟩
      obtain ⟨hW, hg, hsol⟩ := recursive_solution_extend_mem hM hpair hunion hf haU hcover hU hfM haM hvM
      have hWsub : insert a U ⊆ internalHull M A.val a := by
        intro z hz
        rcases ZFSet.mem_insert_iff.mp hz with rfl | hzU
        · exact haHull
        · exact hUsub hzU
      have hWA : insert a U ⊆ A.val := fun _ hz => internalHull_subset M A.val a (hWsub hz)
      have hHullSub : internalHull M A.val a ⊆ insert a U :=
        internalHull_minimal hW hWA hsol.domain_transitive (ZFSet.mem_insert a U)
      have he : insert a U = internalHull M A.val a :=
        ZFSet.ext (fun _ => ⟨fun hz => hWsub hz, fun hz => hHullSub hz⟩)
      exact ⟨_, hg, he ▸ hsol⟩

/-- The unique solution on any internal transitive set belongs to the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal membership recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This theorem needs no Choice axiom in the model: each collected graph is uniquely specified by a formula.
    It applies once an internal transitive domain and an internally defined step rule preserving membership in
    $M$ have been supplied.
-/
theorem internal_membership_recursion {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (hclosed : ∀ a g : M, H a.val g.val ∈ M) (A : M) (hA : A.val.IsTransitive) :
    ∃! f : M, IsRecursiveSolution H A.val f.val := by
  have hlocal : ∀ a : A.val, ∃ f : M, IsRecursiveSolution H (internalHull M A.val a.val) f.val := by
    intro a
    obtain ⟨f, hfM, hf⟩ := internal_solution_on_hull hM hpair hunion hpower hsep hrep ψ ps H hH hclosed
      A hA a.val a.property
    exact ⟨⟨f, hfM⟩, hf⟩
  obtain ⟨_, f, hfM, hf⟩ := collect_hull_solutions hM hunion hpower hsep hrep ψ ps H hH A A.property hlocal
  rw [hullUnion_self] at hf
  exact ⟨⟨f, hfM⟩, hf, fun g hg => Subtype.ext (recursive_solution_unique hg hf)⟩

end PolishSpaceBook.SetTheoryModels
