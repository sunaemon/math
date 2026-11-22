module

public import PolishSpaceBook.SetTheoryChoice
public import PolishSpaceBook.SetTheoryInternalRecursion

@[expose] public section

/-! # An internally definable rule for selecting a previously unused element -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Fix this graph $c$. For any proposed preceding graph $g\in M$, let
    $$r_g:=\{z\in W:z\notin\GraphRange{g}\}.$$
-/
def remainingSet (W g : ZFSet.{u}) : ZFSet.{u} := W.sep (fun b => b ∉ graphRange g)

lemma mem_remainingSet {W g b : ZFSet.{u}} :
    b ∈ remainingSet W g ↔ b ∈ W ∧ b ∉ graphRange g := ZFSet.mem_sep

def remainingFormula {n : ℕ} (W g r : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) r.castSucc).iff
    (memberAt (Fin.last n) W.castSucc ⊓ (rangeMemberFormula g.castSucc (Fin.last n)).not)).all

lemma realize_remainingFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) {n : ℕ} (W g r : Fin n) (xs : Fin n → M) :
    (remainingFormula W g r).Realize Empty.elim xs ↔
      (xs r).val = remainingSet (xs W).val (xs g).val := by
  simp only [remainingFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, realize_memberAt_model,
    realize_rangeMemberFormula hM hunion, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h
    apply ZFSet.ext
    intro b
    rw [mem_remainingSet]
    constructor
    · intro hb
      exact (h ⟨b, hM.mem_trans hb (xs r).property⟩).mp hb
    · intro hb
      exact (h ⟨b, hM.mem_trans hb.1 (xs W).property⟩).mpr hb
  · intro he b
    rw [he, mem_remainingSet]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The range-membership predicate and Separation give $r_g\in M$, even when $g$ is not a function graph.
-/
lemma remainingSet_mem {M W g : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1).not)
    (hW : W ∈ M) (hg : g ∈ M) : remainingSet W g ∈ M := by
  apply separation_mem_of_absolute hM (rangeMemberFormula (0 : Fin 2) 1).not hsep
    ![⟨g, hg⟩] hW (fun b => b ∉ graphRange g)
  intro b _
  simp only [BoundedFormula.realize_not, realize_rangeMemberFormula hM hunion, Fin.snoc]
  rfl

def freshValue (r c : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ b, b ∈ r ∧ pair r b ∈ c then h.choose else ∅

lemma freshValue_spec {M W c r : ZFSet.{u}}
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W) W c)
    (hs : ∀ a ∈ internalNonemptySubsets M W, ∃ b ∈ a, pair a b ∈ c)
    (hr : r ∈ M) (hrW : r ⊆ W) (b : ZFSet.{u}) :
    b = freshValue r c ↔
      (b ∈ r ∧ pair r b ∈ c) ∨ ((¬ ∃ z, z ∈ r) ∧ b = ∅) := by
  classical
  by_cases h : ∃ z, z ∈ r
  · have hS : r ∈ internalNonemptySubsets M W := mem_internalNonemptySubsets.mpr ⟨⟨hr, hrW⟩, h⟩
    have hex : ∃ b, b ∈ r ∧ pair r b ∈ c := hs r hS
    have he := hex.choose_spec
    rw [freshValue, dite_eq_left hex]
    constructor
    · rintro rfl
      exact Or.inl he
    · rintro (hb | hb)
      · obtain ⟨v, _, hv⟩ := hc.2 r hS
        exact (hv b hb.2).trans (hv hex.choose he.2).symm
      · exact False.elim (hb.1 h)
  · have hn : ¬ ∃ b, b ∈ r ∧ pair r b ∈ c := fun ⟨b, hb, _⟩ => h ⟨b, hb⟩
    rw [freshValue, dite_eq_right hn]
    exact ⟨fun hb => Or.inr ⟨h, hb⟩, fun hb => hb.elim
      (fun hb => False.elim (h ⟨b, hb.1⟩)) And.right⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Define the total step rule
    $$H(a,g):=\begin{cases}
    c(r_g),&r_g\ne\emptyset,\\
    \emptyset,&r_g=\emptyset.
    \end{cases}$$
-/
def freshStep (W c _a g : ZFSet.{u}) : ZFSet.{u} := freshValue (remainingSet W g) c

/-- Parameters W, c; input a, preceding graph g, output b. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For parameters $W,c$, an internal defining formula for the step is
    $$\begin{aligned}
    \theta(W,c,a,g,b)\;:\equiv\;\exists r\,\bigl[&
     \forall z\,(z\in r\leftrightarrow
       (z\in W\land\neg\exists t\,\langle t,z\rangle\in g))\\
     &{}\land\bigl((b\in r\land\langle r,b\rangle\in c)
           \lor(r=\emptyset\land b=\emptyset)\bigr)\bigr].
    \end{aligned}$$
    Here $r=\emptyset$ means $\neg\exists z\,(z\in r)$, and similarly for $b$.
-/
def freshStepFormula : ForcingFormulas.Formula 5 :=
  (remainingFormula (0 : Fin 6) 3 5 ⊓
    ((memberAt 4 5 ⊓ pairMemberFormula 1 5 4) ⊔
      ((orderNonemptyFormula 5).not ⊓ (orderNonemptyFormula 4).not))).ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The range formula identifies the internal witness $r$ with $r_g$.
    If $r_g$ is nonempty, the choice graph makes the first disjunct specify exactly one $b$ and rules out the second.
    If $r_g$ is empty, the first disjunct is impossible and the second specifies $b=\emptyset$.
    Consequently
    $$M\models\theta(W,c,a,g,b)\quad\Longleftrightarrow\quad b=H(a,g).$$
-/
lemma realize_freshStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1).not)
    (W c a g b : M)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val) :
    freshStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ![W, c] a) g) b) ↔
      b.val = freshStep W.val c.val a.val g.val := by
  have hzero (x : ZFSet.{u}) : (¬ ∃ z, z ∈ x) ↔ x = ∅ := by
    rw [ZFSet.eq_empty, not_exists]
  simp only [freshStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_sup, BoundedFormula.realize_not, realize_remainingFormula hM hunion,
    realize_memberAt_model, realize_pairMemberFormula_model hM, realize_orderNonemptyFormula hM, Fin.snoc]
  have hr := remainingSet_mem hM hunion hsep W.property g.property
  have hrW : remainingSet W.val g.val ⊆ W.val := fun _ hb => (mem_remainingSet.mp hb).1
  have hf := freshValue_spec hc hs hr hrW b.val
  constructor
  · rintro ⟨r, hrEq, hb⟩
    apply hf.mpr
    rw [hrEq] at hb
    exact hb.imp id (fun h => ⟨h.1, (hzero _).mp h.2⟩)
  · intro hb
    refine ⟨⟨remainingSet W.val g.val, hr⟩, rfl, ?_⟩
    exact (hf.mp hb).imp id (fun h => ⟨h.1, (hzero _).mpr h.2⟩)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The input $a$ does not enter this rule. In the nonempty case, $r_g\in S$, so $c(r_g)$ is uniquely defined
    and belongs to $r_g\IncludedIn W$. In the empty case, Infinity gives $\emptyset\in M$.
    Thus $H(a,g)\in M$ for every $a,g\in M$.
-/
lemma freshStep_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hzero : (∅ : ZFSet.{u}) ∈ M) (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1).not)
    (W c a g : M)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val) :
    freshStep W.val c.val a.val g.val ∈ M := by
  have hr := remainingSet_mem hM hunion hsep W.property g.property
  have hrW : remainingSet W.val g.val ⊆ W.val := fun _ hb => (mem_remainingSet.mp hb).1
  rcases (freshValue_spec hc hs hr hrW _).mp rfl with h | h
  · exact hM.mem_trans h.1 hr
  · change freshValue (remainingSet W.val g.val) c.val ∈ M
    rw [h.2]
    exact hzero

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    If the remaining set is nonempty, its selected element belongs to that set, which gives the last assertion.
-/
lemma freshStep_fresh {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1).not)
    (W c a g : M)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val)
    (hne : ∃ z, z ∈ remainingSet W.val g.val) :
    freshStep W.val c.val a.val g.val ∈ W.val ∧
      freshStep W.val c.val a.val g.val ∉ graphRange g.val := by
  have hr := remainingSet_mem hM hunion hsep W.property g.property
  have hrW : remainingSet W.val g.val ⊆ W.val := fun _ hb => (mem_remainingSet.mp hb).1
  rcases (freshValue_spec hc hs hr hrW _).mp rfl with h | h
  · exact mem_remainingSet.mp h.1
  · exact False.elim (h.1 hne)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal selection recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The step is internally defined and has values in $M$, so the internal membership-recursion theorem in
    §{sec:internal-model-closure} supplies the unique graph on $A$.
-/
theorem internal_fresh_recursion {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hzero : (∅ : ZFSet.{u}) ∈ M)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (W c A : M) (hA : A.val.IsTransitive)
    (hc : ZFSet.IsFunc (internalNonemptySubsets M W.val) W.val c.val)
    (hs : ∀ r ∈ internalNonemptySubsets M W.val, ∃ z ∈ r, pair r z ∈ c.val) :
    ∃! f : M, IsRecursiveSolution (freshStep W.val c.val) A.val f.val :=
  internal_membership_recursion hM hpair hunion hpower hsep hrep freshStepFormula ![W, c]
    (freshStep W.val c.val) (fun a g b => realize_freshStepFormula hM hunion (hsep _) W c a g b hc hs)
    (fun a g => freshStep_mem hM hzero hunion (hsep _) W c a g hc hs) A hA

end PolishSpaceBook.SetTheoryModels
