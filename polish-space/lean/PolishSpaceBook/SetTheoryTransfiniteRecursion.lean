module

public import PolishSpaceBook.SetTheoryRecursiveSolutions
public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-! # Transfinite induction and recursion by compatible initial solutions

The induction proof takes a least counterexample in a bounded ordinal.
For recursion, collect the unique earlier successor-domain graphs, glue them,
and append the next value. No pre-existing transfinite recursion operator is used.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open ZFSet
universe u

/-- A least counterexample below a fixed ordinal contradicts the induction step. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: Transfinite induction
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Suppose the hypothesis holds but $P$ fails at some ordinal $\alpha_0$. By
    §{sec:ordinals-successor-limit}, $\alpha_0+1$ is an ordinal, hence a set well-ordered by $\in$. Therefore
    $$\{\alpha\in\alpha_0+1:\neg P(\alpha)\}$$
    is a nonempty set of ordinals and has an $\in$-least element $\alpha^*$. By minimality, $P(\beta)$ holds for every
    $\beta < \alpha^*$, so the hypothesis forces $P(\alpha^*)$ — contradicting $\neg P(\alpha^*)$.
-/
theorem ordinal_induction_of_step (P : ZFSet.{u} → Prop)
    (step : ∀ a, a.IsOrdinal → (∀ b ∈ a, P b) → P a) :
    ∀ a, a.IsOrdinal → P a := by
  classical
  intro a ha
  by_contra hn
  let B := (insert a a).sep (fun b => ¬ P b)
  have haB : a ∈ B := mem_sep.mpr ⟨by simp, hn⟩
  have hB : B ≠ ∅ := by
    intro he
    exact notMem_empty a (he ▸ haB)
  obtain ⟨b, hbB, hmin⟩ := ZFSet.regularity B hB
  obtain ⟨hb, hnb⟩ := mem_sep.mp hbB
  have hs := isOrdinal_succ ha
  apply hnb
  apply step b (hs.mem hb)
  intro c hcb
  by_contra hnc
  have hcB : c ∈ B := mem_sep.mpr ⟨hs.mem_trans hcb hb, hnc⟩
  have hc : c ∈ B ∩ b := mem_inter.mpr ⟨hcB, hcb⟩
  exact notMem_empty c (hmin ▸ hc)

/-- Zero, successor, and limit cases follow from the least-counterexample induction. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    Splitting the inductive step into zero, successor, and nonzero limit cases gives the equivalent formulation above.
-/
theorem ordinal_induction_cases (P : Ordinal.{u} → Prop) (hzero : P 0)
    (hsucc : ∀ o, P o → P (Order.succ o))
    (hlimit : ∀ o, Order.IsSuccLimit o → (∀ b < o, P b) → P o) (o : Ordinal.{u}) : P o := by
  have h : ∀ a : ZFSet.{u}, a.IsOrdinal → P a.rank := by
    apply ordinal_induction_of_step
    intro a ha ih
    have earlier (b : Ordinal.{u}) (hb : b < a.rank) : P b := by
      have hba : b.toZFSet ∈ a :=
        (ZFSet.IsOrdinal.rank_lt_iff_mem (isOrdinal_toZFSet b) ha).mp (by simpa using hb)
      simpa using ih b.toZFSet hba
    rcases Ordinal.zero_or_succ_or_isSuccLimit a.rank with hz | ⟨b, hb⟩ | hl
    · simpa only [hz] using hzero
    · rw [← hb]
      exact hsucc b (earlier b (by rw [← hb]; exact Order.lt_succ b))
    · exact hlimit _ hl earlier
  simpa using h o.toZFSet (isOrdinal_toZFSet o)

/-- The union of the successors of all smaller ordinals is the given ordinal, including zero. -/
lemma ordinal_predecessor_successors {a : ZFSet.{u}} (ha : a.IsOrdinal) :
    ZFSet.iUnion (fun b : a => insert b.val b.val) = a := by
  apply ZFSet.ext
  intro z
  rw [mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    rcases mem_insert_iff.mp hb with rfl | hz
    · exact b.property
    · exact ha.mem_trans hz b.property
  · intro hz
    exact ⟨⟨z, hz⟩, by simp⟩

/-- The set-indexed union collects the compatible earlier successor-domain graphs. -/
theorem glue_ordinal_successor_solutions {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {a : ZFSet.{u}} (ha : a.IsOrdinal) (f : a → ZFSet.{u})
    (hf : ∀ b, IsRecursiveSolution H (insert b.val b.val) (f b)) :
    IsRecursiveSolution H a (ZFSet.iUnion f) := by
  have h := recursive_solution_iUnion (fun b : a => insert b.val b.val) f hf
  rwa [ordinal_predecessor_successors ha] at h

/-- Construct each successor-domain solution by gluing and then adjoining one new pair. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    \emph{Existence.} For each ordinal $\gamma$, construct a solution $f_\gamma$ on $\gamma+1$ by transfinite induction.
    Suppose the solutions $f_\beta$ have been constructed for $\beta<\gamma$.
    Agreement on common domains makes them compatible. Replacement collects these uniquely determined graphs into a set,
    so their union $g:=\bigcup_{\beta<\gamma}f_\beta$ is a function graph. Its domain is
    $$\bigcup_{\beta<\gamma}(\beta+1)=\gamma.$$
    Indeed, each smaller ordinal belongs to its own successor, and the successor of any smaller ordinal is contained in
    $\gamma$. For $\gamma=0$ this is the empty union, and $g=\emptyset$.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    The graph $g$ satisfies the recursion equation at every earlier input: a partial solution containing that input
    agrees with $g$ on its entire predecessor segment. Now set
    $$f_\gamma:=g\cup\{(\gamma,H(\gamma,g))\}.$$
    The new input is outside the domain of $g$, so this remains a function. Adding its value changes none of the earlier
    restrictions, and its restriction to $\gamma$ is exactly $g$. Thus every required equation holds.
-/
theorem ordinal_successor_solution_exists (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    ∀ a, a.IsOrdinal → ∃ f, IsRecursiveSolution H (insert a a) f := by
  classical
  apply ordinal_induction_of_step
  intro a ha ih
  choose f hf using fun b : a => ih b.val b.property
  have hg := glue_ordinal_successor_solutions ha f hf
  exact ⟨_, recursive_solution_extend hg (mem_irrefl a) (fun _ hz => hz)⟩

/-- Set-length recursion on every ordinal, with uniqueness inherited from overlap agreement. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: statement
  kind: theorem
  title: Transfinite recursion
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    The same union construction gives a solution on any ordinal domain, including a limit domain, proving the theorem.
-/
theorem ordinal_solution_exists_unique (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (a : ZFSet.{u}) (ha : a.IsOrdinal) : ∃! f, IsRecursiveSolution H a f := by
  classical
  choose f hf using fun b : a => ordinal_successor_solution_exists H b.val (ha.mem b.property)
  exact ⟨ZFSet.iUnion f, glue_ordinal_successor_solutions ha f hf,
    fun g hg => recursive_solution_unique hg (glue_ordinal_successor_solutions ha f hf)⟩

/-- A graph with domain D is unchanged by restriction to D. -/
lemma restrictGraph_domain {D Y f : ZFSet.{u}} (hf : ZFSet.IsFunc D Y f) :
    restrictGraph f D = f := by
  apply ZFSet.ext
  intro p
  rw [restrictGraph, mem_sep]
  exact ⟨And.left, fun h => ⟨h, (isFunc_doubleUnion hf).1 h⟩⟩

/-- The unique graph, selected at each set-length domain. -/
def ordinalSolution (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u})
    (ha : a.IsOrdinal) : ZFSet.{u} := (ordinal_solution_exists_unique H a ha).exists.choose

lemma ordinalSolution_spec (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u})
    (ha : a.IsOrdinal) : IsRecursiveSolution H a (ordinalSolution H a ha) :=
  (ordinal_solution_exists_unique H a ha).exists.choose_spec

/-- Solutions on different ordinal domains restrict to the same graph on a common initial segment. -/
theorem ordinalSolution_restrict (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {a b : ZFSet.{u}} (ha : a.IsOrdinal) (hb : b.IsOrdinal) (hab : a ⊆ b) :
    restrictGraph (ordinalSolution H b hb) a = ordinalSolution H a ha := by
  have hfa := ordinalSolution_spec H a ha
  have hfb := ordinalSolution_spec H b hb
  rw [← restrictGraph_domain hfa.function_graph]
  exact restrictGraph_eq_of_agree hfb.function_graph hfa.function_graph hab (fun _ hz => hz)
    (fun z hz v w hv hw => recursive_solutions_agree hfb hfa z (hab hz) hz v w hv hw)

/-- The all-ordinals assignment takes its value from the solution on the next ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Consequently, the assignment $F(\alpha):=f_\alpha(\alpha)$ defines a class function on all ordinals.
-/
def ordinalRecursion (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (a : {a : ZFSet.{u} // a.IsOrdinal}) : ZFSet.{u} :=
  ((ordinalSolution_spec H (insert a.val a.val) (isOrdinal_succ a.property)).function_graph.2
    a.val (by simp)).choose

lemma ordinalRecursion_mem (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (a : {a : ZFSet.{u} // a.IsOrdinal}) :
    pair a.val (ordinalRecursion H a) ∈ ordinalSolution H (insert a.val a.val) (isOrdinal_succ a.property) :=
  ((ordinalSolution_spec H (insert a.val a.val) (isOrdinal_succ a.property)).function_graph.2
    a.val (by simp)).choose_spec.1

/-- Every restriction of the class assignment is a set, namely the unique solution on its domain. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Agreement of the partial solutions shows that each $\restrict{F}{\gamma}$ is exactly the set-length solution on
    $\gamma$.
-/
theorem ordinalRecursion_graph (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (a : ZFSet.{u}) (ha : a.IsOrdinal) :
    functionGraph (fun b : a => ordinalRecursion H ⟨b.val, ha.mem b.property⟩) = ordinalSolution H a ha := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨b, rfl⟩ := mem_range.mp hp
    have hb : insert b.val b.val ⊆ a := by
      intro z hz
      rcases mem_insert_iff.mp hz with rfl | hz
      · exact b.property
      · exact ha.mem_trans hz b.property
    have h := ordinalRecursion_mem H ⟨b.val, ha.mem b.property⟩
    rw [← ordinalSolution_restrict H (isOrdinal_succ (ha.mem b.property)) ha hb] at h
    exact (pair_mem_restrictGraph.mp h).1
  · intro hp
    obtain ⟨b, hb, v, _, rfl⟩ := mem_prod.mp ((ordinalSolution_spec H a ha).function_graph.1 hp)
    let bO : {a : ZFSet.{u} // a.IsOrdinal} := ⟨b, ha.mem hb⟩
    have he := recursive_solutions_agree (ordinalSolution_spec H a ha)
      (ordinalSolution_spec H (insert b b) (isOrdinal_succ bO.property))
      b hb (by simp) v (ordinalRecursion H bO) hp (ordinalRecursion_mem H bO)
    exact mem_range.mpr ⟨⟨b, hb⟩, by simp only [he, bO]⟩

/-- The class assignment obeys the original recursion rule on its actual set-coded initial segment. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    In particular,
    $$F(\alpha)=H(\alpha,\restrict{F}{\alpha}).$$
-/
theorem ordinalRecursion_eq (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (a : {a : ZFSet.{u} // a.IsOrdinal}) :
    ordinalRecursion H a = H a.val
      (functionGraph (fun b : a.val => ordinalRecursion H ⟨b.val, a.property.mem b.property⟩)) := by
  rw [ordinalRecursion_graph]
  have h := ordinalSolution_spec H (insert a.val a.val) (isOrdinal_succ a.property)
  have he := (h.function_graph.2 a.val (by simp)).unique (ordinalRecursion_mem H a) (h.equation a.val (by simp))
  rwa [ordinalSolution_restrict H a.property (isOrdinal_succ a.property)
    (fun _ hz => mem_insert_iff.mpr (Or.inr hz))] at he

/-- Any other class assignment obeying the rule agrees at every ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    Any other class function satisfying this equation agrees with $F$ by the same transfinite-induction argument.
-/
theorem ordinalRecursion_unique (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (F : {a : ZFSet.{u} // a.IsOrdinal} → ZFSet.{u})
    (hF : ∀ a, F a = H a.val (functionGraph (fun b : a.val => F ⟨b.val, a.property.mem b.property⟩))) :
    F = ordinalRecursion H := by
  have h : ∀ a : ZFSet.{u}, a.IsOrdinal → ∀ ha : a.IsOrdinal,
      F ⟨a, ha⟩ = ordinalRecursion H ⟨a, ha⟩ := by
    apply ordinal_induction_of_step
    intro a _ ih ha
    rw [hF, ordinalRecursion_eq]
    apply congrArg (H a)
    apply congrArg functionGraph
    funext b
    exact ih b.val b.property (ha.mem b.property)
  funext a
  exact h a.val a.property a.property

end PolishSpaceBook.SetTheoryModels
