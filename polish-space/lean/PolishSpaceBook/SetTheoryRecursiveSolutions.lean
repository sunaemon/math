module

public import PolishSpaceBook.SetTheoryGraphRestrictions

@[expose] public section

/-! # Agreement and gluing of partial solutions to membership recursion

A partial solution has a transitive domain and satisfies the recursive equation
at each input. The compatibility proof uses membership induction. Gluing is a
set-indexed union, not a union over a proper class of partial solutions.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- A set-coded solution on a domain closed under membership predecessors. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: definition
  title: Partial solutions of membership recursion
-/
structure IsRecursiveSolution (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (D f : ZFSet.{u}) : Prop where
  domain_transitive : D.IsTransitive
  function_graph : ZFSet.IsFunc D (ZFSet.sUnion (ZFSet.sUnion f)) f
  equation : ∀ a ∈ D, ZFSet.pair a (H a (restrictGraph f a)) ∈ f

/-- Partial solutions agree at every common input, by induction over its members. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Let $f:D\to V$ and $g:E\to V$ be partial solutions. By membership induction on $a$, assume they agree at
    every $z\in a$ belonging to both domains. If $a\in D\cap E$, transitivity puts all its members in both domains.
    Thus $\restrict{f}{a}=\restrict{g}{a}$, and
    $$f(a)=H(a,\restrict{f}{a})=H(a,\restrict{g}{a})=g(a).$$
    This proves agreement. If the domains coincide, every pair in either graph occurs in the other, so the graphs
    are equal.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Agreement and gluing of recursive solutions
-/
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
    \begin{proof}[Proof]
    \emph{Uniqueness.} Two solutions $f,f'$ agree on their common domain by transfinite induction on $\alpha$.
    If they agree below $\alpha$, then $\restrict{f}{\alpha}=\restrict{f'}{\alpha}$, so the same rule gives
    $$f(\alpha)=H(\alpha,\restrict{f}{\alpha})=H(\alpha,\restrict{f'}{\alpha})=f'(\alpha).$$
-/
theorem recursive_solutions_agree {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {D E f g : ZFSet.{u}} (hf : IsRecursiveSolution H D f) (hg : IsRecursiveSolution H E g) :
    ∀ a ∈ D, a ∈ E → ∀ b c, ZFSet.pair a b ∈ f → ZFSet.pair a c ∈ g → b = c := by
  intro a
  induction a using ZFSet.inductionOn with
  | h a ih =>
    intro haD haE b c hb hc
    have he : restrictGraph f a = restrictGraph g a :=
      restrictGraph_eq_of_agree hf.function_graph hg.function_graph
        (hf.domain_transitive.subset_of_mem haD) (hg.domain_transitive.subset_of_mem haE)
        (fun z hz v w hv hw => ih z hz
          (hf.domain_transitive.mem_trans hz haD) (hg.domain_transitive.mem_trans hz haE) v w hv hw)
    have hbH : b = H a (restrictGraph f a) := (hf.function_graph.2 a haD).unique hb (hf.equation a haD)
    have hcH : c = H a (restrictGraph g a) := (hg.function_graph.2 a haE).unique hc (hg.equation a haE)
    rw [hbH, hcH, he]

/-- In particular, a solution on a fixed domain is unique. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Agreement and gluing of recursive solutions
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    In particular, there is at most one solution on any fixed ordinal domain.
-/
theorem recursive_solution_unique {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {D f g : ZFSet.{u}} (hf : IsRecursiveSolution H D f) (hg : IsRecursiveSolution H D g) : f = g := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.function_graph.1 hp)
    obtain ⟨c, hc, _⟩ := hg.function_graph.2 a ha
    exact (recursive_solutions_agree hf hg a ha ha b c hp hc) ▸ hc
  · intro hp
    obtain ⟨a, ha, c, _, rfl⟩ := ZFSet.mem_prod.mp (hg.function_graph.1 hp)
    obtain ⟨b, hb, _⟩ := hf.function_graph.2 a ha
    exact (recursive_solutions_agree hf hg a ha ha b c hb hp) ▸ hb

/-- A set-indexed family of partial solutions glues to a solution on the union of the domains. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For the gluing assertion, $A$ is transitive because each $D_i$ is transitive. Pairwise agreement makes $F$
    a function with domain $A$: every input occurs in some graph, and two graphs cannot give it different values.
    For $a\in A$, choose $i\in I$ with $a\in D_i$. Every $z\in a$ lies in $D_i$, and agreement gives
    $\restrict{F}{a}=\restrict{f_i}{a}$. Hence
    $$F(a)=f_i(a)=H(a,\restrict{f_i}{a})=H(a,\restrict{F}{a}),$$
    as required. This includes an empty family, whose union is the empty solution.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Agreement and gluing of recursive solutions
-/
theorem recursive_solution_iUnion {ι : Type*} [Small.{u} ι]
    {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} (D f : ι → ZFSet.{u})
    (hs : ∀ i, IsRecursiveSolution H (D i) (f i)) :
    IsRecursiveSolution H (ZFSet.iUnion D) (ZFSet.iUnion f) := by
  let A := ZFSet.iUnion D
  let U := ZFSet.iUnion f
  have hA : A.IsTransitive := ZFSet.IsTransitive.iUnion (fun i => (hs i).domain_transitive)
  have hfunc : ZFSet.IsFunc A (ZFSet.sUnion (ZFSet.sUnion U)) U := by
    constructor
    · intro p hp
      obtain ⟨i, hpi⟩ := ZFSet.mem_iUnion.mp hp
      obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp ((hs i).function_graph.1 hpi)
      exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_iUnion.mpr ⟨i, ha⟩, second_mem_doubleUnion hp⟩
    · intro a ha
      obtain ⟨i, hai⟩ := ZFSet.mem_iUnion.mp ha
      obtain ⟨b, hb, _⟩ := (hs i).function_graph.2 a hai
      refine ⟨b, ZFSet.mem_iUnion.mpr ⟨i, hb⟩, ?_⟩
      intro c hc
      obtain ⟨j, hcj⟩ := ZFSet.mem_iUnion.mp hc
      have haj := (ZFSet.pair_mem_prod.mp ((hs j).function_graph.1 hcj)).1
      exact recursive_solutions_agree (hs j) (hs i) a haj hai c b hcj hb
  refine ⟨hA, hfunc, ?_⟩
  intro a ha
  obtain ⟨i, hai⟩ := ZFSet.mem_iUnion.mp ha
  have he : restrictGraph U a = restrictGraph (f i) a := by
    apply restrictGraph_eq_of_agree hfunc (hs i).function_graph
      (hA.subset_of_mem ha) ((hs i).domain_transitive.subset_of_mem hai)
    intro z hz b c hb hc
    obtain ⟨j, hbj⟩ := ZFSet.mem_iUnion.mp hb
    have hzj := (ZFSet.pair_mem_prod.mp ((hs j).function_graph.1 hbj)).1
    exact recursive_solutions_agree (hs j) (hs i) z hzj
      ((hs i).domain_transitive.mem_trans hz hai) b c hbj hc
  change ZFSet.pair a (H a (restrictGraph U a)) ∈ U
  rw [he]
  exact ZFSet.mem_iUnion.mpr ⟨i, (hs i).equation a hai⟩

/-- Once the two families have been collected internally, Union performs the gluing in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For gluing inside a transitive model $M$, the two collections $\{D_i:i\in I\}$ and $\{f_i:i\in I\}$
    must first belong to $M$. Union then puts $A,F$ in $M$, and the gluing lemma applies to their actual graphs.
-/
theorem recursive_solution_iUnion_mem {ι : Type*} [Small.{u} ι]
    {M : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence)
    {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} (D f : ι → ZFSet.{u})
    (hs : ∀ i, IsRecursiveSolution H (D i) (f i))
    (hD : ZFSet.range D ∈ M) (hf : ZFSet.range f ∈ M) :
    ZFSet.iUnion D ∈ M ∧ ZFSet.iUnion f ∈ M ∧
      IsRecursiveSolution H (ZFSet.iUnion D) (ZFSet.iUnion f) :=
  ⟨union_mem hM hunion hD, union_mem hM hunion hf, recursive_solution_iUnion D f hs⟩

/-- Extend a partial solution by one input whose membership predecessors are already in its domain. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The set $D'$ is transitive, since every member of the new input already belongs to $D$.
    The new pair has a first coordinate outside $D$, so $f'$ remains a function.
    If $z\in D$, then $a\notin z$: otherwise transitivity would give $a\in D$.
    Also $a\notin a$ by Foundation. Thus adding the new pair changes none of the restrictions to the members of
    an old or new input. All old recursive equations remain true, and the equation at $a$ holds by the definition
    of $v$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: One-point extension of a recursive solution
-/
theorem recursive_solution_extend {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {D f a : ZFSet.{u}} (hf : IsRecursiveSolution H D f) (ha : a ∉ D) (hsub : a ⊆ D) :
    IsRecursiveSolution H (insert a D) (insert (ZFSet.pair a (H a (restrictGraph f a))) f) := by
  let v := H a (restrictGraph f a)
  let g := insert (ZFSet.pair a v) f
  have hmem (z b : ZFSet.{u}) : ZFSet.pair z b ∈ g ↔ (z = a ∧ b = v) ∨ ZFSet.pair z b ∈ f := by
    simp only [g, ZFSet.mem_insert_iff, ZFSet.pair_inj]
  have hD : (insert a D).IsTransitive := by
    intro z hz w hw
    rcases ZFSet.mem_insert_iff.mp hz with he | hzD
    · subst z
      exact ZFSet.mem_insert_iff.mpr (Or.inr (hsub hw))
    · exact ZFSet.mem_insert_iff.mpr (Or.inr (hf.domain_transitive.mem_trans hw hzD))
  have hg : ZFSet.IsFunc (insert a D) (ZFSet.sUnion (ZFSet.sUnion g)) g := by
    constructor
    · intro p hp
      rcases ZFSet.mem_insert_iff.mp hp with he | hpf
      · subst p
        exact ZFSet.pair_mem_prod.mpr ⟨by simp, second_mem_doubleUnion hp⟩
      · obtain ⟨z, hz, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.function_graph.1 hpf)
        exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_insert_iff.mpr (Or.inr hz), second_mem_doubleUnion hp⟩
    · intro z hz
      by_cases hza : z = a
      · subst z
        refine ⟨v, (hmem a v).mpr (Or.inl ⟨rfl, rfl⟩), ?_⟩
        intro b hb
        rcases (hmem a b).mp hb with he | hbf
        · exact he.2
        · exact False.elim (ha (ZFSet.pair_mem_prod.mp (hf.function_graph.1 hbf)).1)
      · have hzD : z ∈ D := (ZFSet.mem_insert_iff.mp hz).resolve_left hza
        obtain ⟨b, hb, huniq⟩ := hf.function_graph.2 z hzD
        refine ⟨b, (hmem z b).mpr (Or.inr hb), ?_⟩
        intro c hc
        rcases (hmem z c).mp hc with he | hcf
        · exact False.elim (hza he.1)
        · exact huniq c hcf
  refine ⟨hD, hg, ?_⟩
  intro z hz
  rcases ZFSet.mem_insert_iff.mp hz with he | hzD
  · subst z
    have heq : restrictGraph g a = restrictGraph f a := restrictGraph_insert_of_notMem (ZFSet.mem_irrefl a)
    change ZFSet.pair a (H a (restrictGraph g a)) ∈ g
    rw [heq]
    exact (hmem a v).mpr (Or.inl ⟨rfl, rfl⟩)
  · have han : a ∉ z := fun haz => ha (hf.domain_transitive.mem_trans haz hzD)
    have heq : restrictGraph g z = restrictGraph f z := restrictGraph_insert_of_notMem han
    change ZFSet.pair z (H z (restrictGraph g z)) ∈ g
    rw [heq]
    exact (hmem z _).mpr (Or.inr (hf.equation z hzD))

/-- The one-point extension stays in a model when the step rule's value belongs to it. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For the one-point extension, if $D,f,a,v\in M$, Pairing and Union put $D',f'$ in $M$.
-/
theorem recursive_solution_extend_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} {D f a : ZFSet.{u}}
    (hf : IsRecursiveSolution H D f) (ha : a ∉ D) (hsub : a ⊆ D)
    (hD : D ∈ M) (hF : f ∈ M) (hA : a ∈ M) (hV : H a (restrictGraph f a) ∈ M) :
    insert a D ∈ M ∧ insert (ZFSet.pair a (H a (restrictGraph f a))) f ∈ M ∧
      IsRecursiveSolution H (insert a D) (insert (ZFSet.pair a (H a (restrictGraph f a))) f) := by
  have hi {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : insert x y ∈ M := by
    rw [ZFSet.insert_eq]
    exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair hx) hy
  exact ⟨hi hA hD, hi (orderedPair_mem hM hpair hA hV) hF, recursive_solution_extend hf ha hsub⟩

end PolishSpaceBook.SetTheoryModels
