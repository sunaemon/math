module

public import PolishSpaceBook.LambdaWeihrauchChoice
public import PolishSpaceBook.LambdaFunctionSpaces
public import PolishSpaceBook.RepresentedBaireSpace
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaFunction

namespace MultiProblem

/-- Lift a represented problem using all valid names of each permissible answer. -/
def onNames {X Y : Type*} (F : MultiProblem X Y) (δX : Representation X)
    (δY : Representation Y) : NameProblem := fun p =>
  {q | ∃ hp : p ∈ δX.domain, ∃ hq : q ∈ δY.domain,
    δY.toFun ⟨q, hq⟩ ∈ F (δX.toFun ⟨p, hp⟩)}

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    A \termdefineas{Weihrauch problem}{problem} from $\mathbf X$ to $\mathbf Y$ is specified by a domain
    $\DomainOf{F}\IncludedIn X$ and a nonempty set $F(x)\IncludedIn Y$ of admissible solutions for every
    $x\in\DomainOf{F}$.
-/
theorem onNames_domain_iff {X Y : Type*} (F : MultiProblem X Y)
    (δX : Representation X) (δY : Representation Y) (p : baire_space) :
    (F.onNames δX δY p).Nonempty ↔
      ∃ hp : p ∈ δX.domain, (F (δX.toFun ⟨p, hp⟩)).Nonempty := by
  constructor
  · rintro ⟨q, hp, hq, hy⟩
    exact ⟨hp, δY.toFun ⟨q, hq⟩, hy⟩
  · rintro ⟨hp, y, hy⟩
    obtain ⟨q, hq⟩ := δY.surjective y
    exact ⟨q.val, hp, q.property, hq ▸ hy⟩

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    A
    \termdefineas{Weihrauch realizer}{realizer} of $F$ is a partial function
    $$\PartialFunctionMap{\Phi}{\BaireSpace}{\BaireSpace}$$
    such that, whenever $p$ names $x\in \DomainOf{F}$, the output $\Phi(p)$ names some element of $F(x)$.
-/
theorem isRealizer_onNames_iff {X Y : Type*} (F : MultiProblem X Y)
    (δX : Representation X) (δY : Representation Y) (Φ : PartialNameMap) :
    (F.onNames δX δY).IsRealizer Φ ↔
      ∀ p : δX.domain, (F (δX.toFun p)).Nonempty →
        ∃ q : δY.domain, Φ p.val = some q.val ∧ δY.toFun q ∈ F (δX.toFun p) := by
  constructor
  · intro h p hp
    obtain ⟨q, hΦ, _, hq, hy⟩ := h p.val ((F.onNames_domain_iff δX δY _).mpr ⟨p.property, hp⟩)
    exact ⟨⟨q, hq⟩, hΦ, hy⟩
  · intro h p hp
    obtain ⟨hp, hx⟩ := (F.onNames_domain_iff δX δY p).mp hp
    obtain ⟨q, hΦ, hy⟩ := h ⟨p, hp⟩ hx
    exact ⟨q.val, hΦ, hp, q.property, hy⟩

end MultiProblem

namespace PartialNameMap

def nameDomain (F : PartialNameMap) : Set baire_space := {p | (F p).isSome}

def nameValue (F : PartialNameMap) (p : F.nameDomain) : baire_space :=
  (F p.val).get p.property

end PartialNameMap

/-- The partial-operator predicate is exactly the book's domain-relative Type-Two notion. -/
theorem lambdaComputable_partial_iff (F : PartialNameMap) :
    WeihrauchChoice.LambdaComputable F ↔ TypeTwoComputable F.nameValue := by
  constructor
  · rintro ⟨P, hP, h⟩
    exact ⟨P, hP, fun p n m => h p.val (F.nameValue p) (Option.some_get p.property).symm n m⟩
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, fun p q hp n m => ?_⟩
    have hd : p ∈ F.nameDomain := by simp [PartialNameMap.nameDomain, hp]
    have hv : F.nameValue ⟨p, hd⟩ = q := by
      apply Option.some.inj
      exact (Option.some_get hd).trans hp
    simpa only [hv] using h ⟨p, hd⟩ n m

namespace LambdaWeihrauch

/-- Ordinary reduction with actual closed lambda operators and the fixed computable pairing. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    For problems $F$ from $\mathbf X$ to $\mathbf Y$ and $G$ from $\mathbf U$ to $\mathbf V$, write
    $$F\WeihrauchReducesTo G$$
    if there are computable partial operators
    $$
    \PartialFunctionMap{K}{\BaireSpace}{\BaireSpace}
    \qquad\text{and}\qquad
    \PartialFunctionMap{H}{\BaireSpace}{\BaireSpace}
    $$
    such that, for every realizer $\Gamma$ of $G$, the map
    $$p\longmapsto H\bigl(\langle p,\Gamma(K(p))\rangle\bigr)$$
    is a realizer of $F$. The operator $K$ preprocesses an instance of $F$ into an instance of $G$; a single call to a
    solver for $G$ supplies one solution; the pairing code lets the unary operator $H$ postprocess the original input
    together with that solution into a solution of the original problem.
-/
def Reduces (F G : NameProblem) : Prop :=
  WeihrauchReduces WeihrauchChoice.LambdaComputable typeTwoPairName F G

/-- Strong reduction gives the postprocessor only the returned answer name. -/
def StrongReduces (F G : NameProblem) : Prop :=
  StrongWeihrauchReduces WeihrauchChoice.LambdaComputable F G

/-- Weihrauch reduction for the represented point problems, not unrelated name problems. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    For problems $F$ from $\mathbf X$ to $\mathbf Y$ and $G$ from $\mathbf U$ to $\mathbf V$, write
    $$F\WeihrauchReducesTo G$$
    if there are computable partial operators
    $$
    \PartialFunctionMap{K}{\BaireSpace}{\BaireSpace}
    \qquad\text{and}\qquad
    \PartialFunctionMap{H}{\BaireSpace}{\BaireSpace}
    $$
    such that, for every realizer $\Gamma$ of $G$, the map
    $$p\longmapsto H\bigl(\langle p,\Gamma(K(p))\rangle\bigr)$$
    is a realizer of $F$. The operator $K$ preprocesses an instance of $F$ into an instance of $G$; a single call to a
    solver for $G$ supplies one solution; the pairing code lets the unary operator $H$ postprocess the original input
    together with that solution into a solution of the original problem.
-/
def OnRepresentations {X Y U V : Type*} (δX : Representation X) (δY : Representation Y)
    (δU : Representation U) (δV : Representation V) (F : MultiProblem X Y)
    (G : MultiProblem U V) : Prop := Reduces (F.onNames δX δY) (G.onNames δU δV)

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    There is also a strong version $F\StrongWeihrauchReducesTo G$ in which the postprocessor may not reuse the
    original input after
    the call to $G$: its output has the form $H(\Gamma(K(p)))$. Strong reducibility is useful when one wants the oracle call
    to contain all information passed from the instance to the solution. The ordinary version $\WeihrauchReducesTo$ is more
    flexible and is the default comparison in the Weihrauch lattice [@BrattkaGherardiPauly2021].
-/
def StrongOnRepresentations {X Y U V : Type*} (δX : Representation X) (δY : Representation Y)
    (δU : Representation U) (δV : Representation V) (F : MultiProblem X Y)
    (G : MultiProblem U V) : Prop := StrongReduces (F.onNames δX δY) (G.onNames δU δV)

/-- Ignore the original input by projecting the paired name onto its answer component. -/
def answerOnly (H : PartialNameMap) : PartialNameMap := fun p => H (typeTwoRightName p)

theorem answerOnly_computable {H : PartialNameMap} (hH : WeihrauchChoice.LambdaComputable H) :
    WeihrauchChoice.LambdaComputable (answerOnly H) := by
  obtain ⟨P, hP, h⟩ := hH
  have hR := rightProgram_computes Set.univ
  refine ⟨compositionProgram P rightProgram, compositionProgram_closed hP hR.1, ?_⟩
  intro p q hp n m
  have hr : OracleRuns p (compositionProgram P rightProgram) n (q n) :=
    compositionProgram_runs hP hR.1 ((h _ q hp n (q n)).mpr rfl)
      (fun k => (typeTwoComputes_iff_runs.mp hR).2 ⟨p, mem_univ _⟩ k)
  exact ⟨fun hm => hr.output_unique hm, fun he => he ▸ hr⟩

/-- Every strong reduction is ordinary, with a concrete lambda postprocessor. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    There is also a strong version $F\StrongWeihrauchReducesTo G$ in which the postprocessor may not reuse the
    original input after
    the call to $G$: its output has the form $H(\Gamma(K(p)))$. Strong reducibility is useful when one wants the oracle call
    to contain all information passed from the instance to the solution. The ordinary version $\WeihrauchReducesTo$ is more
    flexible and is the default comparison in the Weihrauch lattice [@BrattkaGherardiPauly2021].
-/
theorem StrongReduces.reduces {F G : NameProblem} (h : StrongReduces F G) : Reduces F G := by
  obtain ⟨K, H, hK, hH, hr⟩ := h
  refine ⟨K, answerOnly H, hK, answerOnly_computable hH, ?_⟩
  intro Γ hΓ
  have he : ordinaryWeihrauchPostprocess typeTwoPairName K (answerOnly H) Γ =
      strongWeihrauchPostprocess K H Γ := by
    funext p
    cases hk : K p with
    | none => simp [ordinaryWeihrauchPostprocess, strongWeihrauchPostprocess, hk]
    | some k =>
      cases hg : Γ k with
      | none => simp [ordinaryWeihrauchPostprocess, strongWeihrauchPostprocess, hk, hg]
      | some q => simp [ordinaryWeihrauchPostprocess, strongWeihrauchPostprocess, hk, hg, answerOnly]
  rw [he]
  exact hr Γ hΓ

end LambdaWeihrauch
namespace WeihrauchChoice

/-- Every closed subset has a negative name; no computable selection of such
names from arbitrary sets is asserted. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Name a natural number by the first coordinate of a Baire name: $\delta_{\NN}(q):=q(0)$. A
    \termdefineas{negative name of a subset of the natural numbers}{negative name} $a\in\BaireSpace$ describes the set
    $$\NaturalChoiceSet{a}:=\{m\in\NN:\forall s\in\NN,\ a(s)\ne m+1\}.$$
    An entry $m+1$ excludes $m$, while entry $0$ excludes nothing. Repetitions and empty stages are allowed.
    Every subset of discrete $\NN$ is closed, so this is a negative representation of closed subsets.
-/
theorem allowedNaturals_surjective : Function.Surjective allowedNaturals := by
  classical
  intro A
  refine ⟨fun s => if s ∈ A then 0 else s + 1, ?_⟩
  ext m
  change (∀ s, (if s ∈ A then 0 else s + 1) ≠ m + 1) ↔ m ∈ A
  constructor
  · intro hm
    by_contra h
    exact hm m (by simp [h])
  · intro hm s
    by_cases hs : s ∈ A
    · simp [hs]
    · simp only [hs, ite_false, ne_eq, Nat.add_right_cancel_iff]
      intro he
      exact hs (he ▸ hm)

/-- The same zeroth-coordinate natural-number representation used by both tasks. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Name a natural number by the first coordinate of a Baire name: $\delta_{\NN}(q):=q(0)$. A
    \termdefineas{negative name of a subset of the natural numbers}{negative name} $a\in\BaireSpace$ describes the set
    $$\NaturalChoiceSet{a}:=\{m\in\NN:\forall s\in\NN,\ a(s)\ne m+1\}.$$
    An entry $m+1$ excludes $m$, while entry $0$ excludes nothing. Repetitions and empty stages are allowed.
    Every subset of discrete $\NN$ is closed, so this is a negative representation of closed subsets.
-/
def naturalRepresentation : Representation ℕ where
  domain := univ
  toFun p := p.val 0
  surjective m := ⟨⟨fun _ => m, mem_univ _⟩, rfl⟩

/-- Negative names represent actual mathlib closed subsets of discrete naturals. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    Name a natural number by the first coordinate of a Baire name: $\delta_{\NN}(q):=q(0)$. A
    \termdefineas{negative name of a subset of the natural numbers}{negative name} $a\in\BaireSpace$ describes the set
    $$\NaturalChoiceSet{a}:=\{m\in\NN:\forall s\in\NN,\ a(s)\ne m+1\}.$$
    An entry $m+1$ excludes $m$, while entry $0$ excludes nothing. Repetitions and empty stages are allowed.
    Every subset of discrete $\NN$ is closed, so this is a negative representation of closed subsets.
-/
def negativeRepresentation : Representation (TopologicalSpace.Closeds ℕ) where
  domain := univ
  toFun p := ⟨allowedNaturals p.val, allowedNaturals_closed p.val⟩
  surjective A := by
    obtain ⟨a, ha⟩ := allowedNaturals_surjective (A : Set ℕ)
    exact ⟨⟨a, mem_univ _⟩, TopologicalSpace.Closeds.ext ha⟩

def naturalChoiceProblem : MultiProblem (TopologicalSpace.Closeds ℕ) ℕ :=
  fun A => (A : Set ℕ)

def lpoValues : MultiProblem baire_space ℕ := fun p =>
  {m | (m = 0 ∧ ∀ k, p k = 0) ∨ (m = 1 ∧ ∃ k, p k ≠ 0)}

/-- The representation lift is literally the name problem used by the lambda reduction. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The output natural number uses $\delta_{\NN}$. The problem
    \termdefine{closed choice on the natural numbers}, denoted by $\ClosedChoiceNaturals$, takes a negative name $a$
    with $\NaturalChoiceSet{a}\ne\emptyset$ and permits any output in $\NaturalChoiceSet{a}$, again named by
    $\delta_{\NN}$.
-/
theorem closedChoice_onNames :
    naturalChoiceProblem.onNames negativeRepresentation naturalRepresentation = closedChoice := by
  funext a
  ext q
  change (∃ _ : a ∈ (univ : Set baire_space), ∃ _ : q ∈ (univ : Set baire_space),
    q 0 ∈ allowedNaturals a) ↔ q 0 ∈ allowedNaturals a
  simp

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The \termdefine{limited principle of omniscience problem} $\LimitedOmniscienceProblem$ asks whether an input name
    has a nonzero coordinate:
    $$\LimitedOmniscienceProblem(p)=
    \begin{cases}
    0,&\forall k\in\NN,\ p(k)=0,\\
    1,&\exists k\in\NN,\ p(k)\ne0.
    \end{cases}$$
-/
theorem lpo_onNames : lpoValues.onNames baireIdentityRepresentation naturalRepresentation = lpo := by
  funext p
  ext q
  change (∃ _ : p ∈ (univ : Set baire_space), ∃ _ : q ∈ (univ : Set baire_space),
    (q 0 = 0 ∧ ∀ k, p k = 0) ∨ (q 0 = 1 ∧ ∃ k, p k ≠ 0)) ↔
      (q 0 = 0 ∧ ∀ k, p k = 0) ∨ (q 0 = 1 ∧ ∃ k, p k ≠ 0)
  simp

/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: statement
  kind: theorem
  title: A concrete strong Weihrauch reduction
-/
theorem lpo_represented_strong :
    LambdaWeihrauch.StrongOnRepresentations baireIdentityRepresentation naturalRepresentation
      negativeRepresentation naturalRepresentation lpoValues naturalChoiceProblem := by
  change LambdaWeihrauch.StrongReduces
    (lpoValues.onNames baireIdentityRepresentation naturalRepresentation)
    (naturalChoiceProblem.onNames negativeRepresentation naturalRepresentation)
  rw [lpo_onNames, closedChoice_onNames]
  exact lpo_strongly_reduces_to_closedChoice

theorem lpo_represented_ordinary :
    LambdaWeihrauch.OnRepresentations baireIdentityRepresentation naturalRepresentation
      negativeRepresentation naturalRepresentation lpoValues naturalChoiceProblem :=
  LambdaWeihrauch.StrongReduces.reduces lpo_represented_strong

/-- A negative name is not already a selected natural number under the output representation. -/
/-@ booklink:
  source: polish-space-book/weihrauch-reducibility.md
  target: prose
  excerpt: |
    The preprocessor can enumerate an exclusion once a finite query justifies it. It does not choose a member of
    $\NaturalChoiceSet{K(p)}$. That choice is precisely what the oracle supplies. The postprocessor then reads the
    answer
    without using the original input, illustrating the additional restriction in a strong reduction.
-/
theorem preprocessor_not_choice_selector :
    ∃ p : baire_space, preprocess p 0 ∉ allowedNaturals (preprocess p) := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have hb := h (Nat.pair 0 1)
  norm_num [preprocess, Nat.unpair_pair] at hb

end WeihrauchChoice

end PolishSpaceBook
