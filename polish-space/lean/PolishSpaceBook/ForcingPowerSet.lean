module

public import PolishSpaceBook.ForcingSeparationClosure

@[expose] public section

/-! # Bounded subset names and preservation of Power Set -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- The internal subsets of B which are forcing names. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\tau\in M^P$, the proof in §{sec:generic-power-set} constructs the ground-model sets
    $$\begin{aligned}
    B_\tau&:=\bigl(\bigcup\bigcup\tau\bigr)\times P,\\
    C_\tau&:=\{\theta\in\InternalPowerSet{M}{B_\tau}:\theta\in M^P\},\\
    \Pi_\tau&:=C_\tau\times P.
    \end{aligned}$$
    Every subset of $\tau^G$ belonging to the extension has a name in $C_\tau$.
    Let $\psi(a,z)$ be the bounded formula $z\IncludedIn a$, and define
    $$\ForcingPowerSetName{\tau}:=\ForcingSeparationName{\Pi_\tau}{\psi}{\tau}.$$
    For $A,B\in M$, let $\chi(A,B,g)$ be the bounded formula saying that $g$ is a function graph
    from $A$ to $B$, and define
    $$\begin{aligned}
    \rho_{A,B}&:=\ForcingPowerSetName{\check{(A\times B)}},\\
    \ForcingFunctionSpaceName{A}{B}&:=
    \ForcingSeparationName{\rho_{A,B}}{\chi}{(\check A,\check B)}.
    \end{aligned}$$
-/
def boundedNames (P M B : ZFSet.{u}) : ZFSet.{u} :=
  (internalPowerSet M B).sep (IsName P)

lemma mem_boundedNames (P M B σ : ZFSet.{u}) :
    σ ∈ boundedNames P M B ↔ σ ∈ M ∧ σ ⊆ B ∧ IsName P σ := by
  simp only [boundedNames, internalPowerSet, ZFSet.mem_sep, and_assoc]

/-- All conditions label every bounded name; no greatest condition is needed. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Define
    $$\Pi:=C\times P\in M.$$
-/
def boundedNamesName (P M B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (boundedNames P M B) P

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Each first coordinate is a name and each second coordinate is a condition, so $\Pi\in M^P$.
-/
lemma boundedNamesName_isName (P M B : ZFSet.{u}) : IsName P (boundedNamesName P M B) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, p, _, he⟩ := ZFSet.mem_prod.mp hz
    exact ⟨σ, p, he⟩
  · intro σ p hp
    obtain ⟨hσ, hp⟩ := ZFSet.pair_mem_prod.mp hp
    exact ⟨hp, ((mem_boundedNames P M B σ).mp hσ).2.2⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For the nonempty filter $G$, its value is exactly
    $$\Pi^G=\{\theta^G:\theta\in C\}.$$
    Indeed, every member of the value has such a first coordinate; conversely, for any $\theta\in C$, choose
    $p\in G$ and use $\langle\theta,p\rangle\in\Pi$.
-/
lemma mem_value_boundedNamesName (P M B : ZFSet.{u}) [Preorder (Condition P)]
    (G : Order.PFilter (Condition P)) (x : ZFSet.{u}) :
    x ∈ value P G (boundedNamesName P M B) ↔
      ∃ σ : Name P M, σ.val ⊆ B ∧ value P G σ.val = x := by
  rw [mem_value]
  constructor
  · rintro ⟨σ, p, _, hp, he⟩
    have hσ := (mem_boundedNames P M B σ).mp (ZFSet.pair_mem_prod.mp hp).1
    exact ⟨⟨σ, hσ.1, hσ.2.2⟩, hσ.2.1, he⟩
  · rintro ⟨σ, hsub, he⟩
    obtain ⟨p, hp⟩ := G.nonempty
    exact ⟨σ.val, p, hp, ZFSet.pair_mem_prod.mpr
      ⟨(mem_boundedNames P M B σ.val).mpr ⟨σ.property.1, hsub, σ.property.2⟩, p.property⟩, he⟩

/-- An internal subset formula, interpreted as actual inclusion in a transitive model. -/
def subsetFormula : ForcingFormulas.Formula 2 :=
  boundedAll (1 : Fin 2) (memberAt (2 : Fin 3) 0)

lemma realize_subsetFormula {S : ZFSet.{u}} (hS : S.IsTransitive) (x z : S) :
    subsetFormula.Realize Empty.elim (Fin.snoc ![x] z) ↔ z.val ⊆ x.val := by
  rw [subset_iff_internal hS z.property]
  simp [subsetFormula, realize_boundedAll_model]

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

include hM hinf hpair hunion hpower hsep hrep

omit [Preorder (Condition P.val)] in
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Now form the internal power set $\InternalPowerSet{M}{B}\in M$ and separate its name members:
    $$C:=\{\theta\in\InternalPowerSet{M}{B}:M\models\eta(P,\theta)\}.$$
    The defining-formula theorem identifies this predicate with being an actual $P$-name.
    Separation in $M$ therefore gives $C\in M$, with
    $$\theta\in C\quad\Longleftrightarrow\quad
     \theta\in M^P\ \land\ \theta\IncludedIn B.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The bound in the Separation construction does not depend on the selecting formula or its parameters.
    This gives a set of names large enough to represent every subset of a fixed extension set.
    The name predicate from §{sec:internal-forcing-formulas} lets us form this supply inside the ground model.
-/
lemma boundedNames_mem {B : ZFSet.{u}} (hB : B ∈ M) : boundedNames P.val M B ∈ M := by
  apply separation_mem_of_absolute hM nameFormula (hsep _) ![P] (internalPowerSet_mem hM hpower hB)
  intro z _
  have he : Fin.snoc ![P] z = ![P, z] := by ext i; fin_cases i <;> rfl
  rw [he]
  exact name_definable hM hinf hpair hunion hpower hsep hrep P z

omit [Preorder (Condition P.val)] in
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Define
    $$\Pi:=C\times P\in M.$$
-/
lemma boundedNamesName_mem {B : ZFSet.{u}} (hB : B ∈ M) : boundedNamesName P.val M B ∈ M :=
  prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (boundedNames_mem hM hinf hpair hunion hpower hsep hrep P hB) P.property

include hR

/-- All extension subsets of τ's value have names in a single ground-model power set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $x=\tau^G$ with $\tau\in M^P$, and put
    $$A:=\bigcup\bigcup\tau,\qquad B:=A\times P.$$
    Both sets belong to $M$. We first show that every $y\in M[G]$ with $y\IncludedIn x$ has a name
    $\theta\in M^P$ satisfying $\theta\IncludedIn B$.
    Choose $\nu\in M^P$ with $\nu^G=y$, and apply the construction in §{sec:generic-separation} to
    $\varphi(a,z)\equiv z\in a$, with parameter name $\nu$. It gives
    $$\begin{aligned}
    \theta:=\{\langle\sigma,q\rangle\in B:{}&\exists r\in P\,
     (\langle\sigma,r\rangle\in\tau\land q\le r\\
     &{}\land q\forces^*\sigma\in\nu)\}\in M^P.
    \end{aligned}$$
    The valuation identity proved there yields
    $$\theta^G=\{z\in\tau^G:z\in\nu^G\}=x\cap y=y.$$
    Thus every required subset has a name contained in the same set $B$, even when its initially chosen name $\nu$
    is not contained in $B$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\tau\in M^P$, the proof in §{sec:generic-power-set} constructs the ground-model sets
    $$\begin{aligned}
    B_\tau&:=\bigl(\bigcup\bigcup\tau\bigr)\times P,\\
    C_\tau&:=\{\theta\in\InternalPowerSet{M}{B_\tau}:\theta\in M^P\},\\
    \Pi_\tau&:=C_\tau\times P.
    \end{aligned}$$
    Every subset of $\tau^G$ belonging to the extension has a name in $C_\tau$.
    Let $\psi(a,z)$ be the bounded formula $z\IncludedIn a$, and define
    $$\ForcingPowerSetName{\tau}:=\ForcingSeparationName{\Pi_\tau}{\psi}{\tau}.$$
    For $A,B\in M$, let $\chi(A,B,g)$ be the bounded formula saying that $g$ is a function graph
    from $A$ to $B$, and define
    $$\begin{aligned}
    \rho_{A,B}&:=\ForcingPowerSetName{\check{(A\times B)}},\\
    \ForcingFunctionSpaceName{A}{B}&:=
    \ForcingSeparationName{\rho_{A,B}}{\chi}{(\check A,\check B)}.
    \end{aligned}$$
-/
theorem exists_bounded_subset_name (τ : Name P.val M)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (y : Extension P.val M G) (hy : y.val ⊆ value P.val G τ.val) :
    ∃ θ : Name P.val M, θ.val ⊆ ZFSet.prod (childBound τ.val) P.val ∧ value P.val G θ.val = y.val := by
  obtain ⟨ν, hν⟩ := evalName_surjective P.val M G y
  let φ := memberAt (1 : Fin 2) 0
  let θ : Name P.val M := ⟨separationName P.val M τ φ ![ν],
    separationName_mem_ground hM hinf hpair hunion hpower hsep hrep P R hR τ φ ![ν],
    separationName_isName P.val M τ φ ![ν]⟩
  refine ⟨θ, ?_, ?_⟩
  · intro z hz
    change z ∈ separationName P.val M τ φ ![ν] at hz
    rw [separationName, ZFSet.mem_sep] at hz
    exact hz.1
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hzE : z ∈ Extension P.val M G := hE.mem_trans hz (evalName P.val M G θ).property
    have ht := (mem_value_separationName P.val M hM τ φ ![ν] G
      (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG) ⟨z, hzE⟩).mp hz
    simpa [φ, realize_memberAt_model, Fin.snoc, hν] using ht.2
  · intro hz
    have hzE := hE.mem_trans hz y.property
    apply (mem_value_separationName P.val M hM τ φ ![ν] G
      (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG) ⟨z, hzE⟩).mpr
    exact ⟨hy hz, by simpa [φ, realize_memberAt_model, Fin.snoc, hν] using hz⟩

/-- Power Set follows from bounded subset names and the already proved Separation schema. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The set $\Pi^G$ may also contain sets not included in $x$.
    Apply the already proved Separation schema in $M[G]$ to $\Pi^G$, with parameter $x$ and formula
    $$\psi(x,y)\;:\equiv\;\forall z\in y\,(z\in x).$$
    Transitivity of the extension makes this formula equivalent to actual inclusion.
    We obtain
    $$p:=\{y\in\Pi^G:y\IncludedIn x\}\in M[G].$$
    For $y\in M[G]$, the preceding bound gives
    $$y\in p\quad\Longleftrightarrow\quad y\IncludedIn x.$$
    Thus $p=\InternalPowerSet{M[G]}{x}$, proving the internal Power Set axiom.
    The construction collects exactly the subsets that belong to the extension; it does not claim that every ambient
    subset of $x$ belongs to $M[G]$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Power Set in generic extensions
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    In particular, every $y\in M[G]$ with $y\IncludedIn x$ belongs to $\Pi^G$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The bounded supply of subset names in §{sec:generic-power-set} then proves Power Set.
-/
theorem extension_models_power (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    Extension P.val M G ⊨ powerSentence := by
  apply (models_power_iff _).mpr
  intro x
  obtain ⟨τ, hτ⟩ := evalName_surjective P.val M G x
  let B := ZFSet.prod (childBound τ.val) P.val
  have hB : B ∈ M := prod_mem_of_separation hM hpair hunion hpower (hsep _)
    (union_mem hM hunion (union_mem hM hunion τ.property.1)) P.property
  let piName : Name P.val M := ⟨boundedNamesName P.val M B,
    boundedNamesName_mem hM hinf hpair hunion hpower hsep hrep P hB,
    boundedNamesName_isName P.val M B⟩
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  have hsepE := extension_models_separation hM hinf hpair hunion hpower hsep hrep P R hR G hG subsetFormula
  obtain ⟨p, hp⟩ := (realize_separation _ subsetFormula).mp hsepE ![x] (evalName P.val M G piName)
  refine ⟨p, fun z => ?_⟩
  rw [hp, realize_subsetFormula hE, ← subset_iff_internal hE z.property]
  constructor
  · exact And.right
  · intro hz
    refine ⟨?_, hz⟩
    have hx : value P.val G τ.val = x.val := congrArg Subtype.val hτ
    obtain ⟨θ, hθB, he⟩ := exists_bounded_subset_name hM hinf hpair hunion hpower hsep hrep P R hR
      τ G hG z (hx.symm ▸ hz)
    exact (mem_value_boundedNamesName P.val M B G z.val).mpr ⟨θ, hθB, he⟩

end Model
end PolishSpaceBook.SetTheoryModels
