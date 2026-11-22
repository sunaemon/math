module

public import PolishSpaceBook.ForcingPowerSet
public import PolishSpaceBook.BorelCantorGraphs
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Uniform names for power sets and function spaces in a generic extension -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames BorelExpression
universe u

lemma chosen_meets_condition (P : ZFSet.{u}) [Preorder (Condition P)] (G : Order.PFilter (Condition P)) :
    ∃ p ∈ chosen P G, p ∈ P := by
  obtain ⟨p, hp⟩ := G.nonempty
  exact ⟨p.val, ⟨p, hp, rfl⟩, p.property⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

/-- The existing internal Separation construction, packaged as a ground-model name. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $\ForcingSeparationName{\tau}{\varphi}{\vec\nu}$ for the name constructed in
    §{sec:generic-separation}. For every $M$-generic filter $G$, it satisfies
    $$\begin{aligned}
    \bigl(\ForcingSeparationName{\tau}{\varphi}{\vec\nu}\bigr)^G
    =\{z\in\tau^G:M[G]\models\varphi(\vec\nu^G,z)\}.
    \end{aligned}$$
    Thus a formula with ground-model parameter names selects a subset of the valuation of a fixed name.
-/
def separatedName {n : ℕ} (τ : Name P.val M) (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name P.val M) : Name P.val M :=
  ⟨separationName P.val M τ φ xs,
    separationName_mem_ground hM hinf hpair hunion hpower hsep hrep P R hR τ φ xs,
    separationName_isName P.val M τ φ xs⟩

def internalCheckName (a : M) : Name P.val M :=
  ⟨check P.val a.val, check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep P a,
    check_isName P.val a.val⟩

include hM hinf hpair hunion hpower hsep hrep in
lemma value_internalCheckName (a : M) (G : Order.PFilter (Condition P.val)) :
    value P.val G (internalCheckName hM hinf hpair hunion hpower hsep hrep P a).val = a.val :=
  valuation_check P.val (chosen P.val G) (chosen_meets_condition P.val G) a.val

/-- A single family containing names for every subset of the value of τ. -/
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
def subsetNameCarrier (τ : Name P.val M) : Name P.val M :=
  ⟨boundedNamesName P.val M (prod (childBound τ.val) P.val),
    boundedNamesName_mem hM hinf hpair hunion hpower hsep hrep P
      (prod_mem_of_separation hM hpair hunion hpower (hsep _)
        (union_mem hM hunion (union_mem hM hunion τ.property.1)) P.property),
    boundedNamesName_isName P.val M _⟩

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
def powerSetName (τ : Name P.val M) : Name P.val M :=
  separatedName hM hinf hpair hunion hpower hsep hrep P R hR
    (subsetNameCarrier hM hinf hpair hunion hpower hsep hrep P τ) subsetFormula ![τ]

include hM hinf hpair hunion hpower hsep hrep hR in
lemma mem_value_powerSetName (τ : Name P.val M) (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) (y : Extension P.val M G) :
    y.val ∈ value P.val G (powerSetName hM hinf hpair hunion hpower hsep hrep P R hR τ).val ↔
      y.val ⊆ value P.val G τ.val := by
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  rw [powerSetName, separatedName, mem_value_separationName P.val M hM _ _ _ G
    (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG)]
  have he : (fun i : Fin 1 => evalName P.val M G (![τ] i)) =
      (![evalName P.val M G τ] : Fin 1 → Extension P.val M G) := by
    funext i; fin_cases i; rfl
  rw [he, realize_subsetFormula hE]
  refine ⟨And.right, fun hy => ⟨?_, hy⟩⟩
  obtain ⟨θ, hθ, heθ⟩ := exists_bounded_subset_name hM hinf hpair hunion hpower hsep hrep P R hR τ G hG y hy
  exact (mem_value_boundedNamesName P.val M _ G y.val).mpr ⟨θ, hθ, heθ⟩

include hM hinf hpair hunion hpower hsep hrep hR in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Uniform power-set and function-space names
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The bounded-name family and its all-conditions name belong to the ground model by
    §{sec:generic-power-set}; internal Separation then constructs the power-set name.
    Its valuation consists of those members of $\Pi_\tau^G$ included in $\tau^G$.
    Every such member belongs to the extension. Conversely, every extension subset of $\tau^G$ has a
    bounded name, so it lies in $\Pi_\tau^G$ and passes the subset test. This proves the first equality.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The checked product has value $A\times B$. Its power-set name therefore ranges over all extension
    subsets of that product. The shared bounded function predicate is absolute in the transitive
    extension, and the checked parameters have values $A$ and $B$. Applying the same Separation-name
    construction selects exactly the function graphs belonging to the extension, proving the second equality.
-/
theorem value_powerSetName (τ : Name P.val M) (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) :
    value P.val G (powerSetName hM hinf hpair hunion hpower hsep hrep P R hR τ).val =
      internalPowerSet (Extension P.val M G) (value P.val G τ.val) := by
  ext y
  rw [internalPowerSet, ZFSet.mem_sep]
  constructor
  · intro hy
    have hyE := (extension_isTransitive P.val M (chosen P.val G) hM).mem_trans hy
      (evalName P.val M G (powerSetName hM hinf hpair hunion hpower hsep hrep P R hR τ)).property
    exact ⟨hyE, (mem_value_powerSetName hM hinf hpair hunion hpower hsep hrep P R hR τ G hG ⟨y, hyE⟩).mp hy⟩
  · rintro ⟨hyE, hy⟩
    exact (mem_value_powerSetName hM hinf hpair hunion hpower hsep hrep P R hR τ G hG ⟨y, hyE⟩).mpr hy

/-- Function graphs are separated from the power set name of the checked Cartesian product. -/
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
def functionSpaceName (A B : M) : Name P.val M :=
  let AB : M := ⟨prod A.val B.val, prod_mem_of_separation hM hpair hunion hpower (hsep _) A.property B.property⟩
  separatedName hM hinf hpair hunion hpower hsep hrep P R hR
    (powerSetName hM hinf hpair hunion hpower hsep hrep P R hR
      (internalCheckName hM hinf hpair hunion hpower hsep hrep P AB))
    (BoundedSetPredicate.function 0 1 2).compile
    ![internalCheckName hM hinf hpair hunion hpower hsep hrep P A,
      internalCheckName hM hinf hpair hunion hpower hsep hrep P B]

include hM hinf hpair hunion hpower hsep hrep hR in
lemma mem_value_functionSpaceName (A B : M) (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) (g : Extension P.val M G) :
    g.val ∈ value P.val G (functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR A B).val ↔
      IsFunc A.val B.val g.val := by
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  rw [functionSpaceName, separatedName, mem_value_separationName P.val M hM _ _ _ G
    (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG)]
  rw [mem_value_powerSetName hM hinf hpair hunion hpower hsep hrep P R hR _ G hG g,
    value_internalCheckName, BoundedSetPredicate.realize_compile hE]
  change (_ ∧ IsFunc
    (value P.val G (internalCheckName hM hinf hpair hunion hpower hsep hrep P A).val)
    (value P.val G (internalCheckName hM hinf hpair hunion hpower hsep hrep P B).val) g.val) ↔ _
  rw [value_internalCheckName, value_internalCheckName]
  exact ⟨And.right, fun hg => ⟨hg.1, hg⟩⟩

include hM hinf hpair hunion hpower hsep hrep hR in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Uniform power-set and function-space names
-/
theorem value_functionSpaceName (A B : M) (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) :
    value P.val G (functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR A B).val =
      ZFSet.funs A.val B.val ∩ Extension P.val M G := by
  ext g
  rw [ZFSet.mem_inter, ZFSet.mem_funs]
  constructor
  · intro hg
    have hgE := (extension_isTransitive P.val M (chosen P.val G) hM).mem_trans hg
      (evalName P.val M G (functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR A B)).property
    exact ⟨(mem_value_functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR A B G hG ⟨g, hgE⟩).mp hg, hgE⟩
  · rintro ⟨hg, hgE⟩
    exact (mem_value_functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR A B G hG ⟨g, hgE⟩).mpr hg

end PolishSpaceBook.SetTheoryModels
