module

public import PolishSpaceBook.LambdaFunctionSpaces
public import PolishSpaceBook.LambdaHaltingObstruction
public import PolishSpaceBook.LambdaOutputSearch
public import PolishSpaceBook.LambdaRelativePredicates
public import PolishSpaceBook.LambdaRelativeProducts

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaFunction

/-- A modulus bounds the input prefix needed for an output prefix. -/
def NameModulus (F : (ℕ → ℕ) → (ℕ → ℕ)) (μ : ℕ → ℕ) : Prop :=
  ∀ p q n, (∀ i < μ n, p i = q i) → ∀ j < n, F p j = F q j

theorem computableNames_countable : {a : ℕ → ℕ | ComputableName a}.Countable := by
  let : Countable {f : ℕ → ℕ // LambdaRelative.Computable (fun _ => 0) f} :=
    LambdaRelative.countable_computable ℕ ℕ (fun _ => 0)
  have hrel (a : ℕ → ℕ) (ha : ComputableName a) :
      LambdaRelative.Computable (fun _ => 0) a := by
    obtain ⟨A, hA, hr⟩ := ha
    exact ⟨liftNumericalProgram A, LambdaRelative.ofNumerical ⟨hA, hr⟩ (fun _ => 0)⟩
  let embed : {a : ℕ → ℕ // ComputableName a} →
      {f : ℕ → ℕ // LambdaRelative.Computable (fun _ => 0) f} :=
    fun a => ⟨a.val, hrel a.val a.property⟩
  have hi : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {f : ℕ → ℕ // LambdaRelative.Computable (fun _ => 0) f} => z.val) h
  exact Set.countable_coe_iff.mp (Function.Injective.countable hi)

/-- A computable modulus cannot compute the independent output value. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Computability strictly refines continuity, but the
    refinement has two parts. A realizer must eventually find enough input to determine the $n$-th output coordinate, and it
    must also compute the value of that coordinate. A continuous function with a computable modulus need not be computable:
    the constant map $p\mapsto c$ has the trivial modulus for every $c\in\BaireSpace$, but it is computable only when the
    point $c$ is \termforwardas{computable point}{computable}.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The infinite oracle in a function name is essential for representing arbitrary continuous realizers. The following
    construction shows that a single finite reader suffices; all information about the particular realizer can be placed in
    its auxiliary oracle.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The converse is false as stated: not every continuous map is computable. Even when finite-prefix bounds are effectively
    available, the output values themselves may contain non-computable information; for example, the constant map with value
    a non-computable point of Baire space is continuous with trivial modulus but is not computable. Computability is
    continuity together with an effective procedure which, from the requested coordinate and the finite input information
    used, produces the corresponding output value.
-/
theorem exists_noncomputable_constant_with_modulus :
    ∃ c : ℕ → ℕ, Continuous (fun _ : ℕ → ℕ => c) ∧
      NameModulus (fun _ => c) (fun _ => 0) ∧
      NumericalComputes (numericalConstant 0) (fun _ => 0) ∧
      ¬ TypeTwoComputable (fun _ : (Set.univ : Set (ℕ → ℕ)) => c) := by
  have hn : ∃ c : ℕ → ℕ, ¬ ComputableName c := by
    obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.mp computableNames_countable
    refine ⟨fun n => e n n + 1, ?_⟩
    intro hc
    obtain ⟨n, hn⟩ := he hc
    have hx := congrFun hn n
    omega
  obtain ⟨c, hc⟩ := hn
  exact ⟨c, continuous_const, fun _ _ _ _ _ _ => rfl,
    numericalConstant_computes 0, fun h => hc ((computableName_iff_constant c).mpr h)⟩

namespace Representation

/-- The topology on points induced by the partial representation's name domain. -/
abbrev finalTopology {X : Type*} (δ : Representation X) : TopologicalSpace X :=
  TopologicalSpace.coinduced δ.toFun inferInstance

theorem isOpen_finalTopology_iff {X : Type*} (δ : Representation X) (U : Set X) :
    @IsOpen X δ.finalTopology U ↔ IsOpen (δ.toFun ⁻¹' U) := Iff.rfl

/-- Admissibility recovers the original topology of a sequential space. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termdefine{represented space} is a pair
    $$\mathbf X=(X,\delta_X)$$
    where $X$ is a set and $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$ is a partial function whose range is all of $X$.
    A point $p\in \DomainOf{\delta_X}$ is a \termdefineas{represented-space name}{name} of $x$ when $\delta_X(p)=x$. The
    topology induced by $\delta_X$ is the final topology: $U\IncludedIn X$ is open when $\delta_X^{-1}(U)$ is open in
    $\DomainOf{\delta_X}$. For
    \termuseas{admissible representation of topological space}{admissible representations} of Polish spaces this recovers
    the original topology.
-/
theorem finalTopology_eq_of_admissible {X : Type*} [TopologicalSpace X]
    [SequentialSpace X] (δ : Representation X) (hδ : δ.IsAdmissible) :
    δ.finalTopology = ‹TopologicalSpace X› :=
  (isQuotientMap_of_admissible δ hδ).eq_coinduced.symm

end Representation

namespace LambdaIndexPCA

/-- Feed a program's numerical index to the same indexed program. -/
def diagonalHaltingSemidecider : AlphaTerm :=
  lam 40 (app (app outputSearchTerm (var 40)) (var 40))

theorem diagonalHaltingSemidecider_closed : diagonalHaltingSemidecider.Closed := by
  unfold diagonalHaltingSemidecider Closed
  simp only [fv_lam, fv_app, fv_var, (show outputSearchTerm.fv = ∅ from outputSearchTerm_closed)]
  decide

/-- Ordinary finite reduction-certificate search enumerates exactly diagonal halting. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Fix an effective enumeration $(\varphi_e)$ of the partial numerical functions computed by closed lambda terms, and let
    $$K:=\{e\in\NN:\varphi_e(e)\downarrow\}.$$
    Here the downward arrow means that the computation returns a numeral. The set $K$ is recursively enumerable by finite
    simulation, but undecidable. Indeed, a decider would give a program that returns zero on $e\notin K$ and diverges on
    $e\in K$; applying that program to its own index gives a contradiction.
-/
theorem diagonalHalts_semidecidable (e : ℕ) :
    (∃ m, Relation.ReflTransGen Beta (app diagonalHaltingSemidecider (numeral e)) (numeral m)) ↔
      diagonalHalts e := by
  have hs : Relation.ReflTransGen Beta (app diagonalHaltingSemidecider (numeral e))
      (app (app outputSearchTerm (numeral e)) (numeral e)) := by
    apply Relation.ReflTransGen.single
    simpa [diagonalHaltingSemidecider, subst_app, subst_var,
      subst_closed _ _ _ outputSearchTerm_closed] using
      Beta.contract 40 (app (app outputSearchTerm (var 40)) (var 40)) (numeral e)
  exact exists_congr fun m =>
    ⟨fun hm => (outputSearchTerm_runs_iff e e m).mp (numeral_after_reduction hs hm),
      fun hm => hs.trans ((outputSearchTerm_runs_iff e e m).mpr hm)⟩

end LambdaIndexPCA

end PolishSpaceBook
