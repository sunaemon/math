module

public import PolishSpaceBook.LambdaHKLStages

@[expose] public section

/-!
# Relative HKL binary levels from the actual kernel

Duplicate the old level, refine nodes, rectangles and edges, and transport
back along the last-bit decomposition. Iterate this successor operation
inside the actual HKL kernel. Density is in the fixed-parameter catalog;
no extra kernel-code or distinct-pair hypothesis is used. Scheduling and
actual branch/edge fusion are supplied by `LambdaHKLScheduling` and
`LambdaHKLFusion`. The generic-pair truth theorem remains separate.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set SimpleGraph

variable {ε : ℕ → ℕ}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Given level $n$, first duplicate its sets and relations into
    the two last-bit copies. On the new joining edge put the full relation
    $$R_{0^n\concat(0),0^n\concat(1)}
       =E\cap(A_{0^n\concat(0)}\times A_{0^n\concat(1)}).$$
    Initially its endpoint sets are equal, so reflexivity gives full projections. The duplicated system is coherent.
-/
def parameterDuplicateBinaryLevel {n : ℕ} (S : ParameterTreeSystem ε (crucialPairGraph n))
    (E : Setoid FusionReal) (hSE : S.val.EdgesIn E) :
    ParameterSplitTree ε (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n) E := ⟨S, S, hSE, hSE, rfl⟩

def parameterBinarySuccessorSystem {n : ℕ}
    (S : ParameterTreeSystem ε (joinedTreeGraph (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n))) : ParameterTreeSystem ε (crucialPairGraph (n + 1)) :=
  ⟨binarySuccessorSystem S.val, fun v => S.property.1 (splitLastBit n v),
    fun _ _ h => S.property.2 _ _ h⟩

def ParameterHKLSuccessorRequirements {n : ℕ} (E : Setoid FusionReal)
    (D : Set (parameterAnalyticCatalog ε).Condition) (J : Set (ParameterCompatibleRectangle ε E))
    (K : Set (parameterAnalyticCatalog ε).Condition)
    (S : ParameterTreeSystem ε (crucialPairGraph n))
    (T : ParameterTreeSystem ε (crucialPairGraph (n + 1))) : Prop :=
      (∀ s b, T.val.node (Fin.snoc s b) ⊆ S.val.node s) ∧
      (∀ s t b, T.val.edge (Fin.snoc s b) (Fin.snoc t b) ⊆ S.val.edge s t) ∧
      (∀ s, T.nodeCondition s ∈ D) ∧
      (∀ s t (h : (crucialPairGraph (n + 1)).Adj s t), T.edgeCondition h ∈ K) ∧
      ∃ hTE : T.val.EdgesIn E, ∀ r s,
        T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
          (Fin.snoc r false) (Fin.snoc s true) ∈ J ∧
        T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
          (Fin.snoc s true) (Fin.snoc r false) ∈ J ∧
        Disjoint (T.val.node (Fin.snoc r false)) (T.val.node (Fin.snoc s true))

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Every old copied edge has only
    been restricted, so its parent-containment requirement holds too. This completes the induction and proves that
    all three requirements can be achieved simultaneously.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    At this last step the joining edge need no longer remain a full $E$-relation.
-/
theorem parameter_hkl_successor_level {n : ℕ}
    (S : ParameterTreeSystem ε (crucialPairGraph n)) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hSE : S.val.EdgesIn E)
    (D : Set (parameterAnalyticCatalog ε).Condition) (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (J : Set (ParameterCompatibleRectangle ε E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (K : Set (parameterAnalyticCatalog ε).Condition) (hKd : IsCoinitial K) (hKl : IsLowerSet K)
    (hkernel : ∀ r, S.val.node r ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ T : ParameterTreeSystem ε (crucialPairGraph (n + 1)),
      ParameterHKLSuccessorRequirements E D J K S T := by
  let B := parameterDuplicateBinaryLevel S E hSE
  obtain ⟨U, hUB, hUD, hUK, hUE, hUJ⟩ := B.refine_three_stages
    (crucialPairGraph_isTree n) (crucialPairGraph_isTree n) hE hneE
    D hDd hDl J hJd hJl K hKd hKl hkernel
  let T := parameterBinarySuccessorSystem U
  have hTE : T.val.EdgesIn E := fun u v h => hUE _ _ h
  refine ⟨T, ?_, ?_, ?_, ?_, hTE, ?_⟩
  · intro s b
    cases b
    · have h : U.val.node (.inl s) ⊆ S.val.node s := hUB.1 (.inl s)
      simpa only [T, parameterBinarySuccessorSystem, binarySuccessorSystem_node_false] using h
    · have h : U.val.node (.inr s) ⊆ S.val.node s := hUB.1 (.inr s)
      simpa only [T, parameterBinarySuccessorSystem, binarySuccessorSystem_node_true] using h
  · intro s t b
    cases b
    · have h : U.val.edge (.inl s) (.inl t) ⊆ S.val.edge s t := hUB.2 (.inl s) (.inl t)
      simpa [T, parameterBinarySuccessorSystem, binarySuccessorSystem, AnalyticTreeSystem.comap,
        splitLastBit] using h
    · have h : U.val.edge (.inr s) (.inr t) ⊆ S.val.edge s t := hUB.2 (.inr s) (.inr t)
      simpa [T, parameterBinarySuccessorSystem, binarySuccessorSystem, AnalyticTreeSystem.comap,
        splitLastBit] using h
  · intro s
    exact hUD (splitLastBit n s)
  · intro s t h
    exact hUK (splitLastBit n s) (splitLastBit n t) h
  · intro r s
    have hf : T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
        (Fin.snoc r false) (Fin.snoc s true) =
        U.rectangleCondition (isTree_sum_join (crucialPairGraph_isTree n)
          (crucialPairGraph_isTree n) (zeroBinaryWord n) (zeroBinaryWord n)).connected E hUE
          (.inl r) (.inr s) := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;>
        simp [ParameterTreeSystem.rectangleCondition, ParameterTreeSystem.nodeCondition,
          parameterCondition, T, parameterBinarySuccessorSystem]
    have hb : T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
        (Fin.snoc s true) (Fin.snoc r false) =
        U.rectangleCondition (isTree_sum_join (crucialPairGraph_isTree n)
          (crucialPairGraph_isTree n) (zeroBinaryWord n) (zeroBinaryWord n)).connected E hUE
          (.inr s) (.inl r) := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;>
        simp [ParameterTreeSystem.rectangleCondition, ParameterTreeSystem.nodeCondition,
          parameterCondition, T, parameterBinarySuccessorSystem]
    refine ⟨hf.symm ▸ (hUJ r s).1, hb.symm ▸ (hUJ r s).2.1, ?_⟩
    simpa only [T, parameterBinarySuccessorSystem, binarySuccessorSystem_node_false,
      binarySuccessorSystem_node_true] using (hUJ r s).2.2

/-- Iterate the relative successor operation, retaining kernel membership. -/
theorem parameter_hkl_coherent_levels (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (S₀ : ParameterTreeSystem ε (crucialPairGraph 0)) (hS₀E : S₀.val.EdgesIn E)
    (hS₀Ω : ∀ s, S₀.val.node s ⊆ equivalenceGapKernel E (invariantSetoid ε E))
    (D : ℕ → Set (parameterAnalyticCatalog ε).Condition) (hDd : ∀ n, IsCoinitial (D n))
    (hDl : ∀ n, IsLowerSet (D n))
    (J : ℕ → Set (ParameterCompatibleRectangle ε E)) (hJd : ∀ n, IsCoinitial (J n))
    (hJl : ∀ n, IsLowerSet (J n))
    (K : ℕ → Set (parameterAnalyticCatalog ε).Condition) (hKd : ∀ n, IsCoinitial (K n))
    (hKl : ∀ n, IsLowerSet (K n)) :
    ∃ S : ∀ n, ParameterTreeSystem ε (crucialPairGraph n),
      S 0 = S₀ ∧ (∀ n, (S n).val.EdgesIn E) ∧
      (∀ n s, (S n).val.node s ⊆ equivalenceGapKernel E (invariantSetoid ε E)) ∧
      ∀ n, ParameterHKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1))
        (S n) (S (n + 1)) := by
  classical
  let State (n : ℕ) := {S : ParameterTreeSystem ε (crucialPairGraph n) //
    S.val.EdgesIn E ∧ ∀ s, S.val.node s ⊆ equivalenceGapKernel E (invariantSetoid ε E)}
  have hnext (n : ℕ) (S : State n) : ∃ T : State (n + 1),
      ParameterHKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1)) S.val T.val := by
    obtain ⟨T, hT⟩ := parameter_hkl_successor_level S.val E hE hneE S.property.1
      (D (n + 1)) (hDd _) (hDl _) (J (n + 1)) (hJd _) (hJl _)
      (K (n + 1)) (hKd _) (hKl _) S.property.2
    obtain ⟨hTE, _⟩ := hT.2.2.2.2
    have hTΩ (w : binaryWord (n + 1)) :
        T.val.node w ⊆ equivalenceGapKernel E (invariantSetoid ε E) := by
      have hsub := hT.1 (Fin.init w) (w (Fin.last n))
      rw [Fin.snoc_init_self] at hsub
      exact hsub.trans (S.property.2 _)
    exact ⟨⟨T, hTE, hTΩ⟩, hT⟩
  let states : (n : ℕ) → State n :=
    fun n => Nat.rec (motive := fun n => State n) ⟨S₀, hS₀E, hS₀Ω⟩
      (fun n S => (hnext n S).choose) n
  refine ⟨fun n => (states n).val, rfl, fun n => (states n).property.1,
    fun n => (states n).property.2, ?_⟩
  intro n
  exact (hnext n (states n)).choose_spec

def parameterRootBinarySystem (C : (parameterAnalyticCatalog ε).Condition) :
    ParameterTreeSystem ε (crucialPairGraph 0) :=
  ⟨rootBinarySystem C.val, fun _ => parameterCondition_projected ε C,
    fun _ _ h => False.elim h⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Start with any $A_\emptyset\in D_0$ contained in $H$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Construct coherent systems at all levels with the following additional requirements:
    \begin{enumerate}
    \item $A_{s\concat(i)}\IncludedIn A_s$ and $A_s\in D_n$ for $s\in2^n$;
    \item $R_{s\concat(i),t\concat(i)}\IncludedIn R_{s,t}$ for every old crucial pair, and
          $R_{s,t}\in K_n$ for every crucial pair at level $n$;
    \item whenever $s,t\in2^n$ have different last bits,
          $A_s\times A_t\in J_n$ and $A_s\cap A_t=\emptyset$.
    \end{enumerate}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    The refinements are performed in the following order.
-/
/-- Start with a condition inside the actual nonsmooth kernel and construct
all levels. Kernel analyticity, nonemptiness and splitting are proved inputs. -/
theorem parameter_hkl_coherent_levels_from_kernel (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r)
    (D : ℕ → Set (parameterAnalyticCatalog ε).Condition) (hDd : ∀ n, IsCoinitial (D n))
    (hDl : ∀ n, IsLowerSet (D n))
    (J : ℕ → Set (ParameterCompatibleRectangle ε E)) (hJd : ∀ n, IsCoinitial (J n))
    (hJl : ∀ n, IsLowerSet (J n))
    (K : ℕ → Set (parameterAnalyticCatalog ε).Condition) (hKd : ∀ n, IsCoinitial (K n))
    (hKl : ∀ n, IsLowerSet (K n)) :
    ∃ S : ∀ n, ParameterTreeSystem ε (crucialPairGraph n),
      (∀ n, (S n).val.EdgesIn E) ∧
      (∀ n s, (S n).val.node s ⊆ equivalenceGapKernel E (invariantSetoid ε E)) ∧
      (∀ n s, (S n).nodeCondition s ∈ D n) ∧
      (∀ n s t (h : (crucialPairGraph n).Adj s t), (S n).edgeCondition h ∈ K n) ∧
      ∀ n, ParameterHKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1))
        (S n) (S (n + 1)) := by
  obtain ⟨C, hCD, hCΩ⟩ := hDd 0 (parameterHKLKernelCondition ε E hE hneE hns)
  have hrootE : (parameterRootBinarySystem C).val.EdgesIn E := fun _ _ h => False.elim h
  obtain ⟨S, hS0, hSE, hSΩ, hstep⟩ := parameter_hkl_coherent_levels E hE hneE
    (parameterRootBinarySystem C) hrootE (fun _ => hCΩ) D hDd hDl J hJd hJl K hKd hKl
  refine ⟨S, hSE, hSΩ, ?_, ?_, hstep⟩
  · intro n
    cases n with
    | zero => intro s; rw [hS0]; exact hCD
    | succ n => exact (hstep n).2.2.1
  · intro n
    cases n with
    | zero => exact fun _ _ h => False.elim h
    | succ n => exact (hstep n).2.2.2.1

end LambdaTree
end PolishSpaceBook
