module

public import PolishSpaceBook.CantorInternalWords
public import PolishSpaceBook.BorelInternalInclusion

@[expose] public section

/-! # Bounded recognition of approximation trees and Borel inclusions -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

lemma binary_word_mem (T : Set (List Bool)) (s : List Bool) :
    wordGraph (s.map Bool.toNat) ∈ wordTreeSet.{u} (binaryLift T) ↔ s ∈ T := by
  rw [wordGraph_mem_wordTreeSet]
  exact ⟨fun ⟨t, ht, he⟩ => (List.map_injective_iff.mpr bool_toNat_injective) he ▸ ht,
    fun hs => ⟨s, hs, rfl⟩⟩

lemma binary_map_prefix_iff (s t : List Bool) :
    (s.map Bool.toNat).IsPrefix (t.map Bool.toNat) ↔ s.IsPrefix t := by
  constructor
  · intro h
    have he := List.prefix_iff_eq_take.mp h
    simp only [List.length_map, ← List.map_take] at he
    rw [(List.map_injective_iff.mpr bool_toNat_injective) he]
    exact List.take_prefix _ _
  · intro h
    obtain ⟨r, rfl⟩ := h
    exact ⟨r.map Bool.toNat, by simp⟩

/-- Parameters the full binary-word set and the proposed tree code. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following bounded predicates on proposed tree codes and point graphs:
    $$\begin{aligned}
    \mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
    &\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
    \mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
    \mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
    &(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
    &{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
    \end{aligned}$$
    Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
    exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
    family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
    all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
    its natural-number copy.
-/
def binaryTreePredicate : BoundedSetPredicate 2 :=
  .conj (.subset 1 0) (.all 1 (.all 0 ((BoundedSetPredicate.subset 3 2).imply (.member 3 1))))

lemma eval_binaryTreePredicate (T : Set (List Bool)) :
    binaryTreePredicate.eval ![wordTreeSet.{u} (binaryLift Set.univ), wordTreeSet (binaryLift T)] ↔
      IsSubtree T := by
  change (wordTreeSet (binaryLift T) ⊆ wordTreeSet (binaryLift Set.univ) ∧
    ∀ s ∈ wordTreeSet (binaryLift T), ∀ t ∈ wordTreeSet (binaryLift Set.univ),
      (¬ t ⊆ s ∨ t ∈ wordTreeSet (binaryLift T))) ↔ _
  simp only [← imp_iff_not_or]
  constructor
  · rintro ⟨_, h⟩ t s hs ht
    apply (binary_word_mem T t).mp
    exact h _ ((binary_word_mem T s).mpr hs) _ ((binary_word_mem Set.univ t).mpr (Set.mem_univ _))
      (wordGraph_subset_iff.mpr ((binary_map_prefix_iff t s).mpr ht))
  · intro hT
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨s, ⟨t, ht, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
      exact (binary_word_mem Set.univ t).mpr (Set.mem_univ _)
    · intro x hx y hy hsub
      obtain ⟨s, ⟨t, ht, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
      obtain ⟨s', ⟨t', _, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hy
      exact (binary_word_mem T t').mpr (hT ht ((binary_map_prefix_iff t' t).mp
        (wordGraph_subset_iff.mp hsub)))

/-- Every accepted set is the entire graph code of an actual downward-closed binary tree. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following bounded predicates on proposed tree codes and point graphs:
    $$\begin{aligned}
    \mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
    &\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
    \mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
    \mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
    &(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
    &{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
    \end{aligned}$$
    Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
    exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
    family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
    all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
    its natural-number copy.
-/
lemma binaryTreePredicate_iff (W : ZFSet.{u}) :
    binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), W] ↔
      ∃ T : Set (List Bool), IsSubtree T ∧ W = wordTreeSet (binaryLift T) := by
  constructor
  · intro h
    have hsub : W ⊆ wordTreeSet (binaryLift Set.univ) := h.1
    let T : Set (List Bool) := {s | wordGraph (s.map Bool.toNat) ∈ W}
    have he : W = wordTreeSet (binaryLift T) := by
      ext x
      constructor
      · intro hx
        obtain ⟨s, ⟨t, _, rfl⟩, rfl⟩ := mem_wordTreeSet.mp (hsub hx)
        exact (binary_word_mem T t).mpr hx
      · intro hx
        obtain ⟨s, ⟨t, ht, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
        exact ht
    exact ⟨T, (eval_binaryTreePredicate T).mp (he ▸ h), he⟩
  · rintro ⟨T, ht, rfl⟩
    exact (eval_binaryTreePredicate T).mpr ht

/-- Parameters finite words, tree code, point graph. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following bounded predicates on proposed tree codes and point graphs:
    $$\begin{aligned}
    \mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
    &\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
    \mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
    \mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
    &(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
    &{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
    \end{aligned}$$
    Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
    exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
    family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
    all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
    its natural-number copy.
-/
def branchPredicate : BoundedSetPredicate 3 :=
  .all 0 ((BoundedSetPredicate.subset 3 2).imply (.member 3 1))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following bounded predicates on proposed tree codes and point graphs:
    $$\begin{aligned}
    \mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
    &\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
    \mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
    \mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
    &(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
    &{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
    \end{aligned}$$
    Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
    exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
    family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
    all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
    its natural-number copy.
-/
lemma eval_branchPredicate (T : Set (List ℕ)) (x : ℕ → ℕ) :
    branchPredicate.eval ![finiteSequences.{u}, wordTreeSet T, pointGraph x] ↔ x ∈ treeBody T := by
  change (∀ s ∈ finiteSequences, ¬ s ⊆ pointGraph x ∨ s ∈ wordTreeSet T) ↔ _
  simp only [← imp_iff_not_or]
  constructor
  · intro h n
    apply wordGraph_mem_wordTreeSet.mp
    exact h _ (mem_finiteSequences.mpr ⟨_, rfl⟩)
      (wordGraph_subset_pointGraph _ _ |>.mpr (mem_cyl_seqPrefix x n))
  · intro hx s hs hp
    obtain ⟨t, rfl⟩ := mem_finiteSequences.mp hs
    have he := seqPrefix_eq_of_mem_cyl ((wordGraph_subset_pointGraph _ _).mp hp)
    exact wordGraph_mem_wordTreeSet.mpr (he ▸ hx t.length)

/-- Parameters finite words, internal points, internal Borel set, inner tree, outer-complement tree. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define the following bounded predicates on proposed tree codes and point graphs:
    $$\begin{aligned}
    \mathrm{Tree}(W):\equiv{}&W\IncludedIn F_2\land\forall \sigma\in W\;\forall \tau\in F_2\;[\\
    &\tau\IncludedIn \sigma\longrightarrow \tau\in W],\\
    \mathrm{Br}(W,g):\equiv{}&\forall \sigma\in F\;(\sigma\IncludedIn g\longrightarrow \sigma\in W),\\
    \mathrm{Inc}(B,W,V):\equiv{}&\forall g\in X_M\;[\\
    &(\mathrm{Br}(W,g)\longrightarrow g\in B)\\
    &{}\land(\mathrm{Br}(V,g)\longrightarrow g\notin B)].
    \end{aligned}$$
    Graph inclusion between finite words is the prefix relation. Consequently, $\mathrm{Tree}(W)$ holds
    exactly when $W=W_T$ for a downward-closed binary tree $T$; every subset of $F_2$ codes the corresponding
    family of binary words. For a point graph $g_x$, the condition $\mathrm{Br}(W_T,g_x)$ says exactly that
    all finite prefixes of $x$ lie in $T$. We use the Baire point graphs here, identifying a binary tree with
    its natural-number copy.
-/
def approximationInclusionPredicate : BoundedSetPredicate 5 :=
  .all 1 (.conj ((branchPredicate.rename ![0, 3, 5]).imply (.member 5 2))
    ((branchPredicate.rename ![0, 4, 5]).imply (.neg (.member 5 2))))

lemma eval_approximationInclusionPredicate (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (T S : Set (List ℕ)) :
    approximationInclusionPredicate.eval ![finiteSequences, internalBaire M,
      internalInterpretation M c hw NamedLambda.NatListCode.decode [], wordTreeSet T, wordTreeSet S] ↔
      (∀ x ∈ treeBody T, pointGraph x ∈ M → x ∈ c.evaluate hw cylinderBasis []) ∧
      (∀ x ∈ treeBody S, pointGraph x ∈ M → x ∉ c.evaluate hw cylinderBasis []) := by
  have he (g : ZFSet.{u}) :
      (Fin.snoc ![finiteSequences, internalBaire M,
        internalInterpretation M c hw NamedLambda.NatListCode.decode [], wordTreeSet T, wordTreeSet S] g) ∘
          ![(0 : Fin 6), 3, 5] = ![finiteSequences, wordTreeSet T, g] := by
    funext i; fin_cases i <;> rfl
  have he' (g : ZFSet.{u}) :
      (Fin.snoc ![finiteSequences, internalBaire M,
        internalInterpretation M c hw NamedLambda.NatListCode.decode [], wordTreeSet T, wordTreeSet S] g) ∘
          ![(0 : Fin 6), 4, 5] = ![finiteSequences, wordTreeSet S, g] := by
    funext i; fin_cases i <;> rfl
  simp only [approximationInclusionPredicate, eval, eval_imply, eval_rename, he, he']
  change (∀ g ∈ internalBaire M,
    (branchPredicate.eval ![finiteSequences, wordTreeSet T, g] →
      g ∈ internalInterpretation M c hw NamedLambda.NatListCode.decode []) ∧
    (branchPredicate.eval ![finiteSequences, wordTreeSet S, g] →
      g ∉ internalInterpretation M c hw NamedLambda.NatListCode.decode [])) ↔ _
  constructor
  · intro h
    constructor
    · intro x hx hxM
      exact ((pointGraph_mem_internalInterpretation M c hw _ [] x).mp
        ((h _ ((pointGraph_mem_internalBaire x).mpr hxM)).1 ((eval_branchPredicate T x).mpr hx))).2
    · intro x hx hxM hmem
      exact (h _ ((pointGraph_mem_internalBaire x).mpr hxM)).2 ((eval_branchPredicate S x).mpr hx)
        ((pointGraph_mem_internalInterpretation M c hw _ [] x).mpr ⟨hxM, hmem⟩)
  · rintro ⟨ht, hs⟩ g hg
    obtain ⟨x, rfl, hxM⟩ := mem_internalBaire.mp hg
    rw [eval_branchPredicate, eval_branchPredicate, pointGraph_mem_internalInterpretation]
    exact ⟨fun hx => ⟨hxM, ht x hx hxM⟩, fun hx h => hs x hx hxM h.2⟩

/-- The bounded old-point tests imply both inclusions on all external binary points. -/
theorem approximationInclusion_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (T S : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) (hS : wordTreeSet (binaryLift S) ∈ M) :
    approximationInclusionPredicate.eval ![finiteSequences, internalBaire M,
      internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode [],
      wordTreeSet (binaryLift T), wordTreeSet (binaryLift S)] ↔
      treeBody T ⊆ cantorSet c hc.2.2.2.2.2 ∧ cantorSet c hc.2.2.2.2.2 ⊆ (treeBody S)ᶜ := by
  rw [eval_approximationInclusionPredicate]
  constructor
  · rintro ⟨ht, hs⟩
    have ht' := closed_inclusion_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      (binaryLift T) hT (fun x hx hxM =>
        (pointGraph_mem_internalInterpretation M c _ _ [] x).mpr ⟨hxM, ht x hx hxM⟩)
    have hs' := closed_disjoint_of_internal_points hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      (binaryLift S) hS hs
    exact ⟨fun x hx => ht' (cantorInclusion_mem_binaryLift_body hx),
      fun x hx hsx => hs' _ (cantorInclusion_mem_binaryLift_body hsx) hx⟩
  · rintro ⟨ht, hs⟩
    constructor
    · intro x hx _
      obtain ⟨y, hy, rfl⟩ := (Set.ext_iff.mp (binaryLift_body T) x).mp hx
      exact ht hy
    · intro x hx _ hmem
      obtain ⟨y, hy, rfl⟩ := (Set.ext_iff.mp (binaryLift_body S) x).mp hx
      exact hs hmem hy

end PolishSpaceBook.CantorTreeMeasure
