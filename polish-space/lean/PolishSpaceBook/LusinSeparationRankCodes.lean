module

public import PolishSpaceBook.LambdaRankComparisons
public import PolishSpaceBook.LambdaBorelCodeCompleteness
public import PolishSpaceBook.LusinRankSeparation

@[expose] public section

/-! # The effective Lusin separator is an actual bounded tree-rank layer

The joint-tree root supplies the ordinal bound. The existing lambda label
program computes the code of exactly that layer at the original parameter.
A recursive presentation of the ordinal exists; computing the separator does
not require selecting a presentation or a branch.
-/

noncomputable section
namespace PolishSpaceBook
open Set MeasureTheory NamedLambda BorelExpression
namespace LambdaTree

/-- The ordinal bound used by the concrete rank-layer separator. -/
def separatorOrdinal {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) : Ordinal :=
  ((jointTree_wellFounded T S hd).apply (jointTree T S).root).rank

/-- The recursive Kleene--Brouwer presentation bounds this root rank. -/
theorem separatorOrdinal_recursive {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    LambdaRelative.RecursiveOrdinal ε (separatorOrdinal T S hd) := by
  apply LambdaRelative.recursiveOrdinal_of_lt_bound
  exact (KleeneBrouwer.rank_lt_presentation (jointPrefixTree T S)
    (jointTree_wellFounded T S hd) (jointTree T S).root).trans
      (KleeneBrouwer.recursive_rank_bound (jointPrefixTree T S) (jointTree_wellFounded T S hd)).1

/-- The computed code denotes the initial segment of the original section-tree norm. -/
theorem recursiveSeparatorCode_eq_rankLayer {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    (recursiveSeparatorCode T S hd).value cylinderBasis =
      sectionRankLayer S (separatorOrdinal T S hd) := by
  ext x
  rw [recursiveSeparatorCode, RankBound.mem_value_code_iff cylinderBasis
    (by simp [cylinderBasis, NatListCode.decode])]
  have he : (fun b a => x ∈ (sectionEdgeCode S b a).value cylinderBasis) =
      (rootedSection S x).codedExtension := by
    funext b a
    exact propext (mem_sectionEdgeCode S b a x)
  rw [he]
  change (∃ hs : Acc (rootedSection S x).codedExtension 0,
    hs.rank ≤ _) ↔ ∃ hw : WellFounded (strictTreeExtension (rootedSection S x).tree), _
  rw [RootedPrefixTree.coded_root_rank_eq (jointTree T S) (jointTree_wellFounded T S hd)]
  constructor
  · rintro ⟨hs, hb⟩
    have hw := (rootedSection S x).wellFounded_of_codedExtension
      ((rootedSection S x).codedExtension_wellFounded_of_root_acc hs)
    refine ⟨hw, ?_⟩
    change (hw.apply (rootedSection S x).root).rank ≤ _
    rw [← RootedPrefixTree.coded_root_rank_eq (rootedSection S x) hw]
    exact hb
  · rintro ⟨hw, hb⟩
    refine ⟨((rootedSection S x).codedExtension_wellFounded hw).apply 0, ?_⟩
    rw [RootedPrefixTree.coded_root_rank_eq (rootedSection S x) hw]
    exact hb

/-- Boundedness and the lambda rank-label program give the same separator. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For the relative assertion, use the given pair trees $T_0,T_1$ for $A_0,A_1$, and take $\varphi(x)$ to be the root
    rank of $(T_1)_x$. The joint tree $J$ in §{sec:lambda-recursive-borel-separation} is well founded, and its root
    rank $\alpha$ bounds every $\varphi(x)$ for $x\in A_0$. Its Kleene--Brouwer presentation has larger
    $a$-recursive order type, so downward closure gives an $a$-recursive well-order presentation of $\alpha$.
    The rank-layer code constructed there has value exactly $B$: accessibility of the section root is equivalent
    to $x\notin A_1$, and its rank is at most the rank of the root of $J$ exactly when $\varphi(x)\le\alpha$.
    The closed lambda rank-label program computes this code at the same parameter $a$. This construction uses
    the two tree deciders directly; it does not select an ordinal presentation or a branch. The existence of the
    ordinal presentation and the computation of the separator are distinct conclusions.
    \end{proof}
-/
theorem recursive_lusin_rank_separator {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    ∃ α : Ordinal, LambdaRelative.RecursiveOrdinal ε α ∧
      HasRecursiveBorelCode ε (sectionRankLayer S α) ∧
      pairTreeProjection T.tree ⊆ sectionRankLayer S α ∧
      sectionRankLayer S α ⊆ (pairTreeProjection S.tree)ᶜ := by
  refine ⟨separatorOrdinal T S hd, separatorOrdinal_recursive T S hd, ?_, ?_, ?_⟩
  · exact ⟨recursiveSeparatorCode T S hd, recursiveSeparatorCode_computable T S hd,
      (recursiveSeparatorCode_eq_rankLayer T S hd).symm⟩
  · rw [← recursiveSeparatorCode_eq_rankLayer T S hd]
    exact (recursiveSeparatorCode_value T S hd).1
  · rw [← recursiveSeparatorCode_eq_rankLayer T S hd]
    exact (recursiveSeparatorCode_value T S hd).2

/-- The boldface rank proof applies boundedness to the analytic subset of
well-founded sections of the complement's fixed presentation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Apply the tree-rank coanalytic norm $\varphi$ to the coanalytic set
    $\SetDifference{\BaireSpace}{A_1}$. Since $A_0$ is analytic and contained in that coanalytic set, boundedness gives
    an ordinal $\alpha$ with $A_0\IncludedIn(\SetDifference{\BaireSpace}{A_1})_{\le\alpha}$.
    Take this initial segment as $B$. It is Borel by the definition of the norm and is disjoint from $A_1$.
-/
theorem analytic_lusin_rank_separator {A₀ A₁ : Set (ℕ → ℕ)}
    (hA₀ : AnalyticSet A₀) (hA₁ : AnalyticSet A₁) (hd : Disjoint A₀ A₁) :
    ∃ (ε : ℕ → ℕ) (S : PairTree ε), pairTreeProjection S.tree = A₁ ∧
      ∃ α < Ordinal.omega 1, MeasurableSet (sectionRankLayer S α) ∧
        A₀ ⊆ sectionRankLayer S α ∧ sectionRankLayer S α ⊆ A₁ᶜ := by
  obtain ⟨ε, S, hS⟩ := (analyticSet_iff_exists_parameter A₁).mp hA₁
  have hw : ∀ x ∈ A₀, WellFounded (strictTreeExtension (rootedSection S x).tree) := by
    intro x hx
    apply (prefixTreeWellFounded_iff _ (rootedSection S x).downward).mp
    intro hb
    have hmem := (branch_rootedSection_iff S x).mp hb
    exact Set.disjoint_left.mp hd hx (hS ▸ hmem)
  obtain ⟨α, hα, hm, hsub⟩ := analytic_subset_borel_rank_layer S hA₀ hw
  refine ⟨ε, S, hS.symm, α, hα, hm, hsub, ?_⟩
  rintro x ⟨hx, _⟩ hmem
  have hb := (branch_rootedSection_iff S x).mpr (hS ▸ hmem)
  exact (prefixTreeWellFounded_iff _ (rootedSection S x).downward).mpr hx hb

/-- The boldface separator and its stronger effective rank-code form. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{statement*}[Effective Lusin separation from ranks] If $A_0,A_1\IncludedIn\BaireSpace$ are disjoint analytic
    sets, then there is a Borel set $B$ with
    $$
    A_0\IncludedIn B\IncludedIn \SetDifference{\BaireSpace}{A_1}.
    $$
    Moreover, if both sets have pair-tree presentations decidable relative to a real parameter $a$, one can take
    $B$ to be a tree-rank layer at an ordinal with an $a$-recursive well-order presentation. The labels of a Borel
    code for this same $B$ are computable relative to $a$, so in particular $B$ is hyperarithmetic in $a$.
    
    \end{statement*}
-/
theorem lusin_rank_separation {A₀ A₁ : Set (ℕ → ℕ)}
    (hA₀ : AnalyticSet A₀) (hA₁ : AnalyticSet A₁) (hd : Disjoint A₀ A₁) :
    (∃ B, MeasurableSet B ∧ A₀ ⊆ B ∧ B ⊆ A₁ᶜ) ∧
    (∀ ε, Projected ε A₀ → Projected ε A₁ →
      ∃ (S : PairTree ε) (α : Ordinal), pairTreeProjection S.tree = A₁ ∧
        LambdaRelative.RecursiveOrdinal ε α ∧ HasRecursiveBorelCode ε (sectionRankLayer S α) ∧
        A₀ ⊆ sectionRankLayer S α ∧ sectionRankLayer S α ⊆ A₁ᶜ) := by
  constructor
  · obtain ⟨ε, S, _, α, _, hm, hleft, hright⟩ := analytic_lusin_rank_separator hA₀ hA₁ hd
    exact ⟨sectionRankLayer S α, hm, hleft, hright⟩
  · intro ε h₀ h₁
    obtain ⟨T, rfl⟩ := h₀
    obtain ⟨S, rfl⟩ := h₁
    obtain ⟨α, hα, hc, hleft, hright⟩ := recursive_lusin_rank_separator T S hd
    exact ⟨S, α, rfl, hα, hc, hleft, hright⟩

end LambdaTree
end PolishSpaceBook
