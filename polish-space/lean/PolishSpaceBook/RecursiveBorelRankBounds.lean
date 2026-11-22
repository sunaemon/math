module

public import PolishSpaceBook.LambdaBorelCodeCompleteness
public import PolishSpaceBook.BorelExpressionCodeComparison
public import PolishSpaceBook.BorelExpressionValidity
public import PolishSpaceBook.LambdaKleeneBrouwer
public import PolishSpaceBook.WellFoundedRankMaps

@[expose] public section

/-! # Recursive ordinal bounds for the actual present tree of a Borel expression

The label program decides presence of a node. Validity supplies prefix closure
and excludes branches. The same fixed parameter is retained by the node test.
Kleene--Brouwer bounds the whole tree by one recursive ordinal; comparison of
the actual child relation with strict extension bounds the Borel-code ranks.
-/

noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm BorelExpression

local instance recursiveBorelRankWordEncoding : Encodable (List ℕ) := NatListCode.encodable

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A well-founded countable Borel-code tree has rank below $\omegaOneOrd$; if the tree is recursive, its rank is
    below $\churchKleeneOrd$. The latter follows by bounding its rank with its recursive Kleene--Brouwer well-order.
-/
theorem countable_borel_code_rank (c : Code) :
    (⨆ s : {s : List ℕ // c.val s ≠ 0}, (c.property.2.2.2.2.2.apply s.val).rank) <
      (Ordinal.omega 1 : Ordinal.{0}) :=
  c.val.all_accessibility_ranks_lt_omega_one c.property

theorem recursiveBorel_present_decidable {ε : ℕ → ℕ} (c : Code) {P : AlphaTerm}
    (hP : LambdaRelative.Computes ε P c.val) :
    LambdaRelative.DecidablePredicate ε (fun s : List ℕ => c.val s ≠ 0) := by
  have hz : LambdaRelative.DecidablePredicate ε (fun s : List ℕ => c.val s = 0) := by
    refine ⟨mapOutputProgram reverseZeroTerm P, mapOutputProgram_closed reverseZero_computes.1 hP.1,
      fun s => ?_⟩
    have hr := mapOutputProgram_runs reverseZero_computes.1 hP.1 (hP.2 s)
      (reverseZero_computes.2 (c.val s))
    constructor <;> intro hs <;> simpa only [hs, ite_true, ite_false] using hr
  exact hz.not

def recursiveBorelPrefixTree {ε : ℕ → ℕ} (c : Code) {P : AlphaTerm}
    (hP : LambdaRelative.Computes ε P c.val) : LambdaTree.PrefixTree ε where
  tree := {s | c.val s ≠ 0}
  downward := fun _ _ ht hst => ((valid_iff_syntax_wellFounded c.val).mp c.property).1.present_prefix ht hst
  decidable := recursiveBorel_present_decidable c hP

theorem recursiveBorelPrefixTree_no_branch {ε : ℕ → ℕ} (c : Code) {P : AlphaTerm}
    (hP : LambdaRelative.Computes ε P c.val) :
    PrefixTreeWellFounded (recursiveBorelPrefixTree c hP).tree := by
  have hs := ((valid_iff_syntax_wellFounded c.val).mp c.property).1
  have hn := hs.wellFounded_iff_no_branch.mp c.property.2.2.2.2.2
  rintro ⟨p, hp⟩
  obtain ⟨n, hn⟩ := hn p
  exact hp n hn

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The well-founded trees of these codes have ranks below $\churchKleeneOrd$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A well-founded countable Borel-code tree has rank below $\omegaOneOrd$; if the tree is recursive, its rank is
    below $\churchKleeneOrd$. The latter follows by bounding its rank with its recursive Kleene--Brouwer well-order.
-/
theorem recursiveBorel_code_rank_lt_bound {ε : ℕ → ℕ} (c : Code) {P : AlphaTerm}
    (hP : LambdaRelative.Computes ε P c.val) :
    (⨆ s : {s : List ℕ // c.val s ≠ 0}, (c.property.2.2.2.2.2.apply s.val).rank) <
      LambdaRelative.recursiveOrdinalBound ε := by
  let T := recursiveBorelPrefixTree c hP
  have hwT := (prefixTreeWellFounded_iff T.tree T.downward).mp (recursiveBorelPrefixTree_no_branch c hP)
  obtain ⟨W, hW, hbound⟩ := KleeneBrouwer.recursive_bound_of_no_branch T
    (recursiveBorelPrefixTree_no_branch c hP)
  let f (s : List ℕ) : T.tree := if hs : c.val s ≠ 0 then ⟨s, hs⟩ else ⟨[], c.property.1⟩
  have hf : ∀ ⦃s t⦄, c.val.Child s t → strictTreeExtension T.tree (f s) (f t) := by
    intro s t h
    obtain ⟨ht, k, rfl, hs⟩ := h
    change (f t).val.IsPrefix (f (t ++ [k])).val ∧ (f t).val.length < (f (t ++ [k])).val.length
    simp only [f, dite_eq_left ht, dite_eq_left hs]
    exact ⟨List.prefix_append _ _, by simp⟩
  let : WellFounded c.val.Child := c.property.2.2.2.2.2
  let : WellFounded (strictTreeExtension T.tree) := hwT
  apply lt_of_le_of_lt (Ordinal.iSup_le _) hW
  intro s
  have hr := wellFoundedRank_le_of_relation_preserving f hf s.val
  obtain ⟨hs, hb⟩ := hbound (f s.val)
  exact hr.trans hb.le

end PolishSpaceBook
