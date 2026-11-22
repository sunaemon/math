module

public import PolishSpaceBook.LambdaListPrefixes
public import PolishSpaceBook.LambdaRelativeProducts
public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies

@[expose] public section

/-! # Recursive prefix trees using lambda decision programs

List codes are exactly the paired-successor codes used by the lambda library.
The stage-cutoff decider implements the finite test in the book, with no
recursive-program backend. Relative trees retain one fixed real parameter.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm

/-- The book's explicit list code, supplied locally instead of changing the
ambient mathlib encoding of lists. -/
@[reducible] def NamedLambda.NatListCode.encodable : Encodable (List ℕ) where
  encode := NatListCode.encode
  decode n := some (NatListCode.decode n)
  encodek xs := by simp

namespace LambdaTree
local instance : Encodable (List ℕ) := NatListCode.encodable

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The basic coding object is a \termdefine{recursive tree}: a tree $T\IncludedIn\finseq{\omega}$ whose membership relation
    on finite sequences is decidable by a program.
-/
structure PrefixTree (ε : ℕ → ℕ) where
  tree : Set (List ℕ)
  downward : IsSubtree tree
  decidable : LambdaRelative.DecidablePredicate ε (· ∈ tree)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    With a real parameter fixed, recursive trees form a countable family: send each tree to its decidable membership
    predicate and apply §{sec:edst-relative-programs}. The preceding numerical decider also works relative to any
    parameter, since it makes no queries to that parameter.
-/
instance countablePrefixTree (ε : ℕ → ℕ) : Countable (PrefixTree ε) := by
  let := LambdaRelative.countable_decidablePredicates (List ℕ) ε
  apply Function.Injective.countable
    (f := fun T : PrefixTree ε =>
      (⟨(· ∈ T.tree),T.decidable⟩ : {R : List ℕ → Prop // LambdaRelative.DecidablePredicate ε R}))
  intro ⟨T,hT,hcT⟩ ⟨S,hS,hcS⟩ h
  have heq : T = S := congrArg Subtype.val h
  cases heq
  rfl

/-- A trial returns one precisely when the forbidden word is not a prefix. -/
def cutoffTrial (F : AlphaTerm) := numericalCompose reverseZeroTerm
  (numericalCompose listPrefixTerm
    (pairNumerical (numericalCompose F (numericalProjectionTerm false)) (numericalProjectionTerm true)))

def cutoffTrialValue (f : ℕ → List ℕ) (z : ℕ) : ℕ :=
  if (f z.unpair.2).IsPrefix (NatListCode.decode z.unpair.1) then 0 else 1

theorem cutoffTrial_computes {F : AlphaTerm} {f : ℕ → List ℕ}
    (hF : NumericalComputes F (fun n => NatListCode.encode (f n))) :
    NumericalComputes (cutoffTrial F) (cutoffTrialValue f) := by
  have h := reverseZero_computes.comp (listPrefix_computes.comp
    ((hF.comp (projection_computes false)).pair (projection_computes true)))
  unfold cutoffTrial cutoffTrialValue
  convert h using 1
  funext z
  simp only [Nat.unpair_pair,NatListCode.decode_encode,Bool.false_eq_true,ite_false,ite_true]
  split_ifs <;> simp_all


/-- Test exactly the first length-plus-one forbidden words. -/
def cutoffProgram (F : AlphaTerm) := numericalCompose (boundedProductTerm (cutoffTrial F))
  (pairNumerical numericalIdentity (numericalCompose successorTerm listLengthTerm))

local instance cutoffMembershipDecidable (f : ℕ → List ℕ) (xs : List ℕ) :
    Decidable (xs ∈ stageCutoffTree f) :=
  inferInstanceAs (Decidable (∀ i ≤ xs.length, ¬ (f i).IsPrefix xs))

theorem cutoffProduct_value (f : ℕ → List ℕ) (e : ℕ) :
    boundedProduct (cutoffTrialValue f) e ((NatListCode.decode e).length+1) =
      if NatListCode.decode e ∈ stageCutoffTree f then 1 else 0 := by
  have hz := boundedProduct_zero_or_one (cutoffTrialValue f) e ((NatListCode.decode e).length+1)
    (fun i => by simp only [cutoffTrialValue,Nat.unpair_pair]; split_ifs <;> simp)
  have hn : boundedProduct (cutoffTrialValue f) e ((NatListCode.decode e).length+1) ≠ 0 ↔
      NatListCode.decode e ∈ stageCutoffTree f := by
    rw [boundedProduct_ne_zero]
    simp [cutoffTrialValue,stageCutoffTree]
  split_ifs with h
  · exact hz.resolve_left (hn.mpr h)
  · exact not_not.mp (fun hne => h (hn.mp hne))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Lambda decision of the stage-cutoff tree
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    On the code of $t$, compute $|t|$. For each $i\le|t|$, compute the code of $s_i$ and test whether $s_i$ is a prefix
    of $t$. This test compares the code of $s_i$ with the code of the first $|s_i|$ entries of $t$; if $s_i$ is longer
    than $t$, the codes differ. Prefix extraction and numerical equality are computed by closed terms in
    §{sec:lambda-prefix-margin-programs}. Let $a_i$ be zero when the prefix test succeeds and one otherwise. Starting
    with $b_0=1$, use numerical primitive recursion to compute $b_{i+1}=b_i a_i$ through stage $|t|+1$. Every test
    terminates, so the bounded recursion terminates. The output is one exactly when none of the forbidden words
    with index at most $|t|$ is a prefix of $t$, which is exactly membership in the stage-cutoff tree. It is zero
    otherwise. Pairing, composition, and the recursor combine these operations into one closed term. The tree and
    body assertions are those of the preceding lemma.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Finally, let a closed term $F$ compute the code of a forbidden word $s_i$ from $i$. On input $\NatPair{e}{i}$,
    a closed term $T_F$ computes the prefix-test answer for $s_i$ and $\LambdaListDecode{e}$ and reverses zero and one.
    Explicitly, expand the abbreviations
    $$\begin{aligned}
    i&:=\LambdaNumericProjection{2}z,\qquad e:=\LambdaNumericProjection{1}z,\\
    D_F(z)&:=\LambdaListPrefix\,(\LambdaNumericPair\,(Fi)\,e),\\
    T_F&:=\lambdaab{z}{\LambdaZeroTest\,(D_F(z))\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The tree decider is the closed term
    $$C_F:=\lambdaab{e}{\LambdaBoundedProduct{T_F}\,
     \bigl(\LambdaNumericPair\,e\,(\LambdaSucc(\LambdaListLength\,e))\bigr)}.$$
    The bounded-product lemma shows that $C_F$ terminates and returns one exactly when none of the first
    $|\LambdaListDecode{e}|+1$ forbidden words is a prefix of the decoded list. Its other output is zero.
    Thus it decides precisely the stage-cutoff tree in §{sec:edst-recursive-trees}. Lifting this ordinary numerical
    term to ignore an input-name argument gives the same decider relative to any fixed real parameter.
-/
theorem cutoffProgram_computes {F : AlphaTerm} {f : ℕ → List ℕ}
    (hF : NumericalComputes F (fun n => NatListCode.encode (f n))) :
    NumericalComputes (cutoffProgram F)
      (fun e => if NatListCode.decode e ∈ stageCutoffTree f then 1 else 0) := by
  have h := (boundedProduct_computes (cutoffTrial_computes hF)).comp
    (numericalIdentity_computes.pair (successor_computes.comp listLength_computes))
  simpa only [cutoffProgram,Nat.unpair_pair,id_eq,Nat.succ_eq_add_one,cutoffProduct_value] using h

/-- A computable forbidden-word enumeration yields a tree with a lambda decider. -/
def stageCutoff (ε : ℕ → ℕ) (f : ℕ → List ℕ) (F : AlphaTerm)
    (hF : NumericalComputes F (fun n => NatListCode.encode (f n))) : PrefixTree ε where
  tree := stageCutoffTree f
  downward := stageCutoffTree_isSubtree f
  decidable := by
    let h := (cutoffProgram_computes hF).uniform
    refine ⟨liftNumericalProgram (cutoffProgram F),h.1,fun xs => ⟨?_,?_⟩⟩
    · intro hx
      change OracleRuns ε _ (NatListCode.encode xs) 1
      simpa only [NatListCode.decode_encode,ite_eq_left hx] using h.2 ε (NatListCode.encode xs)
    · intro hx
      change OracleRuns ε _ (NatListCode.encode xs) 0
      simpa only [NatListCode.decode_encode,ite_eq_right hx] using h.2 ε (NatListCode.encode xs)

theorem stageCutoff_body (ε : ℕ → ℕ) (f : ℕ → List ℕ) (F : AlphaTerm)
    (hF : NumericalComputes F (fun n => NatListCode.encode (f n))) :
    treeBody (stageCutoff ε f F hF).tree = (⋃ i, cyl (f i))ᶜ :=
  treeBody_stageCutoffTree f

/-- Relative trials pass the same parameter to the forbidden-word enumerator. -/
def relativeCutoffTrial (F : AlphaTerm) : AlphaTerm :=
  mapOutputProgram reverseZeroTerm (mapOutputProgram listPrefixTerm
    (pairOutputProgram (reindexProgram F (numericalProjectionTerm false))
      (liftNumericalProgram (numericalProjectionTerm true))))

theorem relativeCutoffTrial_computes {ε : ℕ → ℕ} {F : AlphaTerm} {f : ℕ → List ℕ}
    (hF : LambdaRelative.Computes ε F (fun n => NatListCode.encode (f n))) :
    LambdaRelative.Computes ε (relativeCutoffTrial F) (cutoffTrialValue f) := by
  have h := (((hF.reindex (projection_computes false)).pair
    (LambdaRelative.ofNumerical (projection_computes true) ε)).map listPrefix_computes).map reverseZero_computes
  unfold relativeCutoffTrial cutoffTrialValue
  convert h using 1
  funext z
  simp only [Nat.unpair_pair,NatListCode.decode_encode,Bool.false_eq_true,ite_false,ite_true]
  split_ifs <;> simp_all

/-- The length bound is numerical; each of its trials may query the parameter. -/
def relativeCutoffProgram (F : AlphaTerm) : AlphaTerm :=
  reindexProgram (relativeProductProgram (relativeCutoffTrial F))
    (pairNumerical numericalIdentity (numericalCompose successorTerm listLengthTerm))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Relative decision of the stage-cutoff tree
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Use the preceding prefix test, passing the same input variable to the enumeration program at every stage.
    For a word $t$, exactly $|t|+1$ tests are required. Each terminates with the fixed parameter, and the
    input-query recursor multiplies their zero/one answers. The construction in §{sec:lambda-prefix-margin-programs}
    proves this finite recursion directly by beta/query reduction and gives a closed program, uniformly in the
    code of $t$. The output is one precisely when no forbidden word with index at most $|t|$ is a prefix of $t$.
    The stage-cutoff identity supplies downward closure and the asserted body.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    To apply this to trees, let $F$, with parameter $\varepsilon$, compute the code of $s_i$ on input $i$.
    Replace the ordinary trial above by
    $$\begin{aligned}
    i(z)&:=\LambdaNumericProjection{2}z,\qquad e(z):=\LambdaNumericProjection{1}z,\\
    D_F(o,z)&:=\LambdaListPrefix\,(\LambdaNumericPair\,(Fo\,i(z))\,e(z)),\\
    T_F&:=\lambdaab{o}{\lambdaab{z}{
     \LambdaZeroTest\,(D_F(o,z))\,\ChurchNumeral{1}\,\ChurchNumeral{0}}},\\
    C_F&:=\lambdaab{o}{\lambdaab{e}{\LambdaRelativeProduct{T_F}\,o\,
     \bigl(\LambdaNumericPair\,e\,(\LambdaSucc(\LambdaListLength\,e))\bigr)}}.
    \end{aligned}$$
    As before, expand the abbreviations inside the abstractions. At a decoded list $t$, the bounded-product lemma
    applies to exactly $|t|+1$ reversed prefix tests. It proves that $C_F$ is the relative decider asserted in
    §{sec:edst-recursive-trees}. Termination of $F$ for every index with this fixed parameter suffices.
-/
theorem relativeCutoffProgram_computes {ε : ℕ → ℕ} {F : AlphaTerm} {f : ℕ → List ℕ}
    (hF : LambdaRelative.Computes ε F (fun n => NatListCode.encode (f n))) :
    LambdaRelative.Computes ε (relativeCutoffProgram F)
      (fun e : ℕ => if NatListCode.decode e ∈ stageCutoffTree f then 1 else 0) := by
  have h := (relativeCutoffTrial_computes hF).boundedProduct.reindex
    (numericalIdentity_computes.pair (successor_computes.comp listLength_computes))
  simpa only [relativeCutoffProgram,Nat.unpair_pair,id_eq,Nat.succ_eq_add_one,cutoffProduct_value] using h

/-- No termination assumption is made for any parameter other than ε. -/
def relativeStageCutoff (ε : ℕ → ℕ) (f : ℕ → List ℕ) (F : AlphaTerm)
    (hF : LambdaRelative.Computes ε F (fun n => NatListCode.encode (f n))) : PrefixTree ε where
  tree := stageCutoffTree f
  downward := stageCutoffTree_isSubtree f
  decidable := by
    let h := relativeCutoffProgram_computes hF
    refine ⟨relativeCutoffProgram F,h.1,fun xs => ⟨?_,?_⟩⟩
    · intro hx
      change OracleRuns ε _ (NatListCode.encode xs) 1
      simpa only [Encodable.encode_nat,NatListCode.decode_encode,ite_eq_left hx] using h.2 (NatListCode.encode xs)
    · intro hx
      change OracleRuns ε _ (NatListCode.encode xs) 0
      simpa only [Encodable.encode_nat,NatListCode.decode_encode,ite_eq_right hx] using h.2 (NatListCode.encode xs)

theorem relativeStageCutoff_body (ε : ℕ → ℕ) (f : ℕ → List ℕ) (F : AlphaTerm)
    (hF : LambdaRelative.Computes ε F (fun n => NatListCode.encode (f n))) :
    treeBody (relativeStageCutoff ε f F hF).tree = (⋃ i, cyl (f i))ᶜ :=
  treeBody_stageCutoffTree f

end LambdaTree

/-- Ordinary recursive trees use the computable constant-zero input name. -/
abbrev RecursivePrefixTree := LambdaTree.PrefixTree (fun _ => 0)

end PolishSpaceBook
