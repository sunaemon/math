module

public import PolishSpaceBook.LambdaKleeneBrouwer
public import PolishSpaceBook.LambdaFiniteCheckTrees
public import PolishSpaceBook.LambdaTreeMapPrograms
public import Mathlib.Data.List.Chain

@[expose] public section

/-! # Recursive trees of certified descending chains

An entry pairs the next element with a certificate for its edge to the
previous element. The certificates make membership decidable even when
the underlying relation is only computably enumerable.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace CertifiedDescent
set_option maxHeartbeats 800000
local instance : Encodable (List ℕ) := NatListCode.encodable

variable (C : ℕ → Prop)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A finite certificate lets us decide a tree of descending chains even when the underlying relation is not decidable.
    Let $\prec$ be a relation on $\NN$, and let a closed numerical term $\LambdaTermName{cert}$ decide a
    predicate $\mathcal C(p,h)$ with
    $$b\prec p\quad\Longleftrightarrow\quad\exists c\;\mathcal C(p,\NatPair{b}{c}).$$
    For a starting number $a$, define $T_a$ to consist of the words whose entries are next-element/certificate pairs
    and whose successive certificates are accepted, starting at $a$. The empty word belongs to $T_a$.
    The preceding number for the first entry is $a$; for every later entry it is the first projection of the previous entry.
-/
def nodes (a : ℕ) : Set (List ℕ) :=
  {s | List.IsChain (fun x y => C (Nat.pair x.unpair.1 y)) (Nat.pair a 0 :: s)}

theorem root_mem (a : ℕ) : [] ∈ nodes C a := by simp [nodes]

theorem downward (a : ℕ) : IsSubtree (nodes C a) := by
  intro s t ht hst
  obtain ⟨u,rfl⟩ := hst
  exact ht.prefix ⟨u,rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A finite certificate lets us decide a tree of descending chains even when the underlying relation is not decidable.
    Let $\prec$ be a relation on $\NN$, and let a closed numerical term $\LambdaTermName{cert}$ decide a
    predicate $\mathcal C(p,h)$ with
    $$b\prec p\quad\Longleftrightarrow\quad\exists c\;\mathcal C(p,\NatPair{b}{c}).$$
    For a starting number $a$, define $T_a$ to consist of the words whose entries are next-element/certificate pairs
    and whose successive certificates are accepted, starting at $a$. The empty word belongs to $T_a$.
    The preceding number for the first entry is $a$; for every later entry it is the first projection of the previous entry.
-/
theorem nodes_iff (a : ℕ) (s : List ℕ) : s ∈ nodes C a ↔
    ∀ i < s.length, C (Nat.pair ((Nat.pair a 0 :: s).getD i 0).unpair.1 (s.getD i 0)) := by
  simp only [nodes,Set.mem_ofPred_eq,List.isChain_iff_getElem,List.length_cons,
    Nat.add_lt_add_iff_right,List.getElem_cons_succ]
  constructor <;> intro h i hi
  · have hi' : i < (Nat.pair a 0 :: s).length := by simp only [List.length_cons]; omega
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi',Option.getD_some] using h i hi
  · have hi' : i < (Nat.pair a 0 :: s).length := by simp only [List.length_cons]; omega
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi',Option.getD_some] using h i hi

/-- The list-cons code is computed before the bounded trials begin. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For $i=1,2$, write $\NatProjection{i}{z}$ for the natural-number projections determined by
    $$\NatProjection{1}{\NatPair{a}{b}}=a,\qquad \NatProjection{2}{\NatPair{a}{b}}=b.$$
    The closed lambda term $\LambdaNumericProjection{i}$ computes this projection on $\ChurchNumeral{z}$.
    On a trial input $v=\NatPair{e}{i}$, where $e$ is a word code, expand
    $$\begin{aligned}
     \LambdaTermName{seed}_{a}(e)&:=\LambdaListCons\,\ChurchNumeral{\NatPair{a}{0}}\,e,\\
    \LambdaTermName{entry}(v)&:= \LambdaListGet\,( \LambdaNumericPair\,( \LambdaNumericProjection{1}v)\,(
    \LambdaNumericProjection{2}v)),\\
    \LambdaTermName{prev}_{a}(v)&:= \LambdaNumericProjection{1} \bigl( \LambdaListGet\,( \LambdaNumericPair\,
    \LambdaTermName{seed}_{a}( \LambdaNumericProjection{1}v)\,( \LambdaNumericProjection{2}v)) \bigr),\\
    \LambdaTermName{trial}_{a}&:= \lambdaab{v}{ \LambdaTermName{cert}( \LambdaNumericPair\,
    \LambdaTermName{prev}_{a}(v)\, \LambdaTermName{entry}(v))},\\
     \LambdaTermName{desc}_{a}&:=\lambdaab{e}{\LambdaBoundedProduct{\LambdaTermName{trial}_{a}}
       (\LambdaNumericPair\,e\,(\LambdaListLength\,e))}.
    \end{aligned}$$
    All abbreviations are expanded before abstraction, with fresh binders. Prepending the dummy entry
    $\NatPair{a}{0}$ makes the previous element available at the same position as the current entry in the original word.
    The dummy certificate is never tested.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A finite certificate lets us decide a tree of descending chains even when the underlying relation is not decidable.
    Let $\prec$ be a relation on $\NN$, and let a closed numerical term $\LambdaTermName{cert}$ decide a
    predicate $\mathcal C(p,h)$ with
    $$b\prec p\quad\Longleftrightarrow\quad\exists c\;\mathcal C(p,\NatPair{b}{c}).$$
    For a starting number $a$, define $T_a$ to consist of the words whose entries are next-element/certificate pairs
    and whose successive certificates are accepted, starting at $a$. The empty word belongs to $T_a$.
    The preceding number for the first entry is $a$; for every later entry it is the first projection of the previous entry.
-/
theorem nodes_decidable {ε : ℕ → ℕ} (hC : LambdaRelative.DecidablePredicate ε C) (a : ℕ) :
    LambdaRelative.DecidablePredicate ε (· ∈ nodes C a) := by
  have hz := projection_computes true
  have hi := projection_computes false
  have hcons := successor_computes.comp ((numericalConstant_computes (Nat.pair a 0)).pair hz)
  have hp := (projection_computes true).comp (listGet_computes.comp (hcons.pair hi))
  have hc := listGet_computes.comp (hz.pair hi)
  let f := fun z : ℕ => Nat.pair
    ((NatListCode.decode (Nat.pair (Nat.pair a 0) z.unpair.1 + 1)).getD z.unpair.2 0).unpair.1
    ((NatListCode.decode z.unpair.1).getD z.unpair.2 0)
  have hpair := hp.pair hc
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.succ_eq_add_one,Nat.unpair_pair] at hpair
  change NumericalComputes _ f at hpair
  have ht := hC.precompNumerical (g := f) hpair (fun _ => rfl)
  have hall := ht.boundedAll listLength_computes
  have hs := hall.precompNumerical (g := NatListCode.encode) numericalIdentity_computes (fun _ => rfl)
  have hd (n : ℕ) : NatListCode.decode (Nat.pair (Nat.pair a 0) n + 1) =
      Nat.pair a 0 :: NatListCode.decode n := by
    simpa only [NatListCode.encode,NatListCode.encode_decode] using
      NatListCode.decode_encode (Nat.pair a 0 :: NatListCode.decode n)
  have hfinal : LambdaRelative.DecidablePredicate ε (fun s : List ℕ =>
      ∀ i < s.length, C (Nat.pair ((Nat.pair a 0 :: s).getD i 0).unpair.1 (s.getD i 0))) := by
    simpa only [f,Encodable.encode_nat,Bool.false_eq_true,ite_true,ite_false,Nat.succ_eq_add_one,hd,
      Nat.unpair_pair,NatListCode.decode_encode] using hs
  have heq : (fun s => s ∈ nodes C a) = (fun s : List ℕ =>
      ∀ i < s.length, C (Nat.pair ((Nat.pair a 0 :: s).getD i 0).unpair.1 (s.getD i 0))) :=
    funext (fun s => propext (nodes_iff C a s))
  rw [heq]
  exact hfinal

noncomputable def tree {ε : ℕ → ℕ} (hC : LambdaRelative.DecidablePredicate ε C) (a : ℕ) :
    LambdaTree.PrefixTree ε where
  tree := nodes C a
  downward := downward C a
  decidable := by
    have h := nodes_decidable C hC a
    exact h

def endpoint (a : ℕ) (s : List ℕ) : ℕ :=
  ((Nat.pair a 0 :: s).getLast (by simp)).unpair.1

@[simp] theorem endpoint_nil (a : ℕ) : endpoint a [] = a := by simp [endpoint]
@[simp] theorem endpoint_append (a : ℕ) (s : List ℕ) (x : ℕ) :
    endpoint a (s ++ [x]) = x.unpair.1 := by
  simp only [endpoint,← List.cons_append,List.getLast_append_singleton]

theorem append_mem {a : ℕ} {s : List ℕ} (hs : s ∈ nodes C a) {x : ℕ}
    (hx : C (Nat.pair (endpoint a s) x)) : s ++ [x] ∈ nodes C a := by
  change List.IsChain _ (Nat.pair a 0 :: (s ++ [x]))
  rw [← List.cons_append,List.isChain_append]
  refine ⟨hs,by simp,?_⟩
  intro y hy z hz
  simp only [List.head?_cons,Option.mem_some_iff] at hz
  subst z
  have hy' : y = (Nat.pair a 0 :: s).getLast (by simp) := by
    simpa only [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil (Nat.pair a 0) s),Option.mem_some_iff,eq_comm] using hy
  simpa [hy',endpoint] using hx

variable {r : ℕ → ℕ → Prop}

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    List construction, lookup, and projections compute precisely the arguments expected by $\LambdaTermName{cert}$.
    The bounded product
    runs one trial per entry and returns one exactly when all certificates are accepted; on the empty word it is one.
    Every trial terminates. The same tests apply to any prefix, giving closure under prefixes. An infinite branch would
    project to an infinite $\prec$-descending chain beginning at $a$, contradicting the hypothesis.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Fix $a\in\KleeneO$. Let $T_a$ contain the empty word and all finite words
    $$s=(\NatPair{b_0}{c_0},\ldots,\NatPair{b_{k-1}}{c_{k-1}})$$
    whose certificates verify the successive steps starting at $a$: when $k>0$, require
    $C(a,\NatPair{b_0}{c_0})$, and require $C(b_i,\NatPair{b_{i+1}}{c_{i+1}})$ for every $i+1<k$.
    These finitely many tests decide membership, and every prefix passes the same earlier tests. An infinite branch
    would give an infinite candidate descent starting at $a$, contrary to well-foundedness below a valid notation.
    Thus $T_a$ is a recursive well-founded tree.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    §{sec:lambda-certified-descent} gives the finite certificate test and the joint domain
    program. It tests only finitely many certificates on each input, even when the starting number
    is not a valid notation. Validity is used to prove that the descent tree is well founded, not to
    run its domain test. The empty word always belongs to the tree and has code zero.
-/
theorem wellFounded (hsound : ∀ p x, C (Nat.pair p x) → r x.unpair.1 p)
    {a : ℕ} (ha : Acc r a) : WellFounded (strictTreeExtension (nodes C a)) := by
  apply (prefixTreeWellFounded_iff _ (downward C a)).mp
  rintro ⟨f,hf⟩
  let g : ℕ → ℕ := fun n => if n = 0 then a else (f (n-1)).unpair.1
  apply (not_acc_iff_exists_descending_chain.mpr ⟨g,by simp [g],?_⟩) ha
  intro n
  have h := (nodes_iff C a (seqPrefix f (n+1))).mp (hf (n+1)) n (by simp [seqPrefix_length])
  cases n with
  | zero =>
    simpa [g,seqPrefix,List.getD_eq_getElem?_getD] using hsound a (f 0) (by simpa [seqPrefix,List.getD_eq_getElem?_getD] using h)
  | succ n =>
    have get (i k : ℕ) (hi : i < k) : (seqPrefix f k).getD i 0 = f i := by
      simp only [seqPrefix,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]
    change C (Nat.pair ((seqPrefix f (n+1+1)).getD n 0).unpair.1
      ((seqPrefix f (n+1+1)).getD (n+1) 0)) at h
    have hc : C (Nat.pair (f n).unpair.1 (f (n+1))) := by
      simpa only [get n (n+1+1) (by omega),get (n+1) (n+1+1) (by omega)] using h
    simpa [g] using hsound (f n).unpair.1 (f (n+1)) hc

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    At a node ending at $b$, every $\prec$-predecessor $d$ has some certificate, so the node has a child ending at $d$.
    Well-founded induction below the starting number bounds the rank of $b$ by that node's strict-extension rank.
    Apply the induction hypothesis at each such child, take successors, and then take their supremum.
    This proves the root comparison.
    The Kleene--Brouwer construction of §{sec:lambda-kleene-brouwer} gives the strict recursive upper bound.
    For the relative assertion, replace the bounded product by its input-query version and pass the same parameter
    to $\LambdaTermName{cert}$ in every trial. The tree and rank arguments are unchanged. This proof does not
    assert a computable choice
    of certificates from true edges.
    \end{proof}
-/
theorem rank_le (hcomplete : ∀ p b, r b p → ∃ c, C (Nat.pair p (Nat.pair b c)))
    {a : ℕ} (hw : WellFounded (strictTreeExtension (nodes C a)))
    {b : ℕ} (hb : Acc r b) :
    ∀ s : nodes C a, endpoint a s.val = b → hb.rank ≤ (hw.apply s).rank := by
  induction hb with
  | intro b hb ih =>
    intro s he
    rw [Acc.rank_eq]
    apply Ordinal.iSup_le
    intro v
    obtain ⟨c,hc⟩ := hcomplete b v.val v.property
    let t : nodes C a := ⟨s.val ++ [Nat.pair v.val c],append_mem C s.property (by simpa [he] using hc)⟩
    have ht : endpoint a t.val = v.val := by simp [t]
    have hst : strictTreeExtension (nodes C a) t s :=
      ⟨List.prefix_append _ _,by simp [t]⟩
    exact Order.succ_le_of_lt ((ih v.val v.property t ht).trans_lt ((hw.apply s).rank_lt_of_rel hst))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Certified descent tree
-/
theorem recursive_bound {ε : ℕ → ℕ} (hC : LambdaRelative.DecidablePredicate ε C)
    (hsound : ∀ p x, C (Nat.pair p x) → r x.unpair.1 p)
    (hcomplete : ∀ p b, r b p → ∃ c, C (Nat.pair p (Nat.pair b c)))
    {a : ℕ} (ha : Acc r a) :
    ∃ W : LambdaRelative.WellOrderPresentation ε, ha.rank < W.orderType := by
  let T := tree C hC a
  have hw := wellFounded C hsound ha
  let root : nodes C a := ⟨[],root_mem C a⟩
  refine ⟨KleeneBrouwer.presentation T hw,?_⟩
  exact (rank_le C hcomplete hw ha root (endpoint_nil a)).trans_lt
    (KleeneBrouwer.rank_lt_presentation T hw root)

end CertifiedDescent
end PolishSpaceBook
