module

public import PolishSpaceBook.EffectiveClosedTreeRepresentation
public import PolishSpaceBook.LambdaFiniteCheckTrees
public import PolishSpaceBook.LambdaPureParameters
public import PolishSpaceBook.LambdaTreeMapPrograms

@[expose] public section

/-! # Computable points, singleton prefix trees and topological closure

Every finite word has a concrete zero-padded lambda-computable extension.
For a computed point, a bounded product of comparisons decides its finite
prefix tree. Countability uses syntax and uniqueness of numerical outputs;
it does not decide totality of an index.
-/

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm

local instance computablePointWordEncoding : Encodable (List ℕ) := NatListCode.encodable

def computableBairePoints : Set (ℕ → ℕ) := {p | ∃ P : AlphaTerm, NumericalComputes P p}

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem mem_computableBairePoints_iff_zero_relative (p : ℕ → ℕ) :
    p ∈ computableBairePoints ↔ LambdaRelative.Computable (fun _ => 0) p := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨_, LambdaRelative.ofNumerical hP _⟩
  · rintro ⟨P, hP⟩
    exact ⟨_, hP.toNumerical (numericalConstant_computes 0)⟩

def paddedWordProgram (s : List ℕ) : AlphaTerm :=
  numericalCompose listGetTerm (pairNumerical (numericalConstant (NatListCode.encode s)) numericalIdentity)

theorem paddedWordProgram_computes (s : List ℕ) :
    NumericalComputes (paddedWordProgram s) (fun n => s.getD n 0) := by
  simpa only [paddedWordProgram, Nat.unpair_pair, NatListCode.decode_encode, id_eq] using
    listGet_computes.comp ((numericalConstant_computes (NatListCode.encode s)).pair numericalIdentity_computes)

theorem paddedWord_mem_cyl (s : List ℕ) : (fun n => s.getD n 0) ∈ cyl s := by
  intro i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem computableBairePoints_countable : computableBairePoints.Countable := by
  have hc := LambdaRelative.countable_computable ℕ ℕ (fun _ => 0)
  let f : computableBairePoints → {p : ℕ → ℕ // LambdaRelative.Computable (fun _ => 0) p} := fun p =>
    ⟨p.val, by obtain ⟨P, hP⟩ := p.property; exact ⟨_, LambdaRelative.ofNumerical hP _⟩⟩
  have : Countable computableBairePoints := Function.Injective.countable (f := f) (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {p : ℕ → ℕ // LambdaRelative.Computable (fun _ => 0) p} => z.val) h)
  exact Set.to_countable _

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem computableBairePoints_dense : Dense computableBairePoints := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p, hp⟩
  obtain ⟨s, _, hsU⟩ := exists_cyl_subset_of_mem_open hp hU
  exact ⟨fun n => s.getD n 0, hsU (paddedWord_mem_cyl s),
    paddedWordProgram s, paddedWordProgram_computes s⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The set of total computable functions is countable but not closed; totality is a $\lPi^0_2$ condition on indices,
        not a topological closedness condition on points.
-/
theorem computableBairePoints_not_closed : ¬ IsClosed computableBairePoints := by
  intro hc
  have he : computableBairePoints = univ := hc.closure_eq.symm.trans computableBairePoints_dense.closure_eq
  have hb : Countable (ℕ → ℕ) := Set.countable_univ_iff.mp (he ▸ computableBairePoints_countable)
  have hcantor : Countable cantor_space := Function.Injective.countable
    (f := fun p : cantor_space => fun n => (p n).toNat) (by
      intro p q h
      funext n
      have hn := congrFun h n
      cases hp : p n <;> cases hq : q n <;> simp_all)
  exact cantor_space_not_countable hcantor

theorem computable_point_prefix_decidable {p : ℕ → ℕ} {P : AlphaTerm}
    (hP : NumericalComputes P p) :
    LambdaRelative.DecidablePredicate (fun _ => 0) (fun s : List ℕ => prefixOfSeq s p) := by
  have hg := listGet_computes
  have hp := hP.comp (projection_computes false)
  simp only [Bool.false_eq_true, ite_false] at hp
  have heq : LambdaRelative.DecidablePredicate (fun _ => 0)
      (fun z : ℕ => (NatListCode.decode z.unpair.1).getD z.unpair.2 0 = p z.unpair.2) := by
    convert (LambdaTree.numerical_le_decidable hg hp (fun _ => 0)).and
      (LambdaTree.numerical_le_decidable hp hg (fun _ => 0)) using 1
    funext z
    exact propext le_antisymm_iff
  have hb := heq.boundedAll listLength_computes
  have hs := hb.precompNumerical (g := fun s : List ℕ => NatListCode.encode s)
    numericalIdentity_computes (by intro s; rfl)
  have hid : (fun s : List ℕ => ∀ i < s.length, s.getD i 0 = p i) =
      (fun s => prefixOfSeq s p) := by
    funext s
    apply propext
    constructor
    · intro h i hi
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        List.get_eq_getElem] using (h i hi).symm
    · intro h i hi
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
        List.get_eq_getElem] using (h i hi).symm
  simp only [Nat.unpair_pair, NatListCode.decode_encode] at hs
  rwa [hid] at hs

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A computable point $p \in \BaireSpace$ gives a $\lPi^0_1$ singleton $\{p\}$: the recursive tree consists of the
        finite prefixes of $p$.
-/
def computableSingletonTree {p : ℕ → ℕ} {P : AlphaTerm} (hP : NumericalComputes P p) :
    LambdaTree.PrefixTree (fun _ => 0) where
  tree := {s | prefixOfSeq s p}
  downward := fun _ _ ht hst => prefixOfSeq_of_prefix hst ht
  decidable := computable_point_prefix_decidable hP

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A computable point $p \in \BaireSpace$ gives a $\lPi^0_1$ singleton $\{p\}$: the recursive tree consists of the
        finite prefixes of $p$.
-/
theorem computableSingletonTree_body {p : ℕ → ℕ} {P : AlphaTerm} (hP : NumericalComputes P p) :
    treeBody (computableSingletonTree hP).tree = {p} := by
  ext q
  constructor
  · intro hq
    have he : q = p := by
      funext n
      have h := hq (n + 1) n (by simp [seqPrefix_length])
      exact (seqPrefix_get q _).symm.trans h.symm
    exact he
  · intro hq
    have he : q = p := hq
    subst q
    exact fun n => prefixOfSeq_seqPrefix p n

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A computable point $p \in \BaireSpace$ gives a $\lPi^0_1$ singleton $\{p\}$: the recursive tree consists of the
        finite prefixes of $p$.
-/
theorem computable_point_singleton_effectivelyClosed {p : ℕ → ℕ} {P : AlphaTerm}
    (hP : NumericalComputes P p) : EffectivelyClosed {p} := by
  rw [← computableSingletonTree_body hP]
  exact recursive_tree_body_effectivelyClosed (computableSingletonTree hP)

end PolishSpaceBook
