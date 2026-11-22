module

public import PolishSpaceBook.CantorDerivativeSplitting
public import PolishSpaceBook.LambdaFiniteCheckTrees

@[expose] public section

/-! # Numerical coding of the finite derivative test

Binary words use the book's natural-list code with entries zero and one.
Finite families use a second list code. Invalid word codes are rejected;
missing table entries have the usual zero default, the empty word.
-/
namespace PolishSpaceBook.CantorDerivative
open Set NamedLambda NamedLambda.AlphaTerm

def encodeWord (s : List Bool) : ℕ := NatListCode.encode (s.map Bool.toNat)
def decodeWord (e : ℕ) : List Bool := (NatListCode.decode e).map (fun a => decide (a = 1))
def Binary (e : ℕ) : Prop := ∀ a ∈ NatListCode.decode e, a ≤ 1

theorem binary_encodeWord (s : List Bool) : Binary (encodeWord s) := by
  intro a ha
  simp only [encodeWord, NatListCode.decode_encode, List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  cases b <;> decide

@[simp] theorem decodeWord_encodeWord (s : List Bool) : decodeWord (encodeWord s) = s := by
  simp only [decodeWord, encodeWord, NatListCode.decode_encode, List.map_map]
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp_all

theorem decodeWord_map {e : ℕ} (he : Binary e) :
    (decodeWord e).map Bool.toNat = NatListCode.decode e := by
  simp only [decodeWord, List.map_map]
  calc
    _ = (NatListCode.decode e).map id := by
      apply List.map_congr_left
      intro a ha
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (he a ha) with rfl | rfl <;> decide
    _ = _ := List.map_id _

theorem encodeWord_decodeWord {e : ℕ} (he : Binary e) : encodeWord (decodeWord e) = e := by
  rw [encodeWord, decodeWord_map he, NatListCode.encode_decode]

theorem encodeWord_injective : Function.Injective encodeWord := by
  intro s t h
  simpa using congrArg decodeWord h

@[simp] theorem decodeWord_length (e : ℕ) : (decodeWord e).length = (NatListCode.decode e).length :=
  List.length_map _

theorem decodeWord_prefix {a b : ℕ} (h : NatListCode.decode a <+: NatListCode.decode b) :
    decodeWord a <+: decodeWord b := h.map _

def tableAt (U i : ℕ) : ℕ := (NatListCode.decode U).getD i 0

def encodeTable {m : ℕ} (u : Fin m → List Bool) : ℕ :=
  NatListCode.encode (List.ofFn fun i => encodeWord (u i))

@[simp] theorem tableAt_encodeTable {m : ℕ} (u : Fin m → List Bool) (i : Fin m) :
    tableAt (encodeTable u) i.val = encodeWord (u i) := by
  simp [tableAt, encodeTable, List.getD, i.isLt]

/-- Restrict the original natural-word tree to binary words. -/
def binaryTree (T : Set (List ℕ)) : Set (List Bool) := {s | s.map Bool.toNat ∈ T}

theorem binaryTree_isSubtree {T : Set (List ℕ)} (hT : IsSubtree T) : IsSubtree (binaryTree T) :=
  fun _ _ ht hst => hT ht (hst.map _)

/-- `c` holds the common level and the table of proposed surviving words. -/
def NumericTest (T : Set (List ℕ)) (s m c n V : ℕ) : Prop :=
  Binary s ∧
  (∀ i < m, Binary (tableAt c.unpair.2 i) ∧ Binary (tableAt V i) ∧
    (NatListCode.decode (tableAt c.unpair.2 i)).length = c.unpair.1 ∧
    NatListCode.decode s <+: NatListCode.decode (tableAt c.unpair.2 i) ∧
    (NatListCode.decode (tableAt V i)).length = c.unpair.1+n ∧
    NatListCode.decode (tableAt c.unpair.2 i) <+: NatListCode.decode (tableAt V i) ∧
    NatListCode.decode (tableAt V i) ∈ T) ∧
  (∀ i < m, ∀ j < m, tableAt c.unpair.2 i = tableAt c.unpair.2 j → i = j)

theorem finiteTest_numeric {T : Set (List ℕ)} {s : List Bool} {m N n : ℕ}
    {u v : Fin m → List Bool} (h : FiniteTest (binaryTree T) s m N n u v) :
    NumericTest T (encodeWord s) m (Nat.pair N (encodeTable u)) n (encodeTable v) := by
  refine ⟨binary_encodeWord s, ?_, ?_⟩
  · intro i hi
    have hu := h.2 ⟨i, hi⟩
    simp only [Nat.unpair_pair]
    rw [show tableAt (encodeTable u) i = encodeWord (u ⟨i,hi⟩) from tableAt_encodeTable _ ⟨i,hi⟩,
      show tableAt (encodeTable v) i = encodeWord (v ⟨i,hi⟩) from tableAt_encodeTable _ ⟨i,hi⟩]
    refine ⟨binary_encodeWord _, binary_encodeWord _, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [encodeWord] using hu.1
    · simpa only [encodeWord, NatListCode.decode_encode] using hu.2.1.map Bool.toNat
    · simpa [encodeWord] using hu.2.2.1
    · simpa only [encodeWord, NatListCode.decode_encode] using hu.2.2.2.1.map Bool.toNat
    · simpa only [encodeWord, NatListCode.decode_encode, binaryTree, Set.mem_ofPred_eq] using hu.2.2.2.2
  · intro i hi j hj he
    simp only [Nat.unpair_pair] at he
    rw [show tableAt (encodeTable u) i = encodeWord (u ⟨i,hi⟩) from tableAt_encodeTable _ ⟨i,hi⟩,
      show tableAt (encodeTable u) j = encodeWord (u ⟨j,hj⟩) from tableAt_encodeTable _ ⟨j,hj⟩] at he
    exact congrArg Fin.val (h.1 (encodeWord_injective he))

theorem numeric_finiteTest {T : Set (List ℕ)} {s m c n V : ℕ} (h : NumericTest T s m c n V) :
    FiniteTest (binaryTree T) (decodeWord s) m c.unpair.1 n
      (fun i => decodeWord (tableAt c.unpair.2 i.val))
      (fun i => decodeWord (tableAt V i.val)) := by
  constructor
  · intro i j hij
    apply Fin.ext
    apply h.2.2 i.val i.isLt j.val j.isLt
    have he := congrArg encodeWord hij
    simpa only [encodeWord_decodeWord (h.2.1 i.val i.isLt).1,
      encodeWord_decodeWord (h.2.1 j.val j.isLt).1] using he
  · intro i
    have hi := h.2.1 i.val i.isLt
    refine ⟨by simpa using hi.2.2.1, decodeWord_prefix hi.2.2.2.1,
      by simpa using hi.2.2.2.2.1, decodeWord_prefix hi.2.2.2.2.2.1, ?_⟩
    change (decodeWord (tableAt V i.val)).map Bool.toNat ∈ T
    rw [decodeWord_map hi.2.1]
    exact hi.2.2.2.2.2.2

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    We now replace branches by finite tables. Decode $c=\NatPair{N}{U}$, where $U$ codes a list of
    word codes, and let $u_i$ be its $i$th word. Let $v_i$ similarly come from the table code $V$.
    A missing entry denotes the empty word. Define $R_T(s,m,c,n,V)$ by requiring all words used below
    to be binary and, for $i,j<m$, requiring
    $$\begin{gathered}
     |u_i|=N,\quad s\prefixOf u_i,\quad
     |v_i|=N+n,\quad u_i\prefixOf v_i,\quad v_i\in T,\\
     u_i=u_j\ \Longrightarrow\ i=j.
    \end{gathered}$$
    Then
    $$s\in D\quad\Longleftrightarrow\quad
     \forall m\in\NN\ \exists c\in\NN\ \forall n\in\NN\ \exists V\in\NN\ R_T(s,m,c,n,V).$$
-/
theorem derivative_numeric_iff {T : Set (List ℕ)} (hT : IsSubtree T) (s : List Bool) :
    s ∈ derivativeTree (binaryTree T) ↔
      ∀ m, ∃ c, ∀ n, ∃ V, NumericTest T (encodeWord s) m c n V := by
  rw [mem_derivativeTree_iff_finite_tests (binaryTree_isSubtree hT)]
  constructor
  · intro h m
    obtain ⟨N, u, hu⟩ := h m
    refine ⟨Nat.pair N (encodeTable u), fun n => ?_⟩
    obtain ⟨v, hv⟩ := hu n
    exact ⟨encodeTable v, finiteTest_numeric hv⟩
  · intro h m
    obtain ⟨c, hc⟩ := h m
    refine ⟨c.unpair.1, fun i => decodeWord (tableAt c.unpair.2 i.val), fun n => ?_⟩
    obtain ⟨V, hV⟩ := hc n
    exact ⟨fun i => decodeWord (tableAt V i.val), by simpa using numeric_finiteTest hV⟩

end PolishSpaceBook.CantorDerivative
