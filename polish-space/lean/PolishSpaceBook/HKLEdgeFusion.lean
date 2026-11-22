module

public import PolishSpaceBook.HKLBranchFusion

@[expose] public section

/-!
# Witnessed edge fusion for the forward HKL implication

The pair conditions, not only their coordinate sets, are fused. A supplied
continuous injective Baire encoding and closed presentations retain actual
relation witnesses. These hypotheses still need effective presentation codes.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

/-- A word followed by an infinite tail has that word as its initial segment. -/
theorem binaryBranchPrefix_wordTail {n : ℕ} (s : binaryWord n) (c : ℕ → Bool) :
    binaryBranchPrefix (binaryWordTail s c) n = s := by
  funext i
  simp [binaryBranchPrefix, binaryWordTail, i.isLt]

/-- The two elementary infinite branches agree strictly after the joining bit. -/
theorem elementary_branches_agree (k : ℕ) (c : ℕ → Bool) {m : ℕ} (hm : k < m) :
    binaryWordTail (zeroBinaryWord k) (binaryCons false c) m =
      binaryWordTail (zeroBinaryWord k) (binaryCons true c) m := by
  have hmk : ¬ m < k := by omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show m - k ≠ 0 by omega)
  simp only [binaryWordTail, dite_eq_right hmk, hj, binaryCons]

/-- Every later prefix of an elementary pair is an oriented crucial pair. -/
theorem elementary_prefix_crucial (k : ℕ) (c : ℕ → Bool) (j : ℕ) :
    CrucialPair
      (binaryBranchPrefix (binaryWordTail (zeroBinaryWord k) (binaryCons false c)) (k + 1 + j))
      (binaryBranchPrefix (binaryWordTail (zeroBinaryWord k) (binaryCons true c)) (k + 1 + j)) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, ← binaryWordTail_snoc, binaryBranchPrefix_wordTail]
    exact .join k
  | succ j ih =>
    rw [Nat.add_succ, binaryBranchPrefix_succ, binaryBranchPrefix_succ,
      elementary_branches_agree k c (by omega : k < k + 1 + j)]
    exact ih.extend _

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

omit [PolishSpace X] in
/-- A cofinal sequence of edge witnesses has coordinates in every branch node. -/
theorem edge_witness_branch_membership
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X)
    (hnest : ∀ n s b, (S (n + 1)).node (Fin.snoc s b) ⊆ (S n).node s)
    (a b : ℕ → Bool) (N : ℕ)
    (hadj : ∀ j, (crucialPairGraph (N + j)).Adj
      (binaryBranchPrefix a (N + j)) (binaryBranchPrefix b (N + j)))
    (p : X × X)
    (hp : ∀ j, p ∈ (S (N + j)).edge
      (binaryBranchPrefix a (N + j)) (binaryBranchPrefix b (N + j))) :
    (∀ n, p.1 ∈ (S n).node (binaryBranchPrefix a n)) ∧
      (∀ n, p.2 ∈ (S n).node (binaryBranchPrefix b n)) := by
  constructor
  · intro n
    apply branch_conditions_antitone S hnest a (show n ≤ N + n by omega)
    change p.1 ∈ (S (N + n)).node (binaryBranchPrefix a (N + n))
    rw [← (S (N + n)).fst_edge _ _ (hadj n)]
    exact ⟨p, hp n, rfl⟩
  · intro n
    apply branch_conditions_antitone S hnest b (show n ≤ N + n by omega)
    change p.2 ∈ (S (N + n)).node (binaryBranchPrefix b (N + n))
    rw [← (S (N + n)).snd_edge _ _ (hadj n)]
    exact ⟨p, hp n, rfl⟩

/-- Pair fusion proves the elementary relation, provided the closed
presentations and cofinal dense encounters are supplied. Node uniqueness
identifies both coordinates of the actual pair witness. -/
theorem hkl_elementary_related_of_edge_fusion
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X)
    (hnest : ∀ n s b, (S (n + 1)).node (Fin.snoc s b) ⊆ (S n).node s)
    (henest : ∀ n s t b, (S (n + 1)).edge (Fin.snoc s b) (Fin.snoc t b) ⊆ (S n).edge s t)
    (E : Setoid X) (hE : ∀ n, (S n).EdgesIn E)
    (π : (ℕ → Bool) → X)
    (hunique : ∀ a x, (∀ n, x ∈ (S n).node (binaryBranchPrefix a n)) → x = π a)
    (f : X × X → FusionReal) (hf : Continuous f) (hinj : Injective f)
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i))
    (hpres : ∀ n s t, (crucialPairGraph n).Adj s t →
      ∃ i, f '' (S n).edge s t = Prod.fst '' K i)
    (hmeet : ∀ D ∈ analyticFusionRequirements K, ∀ N, ∃ n, N ≤ n ∧
      ∀ s t (h : (crucialPairGraph n).Adj s t),
        encodeAnalyticCondition f hf ((S n).edgeCondition h) ∈ D)
    (k : ℕ) (c : ℕ → Bool) :
    E.r (π (binaryWordTail (zeroBinaryWord k) (binaryCons false c)))
      (π (binaryWordTail (zeroBinaryWord k) (binaryCons true c))) := by
  let a := binaryWordTail (zeroBinaryWord k) (binaryCons false c)
  let b := binaryWordTail (zeroBinaryWord k) (binaryCons true c)
  have hadj j := (elementary_prefix_crucial k c j).adj
  let P (j : ℕ) : AnalyticCondition (X × X) := (S (k + 1 + j)).edgeCondition (hadj j)
  have hP : Antitone P := by
    apply antitone_nat_of_succ_le
    intro j
    change (S (k + 1 + (j + 1))).edge (binaryBranchPrefix a (k + 1 + (j + 1)))
      (binaryBranchPrefix b (k + 1 + (j + 1))) ⊆
      (S (k + 1 + j)).edge (binaryBranchPrefix a (k + 1 + j)) (binaryBranchPrefix b (k + 1 + j))
    rw [Nat.add_succ, binaryBranchPrefix_succ, binaryBranchPrefix_succ]
    have hab : a (k + 1 + j) = b (k + 1 + j) := elementary_branches_agree k c (by omega)
    rw [hab]
    exact henest _ _ _ _
  have hPM : ∀ D ∈ analyticFusionRequirements K, ∃ j, encodeAnalyticCondition f hf (P j) ∈ D := by
    intro D hD
    obtain ⟨n, hn, hDn⟩ := hmeet D hD (k + 1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨j, hDn _ _ (hadj j)⟩
  obtain ⟨p, hp, _⟩ := analytic_fusion_of_encoding f hf hinj K hK P hP
    (fun j => hpres _ _ _ (hadj j)) hPM
  have hnodes := edge_witness_branch_membership S hnest a b (k + 1) hadj p hp
  have hp1 := hunique a p.1 hnodes.1
  have hp2 := hunique b p.2 hnodes.2
  have hrel := hE (k + 1 + 0) _ _ (hadj 0) p (hp 0)
  simpa only [hp1, hp2] using hrel

/-- The witnessed elementary pairs and the finite crucial-pair paths prove
the forward eventual-equality implication. The converse needs generic pairs. -/
theorem hkl_e0_preserved_of_edge_fusion
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X)
    (hnest : ∀ n s b, (S (n + 1)).node (Fin.snoc s b) ⊆ (S n).node s)
    (henest : ∀ n s t b, (S (n + 1)).edge (Fin.snoc s b) (Fin.snoc t b) ⊆ (S n).edge s t)
    (E : Setoid X) (hE : ∀ n, (S n).EdgesIn E)
    (π : (ℕ → Bool) → X)
    (hunique : ∀ a x, (∀ n, x ∈ (S n).node (binaryBranchPrefix a n)) → x = π a)
    (f : X × X → FusionReal) (hf : Continuous f) (hinj : Injective f)
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i))
    (hpres : ∀ n s t, (crucialPairGraph n).Adj s t →
      ∃ i, f '' (S n).edge s t = Prod.fst '' K i)
    (hmeet : ∀ D ∈ analyticFusionRequirements K, ∀ N, ∃ n, N ≤ n ∧
      ∀ s t (h : (crucialPairGraph n).Adj s t),
        encodeAnalyticCondition f hf ((S n).edgeCondition h) ∈ D)
    {a b : ℕ → Bool} (hab : E0 a b) : E.r (π a) (π b) := by
  apply e0_preserved_of_crucial_pairs E π _ hab
  exact hkl_elementary_related_of_edge_fusion S hnest henest E hE π hunique f hf hinj K hK hpres hmeet

end PolishSpaceBook
