module

public import PolishSpaceBook.CantorDerivativeTree

@[expose] public section

/-! # Finite splitting witnesses for a derivative node

Arbitrarily large finite families of distinct same-level surviving words
characterize infinitely many branches. Quantifiers over infinite branches
are replaced by quantifiers over finite words and levels.
-/
namespace PolishSpaceBook.CantorDerivative
open Set

/-- Distinct words at a common level are pairwise incompatible. -/
def Splits (T : Set (List Bool)) (s : List Bool) (m : ℕ) : Prop :=
  ∃ (N : ℕ) (u : Fin m → List Bool), Function.Injective u ∧
    ∀ i, (u i).length = N ∧ s <+: u i ∧ Survives T (u i)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For the forward implication, choose $m$ distinct points of $F\cap\cyl{s}$. At a sufficiently large
    common length $N\ge|s|$, their prefixes are distinct. Use these prefixes for $U$, and their prefixes
    of length $N+n$ for $V$. Conversely, fix $m$ and the corresponding $c$. The same candidates $u_i$
    then have extensions at every depth, so König's lemma gives a branch through each. Their common
    length and distinctness make these branches distinct. There are therefore at least $m$ points of
    $F\cap\cyl{s}$ for every $m$, so this set is infinite. The order of the quantifiers matters: the
    table $U$ is fixed before the depth $n$ is supplied.
-/
theorem infinite_iff_splits {T : Set (List Bool)} (hT : IsSubtree T) (s : List Bool) :
    (cyl s ∩ treeBody T).Infinite ↔ ∀ m, Splits T s m := by
  classical
  constructor
  · intro hs m
    let e := hs.natEmbedding (cyl s ∩ treeBody T)
    let x : Fin m → (ℕ → Bool) := fun i => (e i.val).val
    have hx (i : Fin m) : x i ∈ cyl s ∩ treeBody T := (e i.val).property
    have hinj : Function.Injective x := by
      intro i j hij
      exact Fin.ext (e.injective (Subtype.ext hij))
    let N := s.length + Finset.univ.sup
      (fun ij : Fin m × Fin m => firstDiffIndex (x ij.1) (x ij.2) + 1)
    have hsN : s.length ≤ N := Nat.le_add_right _ _
    have hd (i j : Fin m) : firstDiffIndex (x i) (x j) < N := by
      have h := Finset.le_sup (f := fun ij : Fin m × Fin m =>
        firstDiffIndex (x ij.1) (x ij.2) + 1) (Finset.mem_univ (i,j))
      dsimp only at h
      dsimp [N]
      omega
    refine ⟨N, fun i => seqPrefix (x i) N, ?_, ?_⟩
    · intro i j he
      by_contra hij
      have hne : x i ≠ x j := fun h => hij (hinj h)
      apply firstDiffIndex_spec hne
      have h := congrArg (fun t : List Bool => t[firstDiffIndex (x i) (x j)]?) he
      simpa [seqPrefix, hd i j] using h
    · intro i
      refine ⟨by simp, ?_, (survives_iff hT _).mpr ⟨x i, mem_cyl_seqPrefix _ _, (hx i).2⟩⟩
      have h := seqPrefix_prefixOf_of_le (x i) hsN
      simpa only [seqPrefix_eq_of_mem_cyl (hx i).1] using h
  · intro hs hfinite
    let := hfinite.fintype
    let m := Fintype.card ↥(cyl s ∩ treeBody T) + 1
    obtain ⟨N, u, hinj, hu⟩ := hs m
    have hex (i : Fin m) : ∃ x, x ∈ cyl (u i) ∩ treeBody T :=
      (survives_iff hT _).mp (hu i).2.2
    choose x hx using hex
    let f : Fin m → ↥(cyl s ∩ treeBody T) :=
      fun i => ⟨x i, cyl_subset_of_prefix (hu i).2.1 (hx i).1, (hx i).2⟩
    have hf : Function.Injective f := by
      intro i j he
      apply hinj
      have he' : x i = x j := congrArg Subtype.val he
      have hi : seqPrefix (x i) N = u i := by
        simpa only [(hu i).1] using seqPrefix_eq_of_mem_cyl (hx i).1
      have hj : seqPrefix (x j) N = u j := by
        simpa only [(hu j).1] using seqPrefix_eq_of_mem_cyl (hx j).1
      rw [← hi, ← hj, he']
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin, m] at hcard
    omega

theorem mem_derivativeTree_iff {T : Set (List Bool)} (hT : IsSubtree T) (s : List Bool) :
    s ∈ derivativeTree T ↔ ∀ m, Splits T s m :=
  infinite_iff_splits hT s

/-- All conditions here are on finitely many finite words. -/
def FiniteTest (T : Set (List Bool)) (s : List Bool) (m N n : ℕ)
    (u v : Fin m → List Bool) : Prop :=
  Function.Injective u ∧ ∀ i,
    (u i).length = N ∧ s <+: u i ∧
    (v i).length = N + n ∧ u i <+: v i ∧ v i ∈ T

theorem mem_derivativeTree_iff_finite_tests {T : Set (List Bool)} (hT : IsSubtree T)
    (s : List Bool) :
    s ∈ derivativeTree T ↔
      ∀ m, ∃ (N : ℕ) (u : Fin m → List Bool), ∀ n, ∃ v : Fin m → List Bool, FiniteTest T s m N n u v := by
  classical
  rw [mem_derivativeTree_iff hT]
  constructor
  · intro hs m
    obtain ⟨N, u, hinj, hu⟩ := hs m
    refine ⟨N, u, fun n => ?_⟩
    have hex (i : Fin m) : ∃ t, t.length = N+n ∧ u i <+: t ∧ t ∈ T := by
      simpa only [(hu i).1] using (hu i).2.2 n
    choose v hv using hex
    exact ⟨v, hinj, fun i => ⟨(hu i).1, (hu i).2.1, hv i⟩⟩
  · intro hs m
    obtain ⟨N, u, hv⟩ := hs m
    obtain ⟨v₀, hv₀⟩ := hv 0
    refine ⟨N, u, hv₀.1, fun i => ⟨(hv₀.2 i).1, (hv₀.2 i).2.1, fun n => ?_⟩⟩
    obtain ⟨v, hn⟩ := hv n
    refine ⟨v i, ?_, (hn.2 i).2.2.2⟩
    simpa only [(hv₀.2 i).1] using (hn.2 i).2.2.1

end PolishSpaceBook.CantorDerivative
