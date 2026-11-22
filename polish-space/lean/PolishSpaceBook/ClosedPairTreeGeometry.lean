module

public import PolishSpaceBook.PairTreeGeometry
public import PolishSpaceBook.AnalyticConditionCatalog

@[expose] public section

/-! # Closed pair trees independent of a computation model

A closed relation is recovered from its nonempty synchronized cylinder
intersections. The proof retains the point and witness prefixes separately.
-/
namespace PolishSpaceBook
open Set MeasureTheory

theorem fusionCylinder_eq_cyl_ofFn {n : ℕ} (s : FusionPrefix n) :
    fusionCylinder s = cyl (List.ofFn s) := by
  ext x
  simp [fusionCylinder, cyl, prefixOfSeq, Fin.forall_iff]

def closedPairTreeCode (K : Set (FusionReal × FusionReal)) :
    Set (finseq ℕ × finseq ℕ) :=
  {z | z.1.length = z.2.length ∧ (K ∩ (cyl z.1 ×ˢ cyl z.2)).Nonempty}

theorem closedPairTreeCode_synchronized (K : Set (FusionReal × FusionReal)) :
    ∀ z ∈ closedPairTreeCode K, z.1.length = z.2.length := fun _ h => h.1

theorem closedPairTreeCode_downward (K : Set (FusionReal × FusionReal)) :
    ∀ z ∈ closedPairTreeCode K, ∀ n, (z.1.take n, z.2.take n) ∈ closedPairTreeCode K := by
  rintro z ⟨hlen, p, hpK, hps, hpt⟩ n
  refine ⟨by simp only [List.length_take, hlen], p, hpK, ?_, ?_⟩
  · exact cyl_subset_of_prefix (List.take_prefix n z.1) hps
  · exact cyl_subset_of_prefix (List.take_prefix n z.2) hpt

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose closed sets $K_i\IncludedIn\BaireSpace\times\BaireSpace$ with $A_i=\pi_0(K_i)$, and set
    $$T_i=\{(s,t):|s|=|t|,\quad K_i\cap(\cyl{s}\times\cyl{t})\ne\emptyset\}.$$
    These sets of nodes are synchronized and downward closed. If $(x,y)\in K_i$, every pair of its equal-length
    prefixes belongs to $T_i$. Conversely, if all those prefix pairs belong to $T_i$, choose a point of $K_i$
    in each corresponding cylinder. These points converge to $(x,y)$, since both coordinates agree with
    it on increasingly long prefixes. Closedness gives $(x,y)\in K_i$. Hence $[T_i]=K_i$, including when
    $K_i$ is empty.
-/
theorem pairTreeBody_closedPairTreeCode (K : Set (FusionReal × FusionReal)) (hK : IsClosed K) :
    pairTreeBody (closedPairTreeCode K) = K := by
  ext p
  constructor
  · intro hp
    have hne : ∀ n, (witnessProjection K (fun i : Fin n => p.1 i)
        (fun i : Fin n => p.2 i)).Nonempty := by
      intro n
      obtain ⟨q, hqK, hqs, hqt⟩ := (hp n).2
      refine ⟨q.1, ?_, q.2, ?_, hqK⟩
      · simpa [fusionCylinder_eq_cyl_ofFn, seqPrefix] using hqs
      · simpa [fusionCylinder_eq_cyl_ofFn, seqPrefix] using hqt
    have hlimit := closed_witness_prefix_fusion K hK
      (fun n i => p.1 i) (fun n i => p.2 i) (fun _ _ => rfl) (fun _ _ => rfl) hne
    change (p.1, p.2) ∈ K at hlimit
    exact hlimit
  · intro hp n
    exact ⟨by simp [seqPrefix_length], p, hp,
      mem_cyl_seqPrefix p.1 n, mem_cyl_seqPrefix p.2 n⟩

end PolishSpaceBook
