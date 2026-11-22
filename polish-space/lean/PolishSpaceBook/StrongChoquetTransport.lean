module

public import PolishSpaceBook.StrongChoquetGame
public import Mathlib.Topology.Constructions

@[expose] public section

/-! # Transport of strong Choquet strategies

An open embedding sends moves to open moves in the ambient space. Pulling
responses back preserves legality, and the first move forces the common
point to lie in the image. This includes open subspaces and homeomorphisms.
-/
namespace PolishSpaceBook.StrongChoquetGame
open Set Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Send Player I's point and open set through an open embedding. -/
def mapMove {f : X → Y} (hf : IsOpenEmbedding f) (m : Move X) : Move Y :=
  ⟨f m.point, f '' m.openSet, hf.isOpenMap _ m.isOpen, mem_image_of_mem f m.mem⟩

/-- Pull the ambient response back after mapping the entire finite history. -/
def pullStrategy {f : X → Y} (hf : IsOpenEmbedding f) (σ : Strategy Y) : Strategy X :=
  fun history m =>
    let r := σ (history.map (mapMove hf)) (mapMove hf m)
    ⟨f ⁻¹' r.openSet, r.isOpen.preimage hf.continuous, r.mem,
      fun _ hx => by
        obtain ⟨z, hz, he⟩ := r.subset hx
        exact hf.injective he ▸ hz⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix a winning strategy on $Y$. Send each move $(x,U)$ in $X$ to $(f(x),f[U])$ in $Y$;
    the image is open because $f$ is an open embedding. Apply the fixed strategy to this image history.
    If it returns $V$, respond in $X$ with $f^{-1}[V]$. Continuity makes this response open, and
    injectivity together with $V\IncludedIn f[U]$ gives $f^{-1}[V]\IncludedIn U$. The response contains $x$.

    A legal play in $X$ gives a legal image play in $Y$. Let $y$ belong to every open set in the image
    play. The first of these sets is contained in $f[X]$, so $y=f(x)$ for a unique $x\in X$.
    Injectivity implies that $x$ belongs to every original open set. This is a winning strategy on $X$.
    Apply the result to the inclusion of an open subspace, or to a homeomorphism, for the two consequences.
    \end{proof}
-/
theorem pullStrategy_winning {f : X → Y} (hf : IsOpenEmbedding f)
    (σ : Strategy Y) (hσ : Winning Y σ) : Winning X (pullStrategy hf σ) := by
  intro p hp
  let q : ℕ → Move Y := fun n => mapMove hf (p n)
  have hr (n : ℕ) : (responseAt X (pullStrategy hf σ) p n).openSet =
      f ⁻¹' (responseAt Y σ q n).openSet := by
    simp only [responseAt, pullStrategy, List.map_map, q, Function.comp_def]
  have hq : Legal Y σ q := by
    intro n y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h := hp n hx
    rw [hr] at h
    exact h
  obtain ⟨y, hy⟩ := hσ q hq
  obtain ⟨x, _, rfl⟩ := hy 0
  refine ⟨x, fun n => ?_⟩
  obtain ⟨z, hz, he⟩ := hy n
  exact hf.injective he ▸ hz

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Transport of strong Choquet strategies
-/
theorem IsStrongChoquet.of_openEmbedding {f : X → Y} (hY : IsStrongChoquet Y)
    (hf : IsOpenEmbedding f) : IsStrongChoquet X := by
  obtain ⟨σ, hσ⟩ := hY
  exact ⟨pullStrategy hf σ, pullStrategy_winning hf σ hσ⟩

theorem IsStrongChoquet.open_subspace (hX : IsStrongChoquet X) {A : Set X}
    (hA : IsOpen A) : IsStrongChoquet A :=
  hX.of_openEmbedding hA.isOpenEmbedding_subtypeVal

theorem IsStrongChoquet.of_homeomorph (hY : IsStrongChoquet Y) (e : X ≃ₜ Y) :
    IsStrongChoquet X :=
  hY.of_openEmbedding e.isOpenEmbedding

end PolishSpaceBook.StrongChoquetGame
