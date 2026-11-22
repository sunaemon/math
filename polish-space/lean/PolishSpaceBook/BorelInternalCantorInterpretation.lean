module

public import PolishSpaceBook.BorelInternalInterpretation
public import PolishSpaceBook.BorelCantorGraphs

@[expose] public section

/-! # Internal Borel interpretations on Cantor space

Restrict the Baire interpretation to the internal binary function space. Inverse
images commute with the recursive node equations, so complements have the correct
ambient space and the resulting set has exactly the intended binary points.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

def internalCantorInterpretation (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List Bool) (s : List ℕ) : ZFSet.{u} :=
  internalInterpretation M c hw (fun n => (b n).map Bool.toNat) s ∩ internalCantor M

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Cantor Borel interpretation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The characterization of $Y_M$, the internal Baire interpretation theorem, and the preceding lemma give
    $$\begin{aligned}
    g_{i(x)}\in D_s^M
    &\longleftrightarrow g_{i(x)}\in M\ \text{and}\ i(x)\in A_s\\
    &\longleftrightarrow g_{i(x)}\in M\ \text{and}\ x\in D_s.
    \end{aligned}$$
    In particular, the complement clause uses the model's binary points as its ambient space.
-/
lemma cantorPointGraph_mem_internalCantorInterpretation (M : ZFSet.{u})
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List Bool)
    (s : List ℕ) (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalCantorInterpretation M c hw b s ↔
      cantorPointGraph x ∈ M ∧ x ∈ c.evaluate hw (fun n => cyl (b n)) s := by
  rw [internalCantorInterpretation, ZFSet.mem_inter, cantorPointGraph_mem_internalCantor]
  change (pointGraph (cantorInclusion x) ∈ internalInterpretation M c hw _ s ∧ _) ↔ _
  rw [pointGraph_mem_internalInterpretation]
  have he := Set.ext_iff.mp (c.cantor_evaluate hw b s) x
  change (cantorInclusion x ∈ c.evaluate hw (fun n => cyl ((b n).map Bool.toNat)) s ↔
    x ∈ c.evaluate hw (fun n => cyl (b n)) s) at he
  rw [he]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Cantor Borel interpretation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Both $A_s^M$ and $Y_M$ belong to $M$. Separation with the parameter $Y_M$ forms their intersection;
    transitivity ensures that the internal membership predicate has its actual meaning.
-/
theorem internalCantorInterpretation_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List Bool)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph (fun n => (b n).map Bool.toNat) ∈ M)
    (s : List ℕ) : internalCantorInterpretation M c hw b s ∈ M := by
  let Y : M := ⟨_, internalCantor_mem hM hinf hpair hunion hpower hsep⟩
  have hA := internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw _ hc hb s
  have he : internalCantorInterpretation M c hw b s =
      (internalInterpretation M c hw (fun n => (b n).map Bool.toNat) s).sep
        (fun g => g ∈ Y.val) := by
    ext g
    exact Iff.rfl
  rw [he]
  apply separation_mem_of_absolute hM (memberAt (1 : Fin 2) 0) (hsep _) ![Y] hA
  intro g _
  exact Iff.rfl

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Restriction of Cantor Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every graph in $Y_M$ also belongs to $Y_N$. In either model the membership test is equivalent to the same
    external condition $x\in D_s$, which proves the equality.
-/
theorem internalCantorInterpretation_restrict {M N : ZFSet.{u}} (hMN : M ⊆ N)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List Bool) (s : List ℕ) :
    internalCantorInterpretation N c hw b s ∩ internalCantor M =
      internalCantorInterpretation M c hw b s := by
  apply ZFSet.ext
  intro g
  rw [ZFSet.mem_inter]
  constructor
  · rintro ⟨hg, hgM⟩
    obtain ⟨x, rfl, hx⟩ := mem_internalCantor.mp hgM
    exact (cantorPointGraph_mem_internalCantorInterpretation M c hw b s x).mpr
      ⟨hx, ((cantorPointGraph_mem_internalCantorInterpretation N c hw b s x).mp hg).2⟩
  · intro hg
    have hgM := (ZFSet.mem_inter.mp hg).2
    obtain ⟨x, rfl, hx⟩ := mem_internalCantor.mp hgM
    refine ⟨?_, (cantorPointGraph_mem_internalCantor x).mpr hx⟩
    exact (cantorPointGraph_mem_internalCantorInterpretation N c hw b s x).mpr
      ⟨hMN hx, ((cantorPointGraph_mem_internalCantorInterpretation M c hw b s x).mp hg).2⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For the binary cylinders used in random forcing, §{sec:internal-cantor-borel-sets} restricts this construction
    to the internal Cantor space. Inverse images under the inclusion into Baire space commute with every node equation,
    including complements. Consequently, for Cantor-space codes the corresponding identity is
    $$\BorelInterpretation{c}{N}\cap(\CantorSpace\cap M)=\BorelInterpretation{c}{M}.$$
    Here again points are identified with their function graphs. This proves membership agreement on old binary points;
    it does not identify the measure of an internal set of points with the external measure of that set.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Restriction of Cantor Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The same argument applies to each common point
    without an inclusion assumption.
-/
lemma internalCantorInterpretation_agree {M N : ZFSet.{u}} (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List Bool) (s : List ℕ) (x : ℕ → Bool)
    (hxM : cantorPointGraph x ∈ M) (hxN : cantorPointGraph x ∈ N) :
    cantorPointGraph x ∈ internalCantorInterpretation M c hw b s ↔
      cantorPointGraph x ∈ internalCantorInterpretation N c hw b s := by
  simp only [cantorPointGraph_mem_internalCantorInterpretation, hxM, hxN, true_and]

end PolishSpaceBook.BorelExpression
