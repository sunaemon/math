module

public import PolishSpaceBook.InternalFiniteAdditivity
public import PolishSpaceBook.CantorInternalLevelMeasureCodes

@[expose] public section

/-! # Finite-level values derived from the measure graph and cylinder normalization -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ForcingFormulas ZFSet SetTheoryModels BorelExpression FiniteAdditiveCutGraph
universe u

/-- The internal cylinder associated with one binary word. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a binary word $s$, let $\InternalCylinder{M}{s}$ be its cylinder inside the internal Cantor space:
    $$\InternalCylinder{M}{s}:=\{g\in Y_M:w_s\IncludedIn g\}.$$
    Here $w_s$ is the graph of the binary word viewed as a finite sequence of natural numbers.
    Equivalently, this is the cylinder union of §{sec:internal-borel-measure-cut} for the singleton
    word family $\{w_s\}$. Its points are exactly the graphs in $M$ of external points of $\cyl{s}$.
-/
def internalWordCylinder (M : ZFSet.{u}) (s : List Bool) : ZFSet.{u} :=
  internalCylinderUnion M {wordGraph (s.map Bool.toNat)}

lemma mem_internalWordCylinder_ambient {M g : ZFSet.{u}} {s : List Bool}
    (h : g ∈ internalWordCylinder M s) : g ∈ internalCantor M := by
  unfold internalWordCylinder internalCylinderUnion at h
  exact (ZFSet.mem_sep.mp h).1

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a binary word $s$, let $\InternalCylinder{M}{s}$ be its cylinder inside the internal Cantor space:
    $$\InternalCylinder{M}{s}:=\{g\in Y_M:w_s\IncludedIn g\}.$$
    Here $w_s$ is the graph of the binary word viewed as a finite sequence of natural numbers.
    Equivalently, this is the cylinder union of §{sec:internal-borel-measure-cut} for the singleton
    word family $\{w_s\}$. Its points are exactly the graphs in $M$ of external points of $\cyl{s}$.
-/
lemma cantorPointGraph_mem_internalWordCylinder (M : ZFSet.{u}) (s : List Bool) (x : ℕ → Bool) :
    cantorPointGraph x ∈ internalWordCylinder M s ↔ cantorPointGraph x ∈ M ∧ x ∈ cyl s := by
  simp only [internalWordCylinder, internalCylinderUnion, ZFSet.mem_sep,
    cantorPointGraph_mem_internalCantor, ZFSet.mem_singleton, exists_eq_left]
  change (_ ∧ wordGraph (s.map Bool.toNat) ⊆ pointGraph (cantorInclusion x)) ↔ _
  rw [wordGraph_subset_pointGraph]
  change (_ ∧ x ∈ cantorInclusion ⁻¹' cyl (s.map Bool.toNat)) ↔ _
  rw [BorelExpression.cantorInclusion_preimage_cyl]

lemma internalWordCylinder_disjoint (M : ZFSet.{u}) (n : ℕ) {s t : Fin n → Bool} (hst : s ≠ t) :
    Disjoint ((internalWordCylinder M (List.ofFn s) : ZFSet) : Set ZFSet)
      ((internalWordCylinder M (List.ofFn t) : ZFSet) : Set ZFSet) := by
  rw [Set.disjoint_left]
  intro g hgs hgt
  obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (mem_internalWordCylinder_ambient hgs)
  have hs := (cantorPointGraph_mem_internalWordCylinder M _ x).mp hgs
  have ht := (cantorPointGraph_mem_internalWordCylinder M _ x).mp hgt
  exact Set.disjoint_left.mp (level_cylinders_disjoint n hst) hs.2 ht.2

/-- Enumerate the distinct cylinders of a finite tree level. -/
def levelCylinderList (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ) : List ZFSet.{u} := by
  classical
  exact (level T n).toList.map (fun s => internalWordCylinder M (List.ofFn s))

lemma forall_levelCylinderList (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ) (P : ZFSet.{u} → Prop) :
    (∀ A ∈ levelCylinderList M T n, P A) ↔ ∀ s ∈ level T n, P (internalWordCylinder M (List.ofFn s)) := by
  simp [levelCylinderList]

lemma levelCylinderList_pairwise (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ) :
    (levelCylinderList M T n).Pairwise
      (fun (A B : ZFSet.{u}) => Disjoint (A : Set ZFSet) (B : Set ZFSet)) := by
  unfold levelCylinderList
  rw [List.pairwise_map]
  exact (level T n).nodup_toList.imp (fun hst => internalWordCylinder_disjoint M n hst)

lemma listUnion_levelCylinderList (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ) :
    listUnion (levelCylinderList M T n) = internalLevelSet M T n := by
  ext g
  rw [mem_listUnion]
  constructor
  · rintro ⟨A, hA, hg⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hA
    obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (mem_internalWordCylinder_ambient hg)
    obtain ⟨hxM, hx⟩ := (cantorPointGraph_mem_internalWordCylinder M _ x).mp hg
    apply (cantorPointGraph_mem_internalLevelSet M T n x).mpr
    exact ⟨hxM, Set.mem_iUnion₂.mpr ⟨s, Finset.mem_toList.mp hs, hx⟩⟩
  · intro hg
    have hgy : g ∈ internalCantor M := by
      unfold internalLevelSet internalCylinderUnion at hg
      exact (ZFSet.mem_sep.mp hg).1
    obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp hgy
    obtain ⟨hxM, hx⟩ := (cantorPointGraph_mem_internalLevelSet M T n x).mp hg
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨internalWordCylinder M (List.ofFn s), ?_,
      (cantorPointGraph_mem_internalWordCylinder M _ x).mpr ⟨hxM, hxs⟩⟩
    exact List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Finite-level values from measure axioms
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Enumerate the distinct words of $T_n$ and form their internal cylinders. Their finite union is exactly
    $\InternalTreeLevel{M}{T}{n}$ by its membership definition. Distinct words of length $n$ have disjoint
    external cylinders; restricting to the internal points preserves disjointness.
    Finite additivity and the normalization give $|T_n|$ summands, each equal to $2^{-n}$.
    Thus the decoded value is $|T_n|/2^n$. Validity of the graph value and uniqueness of real coding identify
    its whole code with $\TreeLevelMeasureCode{T}{n}$.
    The entire sequence is therefore the graph $G_Q$ already constructed in §{sec:internal-real-cut-addition}.
-/
theorem finiteMeasure_value_level {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ)
    (hcyl : ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D ∧
      pair (internalWordCylinder M (List.ofFn s)) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F) :
    h.value (internalLevelSet M T n) = (levelWeight T n : ℝ) := by
  have hdom := (forall_levelCylinderList M T n (fun A => A ∈ D)).mpr
    (fun s hs => (hcyl s hs).1)
  have hval := (forall_levelCylinderList M T n
    (fun A => pair A (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F)).mpr (fun s hs => (hcyl s hs).2)
  have hv := h.value_listUnion_const (levelCylinderList M T n) hdom
    (levelCylinderList_pairwise M T n) (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n) hval
  rw [listUnion_levelCylinderList] at hv
  simpa [levelCylinderList, levelWeight] using hv

/-- Uniqueness of the graph value upgrades the numerical equality to equality of whole codes. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Finite-level values from measure axioms
-/
theorem finiteMeasure_code_level {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ)
    (hcyl : ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D ∧
      pair (internalWordCylinder M (List.ofFn s)) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F) :
    h.code (internalLevelSet M T n) = levelMeasureCode T n := by
  have hdom := (forall_levelCylinderList M T n (fun A => A ∈ D)).mpr
    (fun s hs => (hcyl s hs).1)
  have hi := h.listUnion_mem (levelCylinderList M T n) hdom
  rw [listUnion_levelCylinderList] at hi
  calc
    h.code (internalLevelSet M T n) = nonnegativeRealCutCode (h.value (internalLevelSet M T n)) :=
      (h.code_valid hi).encode_decode
    _ = levelMeasureCode T n := by rw [finiteMeasure_value_level h M T n hcyl]; rfl

/-- The measure's actual value sequence is the already constructed internal dyadic-code sequence. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Finite-level values from measure axioms
-/
theorem finiteMeasure_level_sequence_mem {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (h : FiniteAdditiveCutGraph D R F) (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M)
    (hcyl : ∀ n, ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D ∧
      pair (internalWordCylinder M (List.ofFn s)) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F) :
    sequenceGraph (fun n => h.code (internalLevelSet M T n)) ∈ M := by
  have he : (fun n => h.code (internalLevelSet M T n)) = levelMeasureCode T :=
    funext (fun n => finiteMeasure_code_level h M T n (hcyl n))
  rw [he]
  exact levelMeasureCode_sequence_mem hM hinf hpair hunion hpower hsep hrep T hT

end PolishSpaceBook.CantorTreeMeasure
