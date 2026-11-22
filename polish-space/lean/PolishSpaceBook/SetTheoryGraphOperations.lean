module

public import PolishSpaceBook.SetTheoryInternalOmega

@[expose] public section

/-! # Ranges, unions, and insertion as internally definable graph operations -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma realize_memberAt_model (M : ZFSet.{u}) {n : ℕ} (i j : Fin n) (xs : Fin n → M) :
    (memberAt i j).Realize Empty.elim xs ↔ (xs i).val ∈ (xs j).val := Iff.rfl

lemma realize_equalAt_model (M : ZFSet.{u}) {n : ℕ} (i j : Fin n) (xs : Fin n → M) :
    (equalAt i j).Realize Empty.elim xs ↔ xs i = xs j := Iff.rfl

lemma realize_pairMemberFormula_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (R a b : Fin n) (xs : Fin n → M) :
    (pairMemberFormula R a b).Realize Empty.elim xs ↔ ZFSet.pair (xs a).val (xs b).val ∈ (xs R).val :=
  realize_pairMemberFormula (M : ZFClass) (fun _ h _ h' => hM.mem_trans h' h) R a b xs

lemma realize_boundedExists_model (M : ZFSet.{u}) {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedExists i φ).Realize Empty.elim xs ↔
      ∃ y : M, y.val ∈ (xs i).val ∧ φ.Realize Empty.elim (Fin.snoc xs y) :=
  realize_boundedExists (M : ZFClass) i φ xs

lemma first_mem_doubleUnion {a b f : ZFSet.{u}} (h : ZFSet.pair a b ∈ f) :
    a ∈ ZFSet.sUnion (ZFSet.sUnion f) := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨{a}, ZFSet.mem_sUnion.mpr ⟨ZFSet.pair a b, h, ?_⟩, ?_⟩ <;> simp [ZFSet.pair]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For a set of ordered pairs $g$, write $\GraphRange{g}$ for its range. More generally, for any set $g$ put
    $$\GraphRange{g}:=\{b\in\bigcup\bigcup g:\exists a\,(\langle a,b\rangle\in g)\}.$$
-/
def graphRange (f : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.sUnion (ZFSet.sUnion f)).sep (fun b => ∃ a, ZFSet.pair a b ∈ f)

lemma mem_graphRange {b f : ZFSet.{u}} : b ∈ graphRange f ↔ ∃ a, ZFSet.pair a b ∈ f := by
  rw [graphRange, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨a, ha⟩ => ⟨second_mem_doubleUnion ha, a, ha⟩⟩

def rangeMemberFormula {n : ℕ} (f b : Fin n) : ForcingFormulas.Formula n :=
  (pairMemberFormula f.castSucc (Fin.last n) b.castSucc).ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Its defining equality is the first-order formula
    $$\forall b\,\bigl(b\in r\leftrightarrow\exists a\,(\langle a,b\rangle\in g)\bigr).$$
-/
def rangeFormula {n : ℕ} (f r : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) r.castSucc).iff (rangeMemberFormula f.castSucc (Fin.last n))).all

def unionFormula {n : ℕ} (x v : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) v.castSucc).iff
    (boundedExists x.castSucc (memberAt (Fin.last n).castSucc (Fin.last (n + 1))))).all

def insertFormula {n : ℕ} (x y v : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) v.castSucc).iff
    (equalAt (Fin.last n) x.castSucc ⊔ memberAt (Fin.last n) y.castSucc)).all

lemma realize_rangeMemberFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) {n : ℕ} (f b : Fin n) (xs : Fin n → M) :
    (rangeMemberFormula f b).Realize Empty.elim xs ↔ (xs b).val ∈ graphRange (xs f).val := by
  have hp (a : M) : (pairMemberFormula f.castSucc (Fin.last n) b.castSucc).Realize Empty.elim
      (Fin.snoc xs a) ↔ ZFSet.pair a.val (xs b).val ∈ (xs f).val :=
    by simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
      realize_pairMemberFormula_model hM
        f.castSucc (Fin.last n) b.castSucc (Fin.snoc xs a)
  simp only [rangeMemberFormula, BoundedFormula.realize_ex, hp, mem_graphRange]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a.val, ha⟩
  · rintro ⟨a, ha⟩
    have hB := union_mem hM hunion (union_mem hM hunion (xs f).property)
    exact ⟨⟨a, hM.mem_trans (first_mem_doubleUnion ha) hB⟩, ha⟩

lemma realize_rangeFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) {n : ℕ} (f r : Fin n) (xs : Fin n → M) :
    (rangeFormula f r).Realize Empty.elim xs ↔ (xs r).val = graphRange (xs f).val := by
  have hr (b : M) : (rangeMemberFormula f.castSucc (Fin.last n)).Realize Empty.elim
      (Fin.snoc xs b) ↔ b.val ∈ graphRange (xs f).val := by
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
      realize_rangeMemberFormula hM hunion f.castSucc (Fin.last n) (Fin.snoc xs b)
  simp only [rangeFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff, hr,
    realize_memberAt_model, Fin.snoc_castSucc, Fin.snoc_last]
  change (∀ b : M, b.val ∈ (xs r).val ↔ b.val ∈ graphRange (xs f).val) ↔ _
  constructor
  · intro h
    apply ZFSet.ext
    intro b
    constructor
    · intro hb; exact (h ⟨b, hM.mem_trans hb (xs r).property⟩).mp hb
    · intro hb
      obtain ⟨a, ha⟩ := mem_graphRange.mp hb
      have hB := union_mem hM hunion (union_mem hM hunion (xs f).property)
      exact (h ⟨b, hM.mem_trans (second_mem_doubleUnion ha) hB⟩).mpr hb
  · intro he b; rw [he]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The same transitivity argument identifies internal unions and insertions with their actual set operations.
-/
lemma realize_unionFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x v : Fin n) (xs : Fin n → M) :
    (unionFormula x v).Realize Empty.elim xs ↔ (xs v).val = ZFSet.sUnion (xs x).val := by
  have hb (z : M) : (boundedExists x.castSucc
      (memberAt (Fin.last n).castSucc (Fin.last (n + 1)))).Realize Empty.elim (Fin.snoc xs z) ↔
      ∃ y : M, y.val ∈ (xs x).val ∧ z.val ∈ y.val :=
    by simpa only [realize_memberAt_model, Fin.snoc_castSucc, Fin.snoc_last] using
      realize_boundedExists_model M x.castSucc
        (memberAt (Fin.last n).castSucc (Fin.last (n + 1))) (Fin.snoc xs z)
  simp only [unionFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff, hb,
    realize_memberAt_model, Fin.snoc_castSucc, Fin.snoc_last]
  change (∀ z : M, z.val ∈ (xs v).val ↔ ∃ y : M, y.val ∈ (xs x).val ∧ z.val ∈ y.val) ↔ _
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨y, hy, hzy⟩ := (h ⟨z, hM.mem_trans hz (xs v).property⟩).mp hz
      exact ⟨y.val, hy, hzy⟩
    · rintro ⟨y, hy, hz⟩
      have hyM := hM.mem_trans hy (xs x).property
      exact (h ⟨z, hM.mem_trans hz hyM⟩).mpr ⟨⟨y, hyM⟩, hy, hz⟩
  · intro he z
    rw [he, ZFSet.mem_sUnion]
    exact ⟨fun ⟨y, hy, hz⟩ => ⟨⟨y, hM.mem_trans hy (xs x).property⟩, hy, hz⟩,
      fun ⟨y, hy, hz⟩ => ⟨y.val, hy, hz⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The same transitivity argument identifies internal unions and insertions with their actual set operations.
-/
lemma realize_insertFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (x y v : Fin n) (xs : Fin n → M) :
    (insertFormula x y v).Realize Empty.elim xs ↔ (xs v).val = insert (xs x).val (xs y).val := by
  simp only [insertFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_sup, realize_memberAt_model, realize_equalAt_model,
    Fin.snoc_castSucc, Fin.snoc_last]
  change (∀ z : M, z.val ∈ (xs v).val ↔ z = xs x ∨ z.val ∈ (xs y).val) ↔ _
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      exact ((h ⟨z, hM.mem_trans hz (xs v).property⟩).mp hz).imp (congrArg Subtype.val) id
    · rintro (rfl | hz)
      · exact (h (xs x)).mpr (Or.inl rfl)
      · exact (h ⟨z, hM.mem_trans hz (xs y).property⟩).mpr (Or.inr hz)
  · intro he z
    rw [he, ZFSet.mem_insert_iff]
    exact or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ Iff.rfl

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Both coordinates of every pair in $g$ belong to $\bigcup\bigcup g$.
    If $g\in M$, two unions put this bound in $M$, so transitivity puts both coordinates in $M$.
    Consequently the internal existential formula recognizes exactly the actual range members, and Separation
    gives $\GraphRange{g}\in M$.
-/
lemma graphRange_mem {M f : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1)) (hf : f ∈ M) :
    graphRange f ∈ M := by
  have hB := union_mem hM hunion (union_mem hM hunion hf)
  apply separation_mem_of_absolute hM (rangeMemberFormula (0 : Fin 2) 1) hsep ![⟨f, hf⟩] hB
    (fun b => ∃ a, ZFSet.pair a b ∈ f)
  intro b _
  simpa [Fin.snoc, mem_graphRange] using
    realize_rangeMemberFormula hM hunion (0 : Fin 2) 1 (Fin.snoc ![⟨f, hf⟩] b)

lemma insert_mem {M x y : ZFSet.{u}} (hM : M.IsTransitive) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hx : x ∈ M) (hy : y ∈ M) : insert x y ∈ M := by
  rw [ZFSet.insert_eq]
  exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair hx) hy

end PolishSpaceBook.SetTheoryModels
