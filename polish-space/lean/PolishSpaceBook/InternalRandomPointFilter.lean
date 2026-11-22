module

public import PolishSpaceBook.BorelInternalDefects
public import PolishSpaceBook.InternalRandomFilterTransport

@[expose] public section

/-! # Reconstructing a filter on the internal random conditions from a null-avoiding point -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

variable {M D F : ZFSet.{u}}
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hcode : ∀ (c : Code), c.val.labelGraph ∈ M → internalBorelCantorSet M c.val c.property.2.2.2.2.2 ∈ D)
  (himage : ∀ (c : Code) (hc : c.val.labelGraph ∈ M),
    η (nullClassOf (F := F) ⟨_, hcode c hc⟩) = c.measureClass)

/-- A coded set containing a null-avoiding point has a positive internal class. -/
def pointCodeCondition {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (c : Code) (hc : c.val.labelGraph ∈ M) (hxc : x ∈ c.cantor) : InternalRandomCondition D F η :=
  ⟨(nullClassOf (F := F) ⟨_, hcode c hc⟩).val, (hpos _).mp (by
    rw [himage c hc]
    intro hz
    exact hx c hc ((Code.measureClass_eq_bot_iff c).mp hz) hxc)⟩

lemma image_pointCodeCondition {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (c : Code) (hc : c.val.labelGraph ∈ M) (hxc : x ∈ c.cantor) :
    η (internalConditionClass η (pointCodeCondition η hpos hcode himage hx c hc hxc)) = c.measureClass :=
  himage c hc

variable (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

/-- Upward closure of the internal classes of all ground-model codes containing the point. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal point filter from a null-avoiding real
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Now suppose a real $r$ avoids every Borel null set coded in $M$.
    The construction in §{sec:internal-random-point-filters} puts the complement, intersection, and symmetric-difference
    codes in $M$ and uses their null defects to build a filter $G_r$ on the internal positive order.
    For every ground-model coded representative $B$ of a condition $p$,
    $$p\in G_r\quad\Longleftrightarrow\quad r\in B.$$
    The filter is independent of the representatives. Applied to the real of an existing $M$-generic filter $G$,
    the same construction recovers $G$ exactly.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The fixed code for the whole space supplies a member of $G_r$.
    Whenever $r\in A_c$, the class of its internal interpretation is positive: if it were zero, measure comparison
    would make $A_c$ a coded null set containing $r$.
    For two witnesses $c,d$, their intersection code is internal, and its external interpretation contains $r$.
    Its positive class strengthens both conditions. Upward closure follows directly from the definition.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For the membership criterion, a witness $d$ for $p\in G_r$ satisfies $[A_d]\le\eta(p)=[A_c]$.
    The preceding lemma therefore gives $r\in A_c$.
    Conversely, if $r\in A_c$, the code $c$ itself is a witness. The equality case of the preceding lemma gives
    independence of representatives.
-/
def internalPointFilter {x : ℕ → Bool} (hx : AvoidsNullCodes M x) :
    Order.PFilter (InternalRandomCondition D F η) := by
  let S : Set (InternalRandomCondition D F η) := {p | ∃ c : Code, c.val.labelGraph ∈ M ∧
    x ∈ c.cantor ∧ c.measureClass ≤ η (internalConditionClass η p)}
  refine (Order.IsPFilter.of_def (F := S) ?_ ?_ ?_).toPFilter
  · have hc : Code.empty.compl.val.labelGraph ∈ M :=
      Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
        (emptyExpression_labelGraph_mem hM hinf hpair hunion hpower hsep hrep)
    have hxc : x ∈ Code.empty.compl.cantor := by rw [Code.cantor_compl, Code.cantor_empty]; simp
    let p := pointCodeCondition η hpos hcode himage hx _ hc hxc
    exact ⟨p, Code.empty.compl, hc, hxc, (image_pointCodeCondition η hpos hcode himage hx _ hc hxc).ge⟩
  · rintro p ⟨c, hc, hxc, hcp⟩ q ⟨d, hd, hxd, hdq⟩
    have hi := Code.inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d hc hd
    have hxi : x ∈ (Code.inf c d).cantor := by rw [Code.cantor_inf]; exact ⟨hxc, hxd⟩
    let r := pointCodeCondition η hpos hcode himage hx _ hi hxi
    have he := image_pointCodeCondition η hpos hcode himage hx _ hi hxi
    refine ⟨r, ⟨Code.inf c d, hi, hxi, he.ge⟩, ?_, ?_⟩
    · change η (internalConditionClass η r) ≤ η (internalConditionClass η p)
      rw [he, Code.measureClass_inf]
      exact inf_le_left.trans hcp
    · change η (internalConditionClass η r) ≤ η (internalConditionClass η q)
      rw [he, Code.measureClass_inf]
      exact inf_le_right.trans hdq
  · rintro p q hpq ⟨c, hc, hxc, hcp⟩
    exact ⟨c, hc, hxc, hcp.trans hpq⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal point filter from a null-avoiding real
-/
lemma mem_internalPointFilter_iff {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (p : InternalRandomCondition D F η) (c : Code) (hc : c.val.labelGraph ∈ M)
    (he : η (internalConditionClass η p) = c.measureClass) :
    p ∈ internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx ↔ x ∈ c.cantor := by
  change (∃ d : Code, d.val.labelGraph ∈ M ∧ x ∈ d.cantor ∧ d.measureClass ≤ η (internalConditionClass η p)) ↔ _
  constructor
  · rintro ⟨d, hd, hxd, hdp⟩
    exact hx.mono hM hinf hpair hunion hpower hsep hrep d c hd hc (he ▸ hdp) hxd
  · intro hxc
    exact ⟨c, hc, hxc, he.ge⟩

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal point filter from a null-avoiding real
-/
lemma internalPoint_membership_independent {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (p : InternalRandomCondition D F η) (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M)
    (hec : η (internalConditionClass η p) = c.measureClass)
    (hed : η (internalConditionClass η p) = d.measureClass) : x ∈ c.cantor ↔ x ∈ d.cantor :=
  hx.congr hM hinf hpair hunion hpower hsep hrep c d hc hd (hec.symm.trans hed)

end PolishSpaceBook.CantorTreeMeasure
