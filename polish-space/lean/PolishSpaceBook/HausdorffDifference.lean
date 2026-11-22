module

public import PolishSpaceBook.BorelStructure
public import PolishSpaceBook.BorelOrdinalRankLayers
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

/-!
# The countable difference hierarchy

The first-entry pieces partition the union of the approximating open sets.
Selecting pieces by ordinal parity leaves both the selected set and its
complement F-sigma. Points that never enter form a separate closed piece.
-/

noncomputable section
namespace PolishSpaceBook.HausdorffDifference
open Set Order Topology

def parity (a : Ordinal) : Ordinal := a % 2

lemma ordinal_lt_two {a : Ordinal} (h : a < 2) : a = 0 ∨ a = 1 :=
  Order.le_one_iff.mp (lt_two_iff.mp h)

lemma parity_cases (a : Ordinal) : parity a = 0 ∨ parity a = 1 :=
  ordinal_lt_two (Ordinal.mod_lt a (by norm_num))

@[simp] lemma parity_zero : parity 0 = 0 := Ordinal.zero_mod 2
@[simp] lemma parity_one : parity 1 = 1 := Ordinal.mod_eq_of_lt one_lt_two
@[simp] lemma parity_two : parity 2 = 0 := Ordinal.mod_self 2
@[simp] lemma parity_two_mul (a : Ordinal) : parity (2 * a) = 0 := Ordinal.mul_mod 2 a
@[simp] lemma parity_two_mul_add_one (a : Ordinal) : parity (2 * a + 1) = 1 := by
  rw [parity, Ordinal.mul_add_mod_self]
  exact parity_one

lemma parity_limit {a : Ordinal} (ha : IsSuccLimit a) : parity a = 0 := by
  rcases parity_cases a with h | h
  · exact h
  · have he := Ordinal.div_add_mod a 2
    rw [show a % 2 = 1 from h] at he
    exact (ha.succ_ne (2 * (a / 2)) (by simpa [succ_eq_add_one] using he)).elim

/-- Ordinal remainder by two agrees with the parity of the finite tail after a limit. -/
lemma parity_finite_tail {a : Ordinal} (ha : a = 0 ∨ IsSuccLimit a) (n : ℕ) :
    parity (a + n) = ((n % 2 : ℕ) : Ordinal) := by
  have h : parity a = 0 := ha.elim (fun h => h ▸ parity_zero) parity_limit
  have he : 2 * (a / 2) = a := by simpa [show a % 2 = 0 from h] using Ordinal.div_add_mod a 2
  rw [← he, parity, Ordinal.mul_add_mod_self]
  exact (Ordinal.natCast_mod n 2).symm

variable {X : Type*}

def piece (U : Ordinal → Set X) (ξ : Ordinal) : Set X :=
  U ξ \ ⋃ η < ξ, U η

lemma mem_piece (U : Ordinal → Set X) (ξ : Ordinal) (x : X) :
    x ∈ piece U ξ ↔ x ∈ U ξ ∧ ∀ η < ξ, x ∉ U η := by
  simp [piece]

def chosen (α : Ordinal) (U : Ordinal → Set X) (select : Ordinal → Prop) : Set X :=
  ⋃ ξ : Iio α, ⋃ (_ : select ξ.val), piece U ξ.val

lemma mem_chosen (α : Ordinal) (U : Ordinal → Set X) (select : Ordinal → Prop) (x : X) :
    x ∈ chosen α U select ↔ ∃ ξ < α, select ξ ∧ x ∈ piece U ξ := by
  simp only [chosen, mem_iUnion, Subtype.exists]
  aesop

lemma piece_disjoint (U : Ordinal → Set X) {ξ η : Ordinal} (h : ξ ≠ η) :
    Disjoint (piece U ξ) (piece U η) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [mem_piece] at hx hy
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hy.2 ξ hlt hx.1
  · exact hx.2 η hgt hy.1

/-- A least entry exists for every point in the union, even without monotonicity. -/
lemma exists_first_entry {α : Ordinal} {U : Ordinal → Set X} {x : X}
    (hx : x ∈ ⋃ ξ < α, U ξ) : ∃ ξ < α, x ∈ piece U ξ := by
  have hex : ({ξ : Ordinal | ξ < α ∧ x ∈ U ξ} : Set Ordinal).Nonempty := by
    obtain ⟨ξ, hξ, hxξ⟩ := mem_iUnion₂.mp hx
    exact ⟨ξ, hξ, hxξ⟩
  obtain ⟨ξ, hξ, hmin⟩ := wellFounded_lt.has_min _ hex
  refine ⟨ξ, hξ.1, (mem_piece U ξ x).mpr ⟨hξ.2, ?_⟩⟩
  intro η hη hxη
  exact hmin η ⟨hη.trans hξ.1, hxη⟩ hη

lemma complement_chosen (α : Ordinal) (U : Ordinal → Set X) (select : Ordinal → Prop) :
    (chosen α U select)ᶜ = (⋃ ξ < α, U ξ)ᶜ ∪ chosen α U (fun ξ => ¬ select ξ) := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hxin : x ∈ ⋃ ξ < α, U ξ
    · obtain ⟨ξ, hξ, hxξ⟩ := exists_first_entry hxin
      refine Or.inr ((mem_chosen _ _ _ _).mpr ⟨ξ, hξ, ?_, hxξ⟩)
      exact fun h => hx ((mem_chosen _ _ _ _).mpr ⟨ξ, hξ, h, hxξ⟩)
    · exact Or.inl hxin
  · intro hx hxchosen
    obtain ⟨ξ, hξ, hsξ, hxξ⟩ := (mem_chosen _ _ _ _).mp hxchosen
    rcases hx with hout | hother
    · exact hout (mem_iUnion₂.mpr ⟨ξ, hξ, (mem_piece _ _ _).mp hxξ |>.1⟩)
    · obtain ⟨η, _, hsη, hxη⟩ := (mem_chosen _ _ _ _).mp hother
      by_cases he : ξ = η
      · exact hsη (he ▸ hsξ)
      · exact Set.disjoint_left.mp (piece_disjoint U he) hxξ hxη

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For an ordinal $\xi$, write $\xi=\lambda+n$ uniquely with $\lambda=0$ or $\lambda$ a limit ordinal and $n<\omega$. Call
    $\xi$ *even* or *odd* according as $n$ is even or odd. If $\alpha<\omegaOneOrd$ and $(U_\xi)_{\xi<\alpha}$ is an
    increasing sequence of open subsets of a metric space $X$, define
    $$
    D_\alpha((U_\xi)_{\xi<\alpha})
    =
    \left\{x\in X:
    \begin{array}{l}
    \text{there is a least }\xi<\alpha\text{ with }x\in U_\xi,\\
    \text{and that }\xi\text{ has parity opposite to }\alpha
    \end{array}
    \right\}.
    $$
-/
def differenceSet (α : Ordinal) (U : Ordinal → Set X) : Set X :=
  chosen α U (fun ξ => parity ξ ≠ parity α)

lemma complement_differenceSet (α : Ordinal) (U : Ordinal → Set X) :
    (differenceSet α U)ᶜ = (⋃ ξ < α, U ξ)ᶜ ∪ chosen α U (fun ξ => parity ξ = parity α) := by
  simp only [differenceSet, complement_chosen, not_not]

lemma difference_zero (U : Ordinal → Set X) : differenceSet 0 U = ∅ := by
  ext x
  simp [differenceSet, mem_chosen]

lemma difference_one (U : Ordinal → Set X) : differenceSet 1 U = U 0 := by
  ext x
  simp [differenceSet, mem_chosen, mem_piece]

lemma difference_two (U : Ordinal → Set X) : differenceSet 2 U = U 1 \ U 0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hp, hxξ⟩ := (mem_chosen _ _ _ _).mp hx
    rcases ordinal_lt_two hξ with rfl | rfl
    · simp at hp
    · have h := (mem_piece _ _ _).mp hxξ
      exact ⟨h.1, h.2 0 zero_lt_one⟩
  · rintro ⟨hx1, hx0⟩
    apply (mem_chosen _ _ _ _).mpr
    refine ⟨1, one_lt_two, by simp, (mem_piece _ _ _).mpr ⟨hx1, ?_⟩⟩
    intro η hη
    have : η = 0 := Order.lt_one_iff.mp hη
    simpa [this] using hx0

section Topology
variable [TopologicalSpace X]

lemma fsigma_closed {F : Set X} (hF : IsClosed F) : IsFsigma F :=
  ⟨{F}, countable_singleton F, by simpa using hF, by simp⟩

lemma fsigma_iUnion {ι : Sort*} [Countable ι] {A : ι → Set X} (hA : ∀ i, IsFsigma (A i)) :
    IsFsigma (⋃ i, A i) := by
  apply isFsigma_iff_isGδ_compl.mpr
  rw [compl_iUnion]
  exact IsGδ.iInter fun i => (hA i).isGdelta_compl

lemma fsigma_inter {A B : Set X} (hA : IsFsigma A) (hB : IsFsigma B) : IsFsigma (A ∩ B) := by
  apply isFsigma_iff_isGδ_compl.mpr
  rw [compl_inter]
  exact hA.isGdelta_compl.union hB.isGdelta_compl

lemma fsigma_union {A B : Set X} (hA : IsFsigma A) (hB : IsFsigma B) : IsFsigma (A ∪ B) := by
  apply isFsigma_iff_isGδ_compl.mpr
  rw [compl_union]
  exact hA.isGdelta_compl.inter hB.isGdelta_compl

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    The sets obtained in this way form the $\alpha$-th level $\mathsf D_\alpha(\bSigma^0_1)(X)$ of the hierarchy. Thus
    $\mathsf D_1(\bSigma^0_1)$ consists of the open sets, $\mathsf D_2(\bSigma^0_1)$ consists of differences
    $\SetDifference{U_1}{U_0}$ of open sets with $U_0\IncludedIn U_1$, and higher levels continue by alternating entry into
    an increasing open
    approximation. Within the union of the approximating opens, complementation reverses the selected parity.
    The complement also contains every point that never enters the approximation. Thus reversing parity alone does
    not give the full complement unless the open sets cover the space.
-/
def InLevel (α : Ordinal) (A : Set X) : Prop :=
  ∃ U : Ordinal → Set X, (∀ ξ < α, IsOpen (U ξ)) ∧
    (∀ ξ < α, ∀ η < α, ξ ≤ η → U ξ ⊆ U η) ∧ A = differenceSet α U

lemma level_one_iff {A : Set X} : InLevel 1 A ↔ IsOpen A := by
  constructor
  · rintro ⟨U, hU, _, rfl⟩
    rw [difference_one]
    exact hU 0 zero_lt_one
  · intro hA
    exact ⟨fun _ => A, fun _ _ => hA, fun _ _ _ _ _ => Subset.rfl, (difference_one (fun _ => A)).symm⟩

lemma level_two_iff {A : Set X} : InLevel 2 A ↔
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U ⊆ V ∧ A = V \ U := by
  classical
  constructor
  · rintro ⟨U, hU, hmono, rfl⟩
    exact ⟨U 0, U 1, hU 0 (by norm_num), hU 1 one_lt_two,
      hmono 0 (by norm_num) 1 one_lt_two zero_le_one, difference_two U⟩
  · rintro ⟨U, V, hU, hV, hUV, rfl⟩
    refine ⟨fun ξ => if ξ = 0 then U else V, ?_, ?_, ?_⟩
    · intro ξ _
      dsimp only
      split_ifs <;> assumption
    · intro ξ hξ η hη hle
      rcases ordinal_lt_two hξ with rfl | rfl <;>
        rcases ordinal_lt_two hη with rfl | rfl <;> simp_all
    · simp [difference_two]

end Topology

section Metric
variable [MetricSpace X]

lemma fsigma_open {U : Set X} (hU : IsOpen U) : IsFsigma U := by
  simpa using IsGδ.isFsigma_compl (isGδ_of_isClosed_metric hU.isClosed_compl)

lemma piece_isFsigma {U : Ordinal → Set X} {ξ : Ordinal}
    (hU : ∀ η ≤ ξ, IsOpen (U η)) : IsFsigma (piece U ξ) := by
  apply fsigma_inter (fsigma_open (hU ξ le_rfl))
  apply fsigma_closed
  exact (isOpen_iUnion fun η => isOpen_iUnion fun hη => hU η hη.le).isClosed_compl

lemma chosen_isFsigma {α : Ordinal} (hα : α < Ordinal.omega 1)
    {U : Ordinal → Set X} (hU : ∀ ξ < α, IsOpen (U ξ)) (select : Ordinal → Prop) :
    IsFsigma (chosen α U select) := by
  let := (OrdinalRankLayer.countable_Iio α hα).to_subtype
  exact fsigma_iUnion fun ξ : Iio α => fsigma_iUnion fun (_ : select ξ.val) =>
    piece_isFsigma (fun η hη => hU η (hη.trans_lt ξ.property))

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Put
    $$
    S_\xi=\SetDifference{U_\xi}{\bigcup_{\eta<\xi}U_\eta}.
    $$
    The sets $S_\xi$ are pairwise disjoint: if $\xi<\eta$, membership in $S_\eta$ excludes membership in $U_\xi$.
    Every point of $\bigcup_{\xi<\alpha}U_\xi$ has a least entry stage, so it belongs to exactly one $S_\xi$.
    Thus $D_\alpha((U_\xi))$ is the union of those $S_\xi$ whose parity is opposite to that of $\alpha$. Each $S_\xi$ is the
    intersection of an open set with the complement of an open set. In a metric space this is an $F_\sigma$ set, because
    every open set is $F_\sigma$. Hence $D_\alpha((U_\xi))$ is $F_\sigma$, being a countable union of $F_\sigma$ sets.

    Its complement is the union of the remaining $S_\xi$ together with
    $$
    \SetDifference{X}{\bigcup_{\xi<\alpha}U_\xi} ,
    $$
    which is closed. Hence the complement is also $F_\sigma$. Therefore the set is both $F_\sigma$ and $G_\delta$, so it
    lies in $\bDelta^0_2(X)$.
    \end{proof}
-/
/-- Both the selected pieces and the complementary pieces form countable F-sigma unions. -/
theorem differenceSet_mem_delta2 {α : Ordinal} (hα : α < Ordinal.omega 1)
    {U : Ordinal → Set X} (hU : ∀ ξ < α, IsOpen (U ξ)) :
    differenceSet α U ∈ borelDelta (2 : Ordinal) := by
  have hD : IsFsigma (differenceSet α U) := chosen_isFsigma hα hU _
  have hc : IsFsigma (differenceSet α U)ᶜ := by
    rw [complement_differenceSet]
    exact fsigma_union (fsigma_closed (isOpen_iUnion fun ξ => isOpen_iUnion (hU ξ)).isClosed_compl)
      (chosen_isFsigma hα hU _)
  exact ⟨by simpa [borelSigma_two] using hD, by simpa [borelPi, borelSigma_two] using hc⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: proposition
  excerpt: |
    For every countable $\alpha$, $$ \mathsf D_\alpha(\bSigma^0_1)(X)\IncludedIn \bDelta^0_2(X). $$ \end{proposition*}
-/
theorem level_subset_delta2 {α : Ordinal} (hα : α < Ordinal.omega 1)
    {A : Set X} (hA : InLevel α A) : A ∈ borelDelta (2 : Ordinal) := by
  obtain ⟨U, hU, _, rfl⟩ := hA
  exact differenceSet_mem_delta2 hα hU

end Metric
end PolishSpaceBook.HausdorffDifference
