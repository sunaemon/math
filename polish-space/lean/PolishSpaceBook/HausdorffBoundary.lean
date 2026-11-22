module

public import PolishSpaceBook.HausdorffDifference
public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.Topology.Baire.Lemmas

@[expose] public section

/-!
# The closed boundary derivative for Hausdorff's theorem

At each step retain exactly the points where both sides remain arbitrarily close.
A countable basis bounds the first stable stage, and Baire category makes that
stage empty for a set whose two sides are G-delta.
-/

noncomputable section
namespace PolishSpaceBook.HausdorffDifference
open Set Order Topology TopologicalSpace
universe u
variable {X : Type u} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Let $A\in\bDelta^0_2(X)$. Define a decreasing sequence of closed sets by transfinite recursion:
    $$
    F_0=X,\qquad
    F_\lambda=\bigcap_{\xi<\lambda}F_\xi\quad(\lambda\text{ limit}),
    $$
    and
    $$
    F_{\xi+1}
    =
    \AmbientClosure{F_\xi}{A\cap F_\xi}
    \cap
    \AmbientClosure{F_\xi}{(\SetDifference{X}{A})\cap F_\xi}.
    $$
    The operation on the right is monotone in the closed set $F_\xi$ and takes values in $F_\xi$.
    Consequently all stages are closed and the sequence is decreasing. Since $F_\xi$ is closed in $X$, the two
    relative closures in the formula agree with their closures in $X$. Thus $F_{\xi+1}$ is the relative boundary,
    inside $F_\xi$, between $A$ and its complement. Outside $F_{\xi+1}$, membership in $A$ is locally constant
    relative to $F_\xi$.
-/
def boundaryDerivative (A F : Set X) : Set X := closure (A ∩ F) ∩ closure (Aᶜ ∩ F)

lemma boundaryDerivative_closed (A F : Set X) : IsClosed (boundaryDerivative A F) :=
  isClosed_closure.inter isClosed_closure

lemma boundaryDerivative_mono (A : Set X) : Monotone (boundaryDerivative A) := by
  intro F G h
  exact inter_subset_inter (closure_mono (inter_subset_inter_right A h))
    (closure_mono (inter_subset_inter_right Aᶜ h))

lemma boundaryDerivative_subset (A : Set X) {F : Set X} (hF : IsClosed F) :
    boundaryDerivative A F ⊆ F :=
  inter_subset_left.trans (closure_minimal inter_subset_right hF)

/-- This equation is equivalent to the initial, successor and limit recursion. -/
def boundaryStage (A : Set X) (a : Ordinal.{u}) : Set X :=
  {x | ∀ b < a, x ∈ boundaryDerivative A (boundaryStage A b)}
termination_by a

lemma boundaryStage_eq (A : Set X) (a : Ordinal.{u}) :
    boundaryStage A a = {x | ∀ b < a, x ∈ boundaryDerivative A (boundaryStage A b)} := by
  rw [boundaryStage]

lemma boundaryStage_zero (A : Set X) : boundaryStage A 0 = univ := by
  rw [boundaryStage_eq]
  simp

lemma boundaryStage_closed (A : Set X) (a : Ordinal.{u}) : IsClosed (boundaryStage A a) := by
  rw [boundaryStage_eq]
  convert isClosed_iInter (fun b : Ordinal.{u} =>
    isClosed_iInter fun (_ : b < a) => boundaryDerivative_closed A (boundaryStage A b)) using 1
  ext x
  simp

lemma boundaryStage_subset_derivative (A : Set X) {a b : Ordinal.{u}} (h : a < b) :
    boundaryStage A b ⊆ boundaryDerivative A (boundaryStage A a) := by
  rw [boundaryStage_eq A b]
  exact fun _ hx => hx a h

lemma boundaryStage_antitone (A : Set X) : Antitone (boundaryStage A) := by
  intro a b h
  rcases h.eq_or_lt with rfl | h
  · exact Subset.rfl
  · exact (boundaryStage_subset_derivative A h).trans
      (boundaryDerivative_subset A (boundaryStage_closed A a))

lemma boundaryStage_succ (A : Set X) (a : Ordinal.{u}) :
    boundaryStage A (a + 1) = boundaryDerivative A (boundaryStage A a) := by
  apply Subset.antisymm (boundaryStage_subset_derivative A (lt_add_one a))
  intro x hx
  rw [boundaryStage_eq]
  exact fun b hb => boundaryDerivative_mono A (boundaryStage_antitone A (lt_add_one_iff.mp hb)) hx

lemma boundaryStage_limit (A : Set X) {a : Ordinal.{u}} (ha : IsSuccLimit a) :
    boundaryStage A a = ⋂ b < a, boundaryStage A b := by
  apply Subset.antisymm
  · exact fun x hx => mem_iInter₂.mpr fun b hb => boundaryStage_antitone A hb.le hx
  · intro x hx
    rw [boundaryStage_eq]
    exact fun b hb => boundaryStage_subset_derivative A (lt_add_one b)
      (mem_iInter₂.mp hx (b + 1) (ha.succ_lt hb))

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    This derivative reaches the empty set at a countable stage. To see first that some stage stabilizes, choose an
    ordinal whose cardinality exceeds that of the power set of $X$. Two stages below it must agree; since the sequence
    is decreasing, an adjacent pair must also agree. Let $\theta$ be the first ordinal with $F_{\theta+1}=F_\theta$.
    Fix a countable basis $\Sequence{B_n}{n\in\omega}$ of $X$. For every $\xi<\theta$, choose $n(\xi)$ such that
    $$
    B_{n(\xi)}\cap F_\xi\ne\emptyset,
    \qquad
    B_{n(\xi)}\cap F_{\xi+1}=\emptyset.
    $$
    Such a basic open set exists because $F_{\xi+1}$ is a proper closed subset of $F_\xi$.
    If $\xi<\eta<\theta$, then $F_\eta\IncludedIn F_{\xi+1}$, so $B_{n(\xi)}$ cannot meet $F_\eta$.
    Therefore $n(\xi)\ne n(\eta)$. This injection into $\omega$ shows that $\theta$ is countable.
-/
/-- Any antitone closed chain has a countable first adjacent equality. -/
lemma closed_chain_countable_stable [SecondCountableTopology X]
    (F : Ordinal.{u} → Set X) (hF : ∀ a, IsClosed (F a)) (hanti : Antitone F) :
    ∃ a < Ordinal.omega 1, F (a + 1) = F a := by
  classical
  have hex : ∃ a, F (a + 1) = F a := by
    have h := Cardinal.not_injective_limitation_set F
    rw [Set.injOn_iff_injective, Function.not_injective_iff] at h
    obtain ⟨a, b, heq, hne⟩ := h
    have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
    have aux : ∀ a b, a < b → F a = F b → F (a + 1) = F a := by
      intro a b hab heq
      apply Subset.antisymm (hanti (lt_add_one a).le)
      rw [heq]
      exact hanti (add_one_le_of_lt hab)
    rcases lt_or_gt_of_ne hne' with hab | hba
    · exact ⟨a, aux a b hab heq⟩
    · exact ⟨b, aux b a hba heq.symm⟩
  obtain ⟨a, ha, hleast⟩ := wellFounded_lt.has_min {a | F (a + 1) = F a} hex
  have hstrict : ∀ b < a, F (b + 1) ≠ F b := fun b hb heq => hleast b heq hb
  obtain ⟨B, hBc, _, hB⟩ := TopologicalSpace.exists_countable_basis X
  have hdata : ∀ b : Iio a, ∃ U : B,
      (U.val ∩ F b).Nonempty ∧ Disjoint U.val (F (b.val + 1)) := by
    intro b
    obtain ⟨x, hxb, hxnot⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.mpr
      ⟨hanti (lt_add_one b.val).le, hstrict b b.property⟩)
    obtain ⟨U, hUB, hxU, hU⟩ := hB.exists_subset_of_mem_open hxnot (hF (b.val + 1)).isOpen_compl
    exact ⟨⟨U, hUB⟩, ⟨x, hxU, hxb⟩, Set.disjoint_left.mpr fun y hy hyb => hU hy hyb⟩
  choose U hmeet hmiss using hdata
  have hinj : Function.Injective U := by
    intro b c heq
    by_contra hne
    have hne' : b.val ≠ c.val := fun h => hne (Subtype.ext h)
    have aux : ∀ b c : Iio a, b.val < c.val → U b = U c → False := by
      intro b c hbc heq
      obtain ⟨x, hxU, hxc⟩ := hmeet c
      exact Set.disjoint_left.mp (hmiss b) (heq ▸ hxU) (hanti (add_one_le_of_lt hbc) hxc)
    rcases lt_or_gt_of_ne hne' with hbc | hcb
    · exact aux b c hbc heq
    · exact aux c b hcb heq.symm
  let : Countable B := hBc.to_subtype
  let := hinj.countable
  have hcount : (Iio a).Countable := Set.to_countable _
  have hcard := Cardinal.le_aleph0_iff_set_countable.mpr hcount
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0] at hcard
  exact ⟨a, Cardinal.lt_omega_iff_card_lt.mpr (Cardinal.lt_aleph_one_iff.mpr hcard), ha⟩

lemma boundaryStage_countable_stable [SecondCountableTopology X] (A : Set X) :
    ∃ a < Ordinal.omega 1, boundaryStage A (a + 1) = boundaryStage A a :=
  closed_chain_countable_stable _ (boundaryStage_closed A) (boundaryStage_antitone A)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    For each $\xi<\theta$, set
    $$
    P_\xi=\SetDifference{F_\xi}{F_{\xi+1}}.
    $$
    The sets $P_\xi$ partition $X$. Indeed, every point has a first stage at which it no longer belongs to $F_\xi$,
    since $F_\theta=\emptyset$. This first loss cannot occur at a limit stage, where membership means membership in
    all earlier stages; it therefore occurs at a successor. Decreasingness makes the layers disjoint.
-/
/-- Each point leaves at a successor step; limit stages introduce no new loss. -/
lemma boundaryStage_exists_removal (A : Set X) {x : X} (a : Ordinal.{u})
    (hx : x ∉ boundaryStage A a) :
    ∃ b < a, x ∈ boundaryStage A b ∧ x ∉ boundaryStage A (b + 1) := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rw [boundaryStage_eq] at hx
    obtain ⟨b, hb, hxb⟩ : ∃ b < a, x ∉ boundaryDerivative A (boundaryStage A b) := by
      simp only [mem_ofPred_eq] at hx
      push Not at hx
      exact hx
    by_cases hmem : x ∈ boundaryStage A b
    · exact ⟨b, hb, hmem, by rwa [boundaryStage_succ]⟩
    · obtain ⟨c, hc, hxc, hnot⟩ := ih b hb hmem
      exact ⟨c, hc.trans hb, hxc, hnot⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    The open sets representing the two sides of each layer can be given explicitly:
    $$
    \begin{aligned}
    G_\xi&=\SetDifference{X}{\Closure{(\SetDifference{X}{A})\cap F_\xi}},\\
    H_\xi&=\SetDifference{X}{\Closure{A\cap F_\xi}}.
    \end{aligned}
    $$
    They satisfy
    $$
    G_\xi\cap F_\xi=A\cap P_\xi,
    \qquad
    H_\xi\cap F_\xi=\SetDifference{P_\xi}{A}.
    $$
    For example, a point of $A\cap F_\xi$ already belongs to $\Closure{A\cap F_\xi}$, so it leaves the next
    stage precisely when it lies outside $\Closure{(\SetDifference{X}{A})\cap F_\xi}$.
    Conversely, a point of $F_\xi$ outside this latter closure cannot belong to $\SetDifference{X}{A}$.
    This proves the first identity; the second follows by exchanging the two sides.
-/
/-- The two ambient open sets are canonical: no extension choice is needed. -/
def positiveExit (A F : Set X) : Set X := (closure (Aᶜ ∩ F))ᶜ

def negativeExit (A F : Set X) : Set X := (closure (A ∩ F))ᶜ

lemma positiveExit_open (A F : Set X) : IsOpen (positiveExit A F) :=
  isClosed_closure.isOpen_compl

lemma negativeExit_open (A F : Set X) : IsOpen (negativeExit A F) :=
  isClosed_closure.isOpen_compl

lemma positiveExit_inter (A F : Set X) :
    positiveExit A F ∩ F = A ∩ (F \ boundaryDerivative A F) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hxF⟩
    have hxA : x ∈ A := by
      by_contra hn
      exact hx (subset_closure ⟨hn, hxF⟩)
    exact ⟨hxA, hxF, fun hd => hx hd.2⟩
  · rintro ⟨hxA, hxF, hxD⟩
    exact ⟨fun hc => hxD ⟨subset_closure ⟨hxA, hxF⟩, hc⟩, hxF⟩

lemma negativeExit_inter (A F : Set X) :
    negativeExit A F ∩ F = (F \ boundaryDerivative A F) \ A := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hxF⟩
    have hxA : x ∉ A := fun ha => hx (subset_closure ⟨ha, hxF⟩)
    exact ⟨⟨hxF, fun hd => hx hd.1⟩, hxA⟩
  · rintro ⟨⟨hxF, hxD⟩, hxA⟩
    exact ⟨fun hc => hxD ⟨hc, subset_closure ⟨hxA, hxF⟩⟩, hxF⟩

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Put $R_\xi=\SetDifference{X}{F_\xi}$. Then $R_\xi$ is open, the sequence $(R_\xi)_{\xi<\theta}$ is increasing, and
    $$
    R_{\xi+1}
    =
    R_\xi\cup G_\xi\cup H_\xi.
    $$
-/
lemma boundaryDerivative_compl (A : Set X) {F : Set X} (hF : IsClosed F) :
    (boundaryDerivative A F)ᶜ = Fᶜ ∪ negativeExit A F ∪ positiveExit A F := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hn : x ∈ closure (A ∩ F)
    · exact Or.inr fun hp => hx ⟨hn, hp⟩
    · exact Or.inl (Or.inr hn)
  · rintro ((hx | hx) | hx) hd
    · exact hx (boundaryDerivative_subset A hF hd)
    · exact hx hd.1
    · exact hx hd.2

lemma boundary_layers_disjoint (A : Set X) {a b : Ordinal.{u}} (h : a ≠ b) :
    Disjoint (boundaryStage A a \ boundaryStage A (a + 1))
      (boundaryStage A b \ boundaryStage A (b + 1)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact hx.2 (boundaryStage_antitone A (add_one_le_of_lt hlt) hy.1)
  · exact hy.2 (boundaryStage_antitone A (add_one_le_of_lt hgt) hx.1)

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    If the stabilized closed set $F_\theta$ were nonempty, then in the Polish space $F_\theta$ both $A\cap F_\theta$ and
    $\SetDifference{F_\theta}{A}$ would be dense. Since $A\in\bDelta^0_2(X)$, both of these relative sets are $G_\delta$ in
    $F_\theta$. Two disjoint dense $G_\delta$ subsets of a nonempty Polish space cannot exist, by the Baire category
    theorem. Therefore $F_\theta=\emptyset$.
-/
/-- A closed fixed point would have two disjoint dense G-delta sides. -/
lemma boundary_fixed_empty [PolishSpace X] {A F : Set X}
    (hA : IsGδ A) (hcA : IsGδ Aᶜ) (hF : IsClosed F)
    (hfix : boundaryDerivative A F = F) : F = ∅ := by
  let : PolishSpace F := hF.polishSpace
  have hd : Dense ((Subtype.val : F → X) ⁻¹' A) := by
    apply IsInducing.subtypeVal.dense_iff.mpr
    intro x
    rw [Subtype.image_preimage_val, inter_comm]
    exact (show x.val ∈ boundaryDerivative A F by rw [hfix]; exact x.property).1
  have hdc : Dense ((Subtype.val : F → X) ⁻¹' Aᶜ) := by
    apply IsInducing.subtypeVal.dense_iff.mpr
    intro x
    rw [Subtype.image_preimage_val, inter_comm]
    exact (show x.val ∈ boundaryDerivative A F by rw [hfix]; exact x.property).2
  have hboth := Dense.inter_of_Gδ (hA.preimage continuous_subtype_val)
    (hcA.preimage continuous_subtype_val) hd hdc
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let : Nonempty F := ⟨⟨x, hx⟩⟩
  obtain ⟨y, hy, hny⟩ := hboth.nonempty
  exact hny hy

/-- The boundary recursion for a Delta-0-2 set becomes empty at a countable stage. -/
theorem boundaryStage_countable_empty [PolishSpace X] {A : Set X}
    (hA : A ∈ borelDelta (2 : Ordinal)) :
    ∃ a < Ordinal.omega 1, boundaryStage A a = ∅ := by
  have hAG : IsGδ A := by simpa [borelPi_two] using hA.2
  have hcAG : IsGδ Aᶜ := (show IsFsigma A by simpa [borelSigma_two] using hA.1).isGdelta_compl
  obtain ⟨a, ha, hstable⟩ := boundaryStage_countable_stable A
  refine ⟨a, ha, boundary_fixed_empty hAG hcAG (boundaryStage_closed A a) ?_⟩
  rwa [boundaryStage_succ] at hstable

end PolishSpaceBook.HausdorffDifference
