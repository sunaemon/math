module

public import PolishSpaceBook.ForcingGenericTruth
public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.PFilterTransport

@[expose] public section

/-! # Generic-filter transport through an internally represented dense embedding -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic BoundedSetPredicate
universe u

/-- Parameters: target conditions, target order, embedding graph, dense test,
and candidate source condition. -/
def densePullbackPredicate : BoundedSetPredicate 5 :=
  .ex 3 (.ex 0 (.conj (.pairMember 2 4 6) (.pairMember 1 6 5)))

def denseImagePredicate : BoundedSetPredicate 3 := .ex 1 (.pairMember 0 3 2)

/-- Parameters: source, target, target order, embedding graph, the bound,
and the candidate target condition. -/
def imageBelowOrIncompatiblePredicate : BoundedSetPredicate 6 :=
  .disj (.conj (.ex 0 (.pairMember 3 6 5)) (.pairMember 2 5 4))
    (.all 1 (.neg (.conj (.pairMember 2 6 5) (.pairMember 2 6 4))))

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (P Q S E : M) [Preorder (Condition P.val)] [Preorder (Condition Q.val)]
  (e : Condition P.val ↪o Condition Q.val)
  (hS : ∀ p q : Condition Q.val, pair p.val q.val ∈ S.val ↔ p ≤ q)
  (hE : ∀ p : Condition P.val, ∀ q : Condition Q.val, pair p.val q.val ∈ E.val ↔ e p = q)
  (hd : ∀ q : Condition Q.val, ∃ p, e p ≤ q)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    More generally, let $e:P\to Q$ be an internally represented dense order embedding, where both
    orders and their order relations belong to $M$. For an $M$-generic filter $G$ on $P$, put
    $$H=\{q\in Q:\exists p\in G\ (e(p)\le q)\}.$$
    This is a filter. If $D\in M$ is dense in $Q$, then
    $$T=\{p\in P:\exists d\in D\ (e(p)\le d)\}$$
    belongs to $M$ and is dense in $P$: first refine $e(p)$ into $D$, then refine further into the image
    of $e$. Meeting $T$ makes $H$ meet $D$. Hence $H$ is $M$-generic.

    Conversely, let $H$ be $M$-generic on $Q$ and put $G=\{p\in P:e(p)\in H\}$.
    For each $b\in H$, the set consisting of image conditions below $b$ together with all conditions
    incompatible with $b$ is dense and belongs to $M$. A filter containing $b$ cannot meet the
    incompatible part. Thus there is $p\in G$ with $e(p)\le b$.
    This property makes $G$ nonempty and directed, and upward closure follows from monotonicity of $e$.
    For every dense $D\in M$ in $P$, its image $e[D]$ is internal and dense in $Q$.
    Meeting this image shows that $G$ is $M$-generic. The same refinement property, together with
    order reflection, shows that the two filter constructions are inverse. No countability assumption
    on $M$ enters this correspondence.
-/
include hM hsep hS hE hd in
 theorem modelGeneric_transport (G : Order.PFilter (Condition P.val))
    (hG : ModelGeneric P.val M G) : ModelGeneric Q.val M (transportPFilter e G) := by
  intro D hDM hDQ hD
  let T := P.val.sep (fun p => ∃ d ∈ D, ∃ q ∈ Q.val,
    pair p q ∈ E.val ∧ pair q d ∈ S.val)
  have hT : T ∈ M := by
    have he (p : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![Q, S, E, ⟨D, hDM⟩]) p =
        ![Q.val, S.val, E.val, D, p] := by funext i; fin_cases i <;> rfl
    simpa [T, he, densePullbackPredicate, eval, Fin.snoc, Fin.castLT] using densePullbackPredicate.separation_mem hM (hsep _) ![Q, S, E, ⟨D, hDM⟩] P.property
  have ht (p : Condition P.val) : p.val ∈ T ↔ ∃ d : Condition Q.val, d.val ∈ D ∧ e p ≤ d := by
    simp only [T, mem_sep, p.property, true_and]
    constructor
    · rintro ⟨d, hdD, q, hqQ, hpq, hqd⟩
      have heq := (hE p ⟨q, hqQ⟩).mp hpq
      exact ⟨⟨d, hDQ hdD⟩, hdD, heq ▸ (hS ⟨q, hqQ⟩ ⟨d, hDQ hdD⟩).mp hqd⟩
    · rintro ⟨d, hdD, hpd⟩
      exact ⟨d.val, hdD, (e p).val, (e p).property, (hE p (e p)).mpr rfl, (hS (e p) d).mpr hpd⟩
  have htDense : IsCoinitial {p : Condition P.val | p.val ∈ T} := by
    intro p
    obtain ⟨d, hdD, hdp⟩ := hD (e p)
    obtain ⟨r, hrd⟩ := hd d
    exact ⟨r, (ht r).mpr ⟨d, hdD, hrd⟩, e.le_iff_le.mp (hrd.trans hdp)⟩
  obtain ⟨p, hpG, hpT⟩ := hG T hT (fun _ h => (mem_sep.mp h).1) htDense
  obtain ⟨d, hdD, hpd⟩ := (ht p).mp hpT
  exact ⟨d, (mem_transportPFilter e G d).mpr ⟨p, hpG, hpd⟩, hdD⟩

include hM hsep hS hE hd in
 theorem modelGeneric_image_coinitial (H : Order.PFilter (Condition Q.val))
    (hH : ModelGeneric Q.val M H) (b : Condition Q.val) (hb : b ∈ H) :
    ∃ p : Condition P.val, e p ∈ H ∧ e p ≤ b := by
  let J := Q.val.sep (fun q =>
    ((∃ p ∈ P.val, pair p q ∈ E.val) ∧ pair q b.val ∈ S.val) ∨
      ∀ r ∈ Q.val, ¬(pair r q ∈ S.val ∧ pair r b.val ∈ S.val))
  have hJ : J ∈ M := by
    let bm : M := ⟨b.val, hM.mem_trans b.property Q.property⟩
    have he (q : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, Q, S, E, bm]) q =
        ![P.val, Q.val, S.val, E.val, b.val, q] := by funext i; fin_cases i <;> rfl
    simpa [J, he, imageBelowOrIncompatiblePredicate, eval, Fin.snoc, Fin.castLT] using imageBelowOrIncompatiblePredicate.separation_mem hM (hsep _) ![P, Q, S, E, bm] Q.property
  have hj (q : Condition Q.val) : q.val ∈ J ↔
      (∃ p : Condition P.val, e p = q ∧ q ≤ b) ∨ incompatible Q.val q b := by
    simp only [J, mem_sep, q.property, true_and]
    constructor
    · rintro (⟨⟨p, hp, hpq⟩, hqb⟩ | h)
      · exact Or.inl ⟨⟨p, hp⟩, (hE ⟨p, hp⟩ q).mp hpq, (hS q b).mp hqb⟩
      · exact Or.inr (fun ⟨r, hrq, hrb⟩ => h r.val r.property ⟨(hS r q).mpr hrq, (hS r b).mpr hrb⟩)
    · rintro (⟨p, heq, hqb⟩ | h)
      · exact Or.inl ⟨⟨p.val, p.property, (hE p q).mpr heq⟩, (hS q b).mpr hqb⟩
      · exact Or.inr (fun r hr hrs => h ⟨⟨r, hr⟩, (hS ⟨r, hr⟩ q).mp hrs.1, (hS ⟨r, hr⟩ b).mp hrs.2⟩)
  have hjDense : IsCoinitial {q : Condition Q.val | q.val ∈ J} := by
    intro q
    by_cases hc : ∃ r : Condition Q.val, r ≤ q ∧ r ≤ b
    · obtain ⟨r, hrq, hrb⟩ := hc
      obtain ⟨p, hpr⟩ := hd r
      exact ⟨e p, (hj (e p)).mpr (Or.inl ⟨p, rfl, hpr.trans hrb⟩), hpr.trans hrq⟩
    · exact ⟨q, (hj q).mpr (Or.inr hc), le_rfl⟩
  obtain ⟨q, hqH, hqJ⟩ := hH J hJ (fun _ h => (mem_sep.mp h).1) hjDense
  rcases (hj q).mp hqJ with ⟨p, rfl, hpb⟩ | hq
  · exact ⟨p, hqH, hpb⟩
  · obtain ⟨r, _, hrq, hrb⟩ := H.directed q hqH b hb
    exact (hq ⟨r, hrq, hrb⟩).elim

/-- The inverse filter uses coinitial image conditions, obtained from an
internal dense test. Mere nonempty intersection with the image would not suffice. -/
def pullbackPFilter (H : Order.PFilter (Condition Q.val))
    (hco : ∀ b ∈ H, ∃ p, e p ∈ H ∧ e p ≤ b) : Order.PFilter (Condition P.val) :=
  (Order.IsPFilter.of_def (F := {p | e p ∈ H})
    (by obtain ⟨b, hb⟩ := H.nonempty; obtain ⟨p, hp, _⟩ := hco b hb; exact ⟨p, hp⟩)
    (by
      intro p hp q hq
      obtain ⟨b, hb, hbp, hbq⟩ := H.directed (e p) hp (e q) hq
      obtain ⟨r, hr, hrb⟩ := hco b hb
      exact ⟨r, hr, e.le_iff_le.mp (hrb.trans hbp), e.le_iff_le.mp (hrb.trans hbq)⟩)
    (by intro p q hpq hp; exact H.mem_of_le (e.monotone hpq) hp)).toPFilter

lemma mem_pullbackPFilter (H : Order.PFilter (Condition Q.val))
    (hco : ∀ b ∈ H, ∃ p, e p ∈ H ∧ e p ≤ b) (p : Condition P.val) :
    p ∈ pullbackPFilter P Q e H hco ↔ e p ∈ H := Iff.rfl

lemma transport_pullbackPFilter (H : Order.PFilter (Condition Q.val))
    (hco : ∀ b ∈ H, ∃ p, e p ∈ H ∧ e p ≤ b) :
    transportPFilter e (pullbackPFilter P Q e H hco) = H := by
  ext b
  change (∃ p ∈ pullbackPFilter P Q e H hco, e p ≤ b) ↔ b ∈ H
  exact ⟨fun ⟨p, hp, hpb⟩ => H.mem_of_le hpb hp, fun hb => hco b hb⟩

include hM hsep hE hd in
 theorem modelGeneric_pullback (H : Order.PFilter (Condition Q.val))
    (hH : ModelGeneric Q.val M H) (hco : ∀ b ∈ H, ∃ p, e p ∈ H ∧ e p ≤ b) :
    ModelGeneric P.val M (pullbackPFilter P Q e H hco) := by
  intro D hDM hDP hD
  let T := Q.val.sep (fun q => ∃ p ∈ D, pair p q ∈ E.val)
  have hT : T ∈ M := by
    have he (q : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![E, ⟨D, hDM⟩]) q = ![E.val, D, q] := by
      funext i; fin_cases i <;> rfl
    simpa [T, he, denseImagePredicate, eval, Fin.snoc, Fin.castLT] using denseImagePredicate.separation_mem hM (hsep _) ![E, ⟨D, hDM⟩] Q.property
  have ht (q : Condition Q.val) : q.val ∈ T ↔ ∃ p : Condition P.val, p.val ∈ D ∧ e p = q := by
    simp only [T, mem_sep, q.property, true_and]
    exact ⟨fun ⟨p, hpD, hpq⟩ => ⟨⟨p, hDP hpD⟩, hpD, (hE _ q).mp hpq⟩,
      fun ⟨p, hpD, hpq⟩ => ⟨p.val, hpD, (hE p q).mpr hpq⟩⟩
  have htDense : IsCoinitial {q : Condition Q.val | q.val ∈ T} := by
    intro q
    obtain ⟨p, hpq⟩ := hd q
    obtain ⟨r, hrD, hrp⟩ := hD p
    exact ⟨e r, (ht (e r)).mpr ⟨r, hrD, rfl⟩, (e.monotone hrp).trans hpq⟩
  obtain ⟨q, hqH, hqT⟩ := hH T hT (fun _ h => (mem_sep.mp h).1) htDense
  obtain ⟨p, hpD, rfl⟩ := (ht q).mp hqT
  exact ⟨p, hqH, hpD⟩

end PolishSpaceBook.SetTheoryModels
