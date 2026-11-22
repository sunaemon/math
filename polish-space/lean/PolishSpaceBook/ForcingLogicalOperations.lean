module

public import PolishSpaceBook.BorelForcingTruth

@[expose] public section

/-! # Implication and universal quantification for order forcing

The dense tests retain a positive condition or a concrete counterexample.
These are the connective and quantifier steps used after atomic truth.
-/

namespace PolishSpaceBook
open Set
variable {P : Type*} [Preorder P] {I : Type*}

def forcingImp (A B : Set P) : Set P := {p | ∀ q, q ≤ p → q ∈ A → q ∈ B}
def forcingAll (C : I → Set P) : Set P := {p | ∀ i, p ∈ C i}
def forcingImpTest (A B : Set P) : Set P := forcingImp A B ∪ (A ∩ forcingNeg B)
def forcingAllTest (C : I → Set P) : Set P := forcingAll C ∪ ⋃ i, forcingNeg (C i)

lemma forcingImp_lower (A B : Set P) : IsLowerSet (forcingImp A B) :=
  fun _ _ hqp hp r hrq => hp r (hrq.trans hqp)

lemma forcingAll_lower (C : I → Set P) (hC : ∀ i, IsLowerSet (C i)) :
    IsLowerSet (forcingAll C) := fun _ _ hqp hp i => hC i hqp (hp i)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For implication, fix a condition forcing the antecedent; the dense refinements force the consequent, so the
    inductive saturation of the consequent applies.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    the universal-style clauses ($\neg, \to, \forall$) inherit by reusing $q
    \le p$ as a stronger universal hypothesis.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For conjunction, density
    of conditions forcing both conjuncts gives density for each separately, and the induction hypothesis applies.
    For negation, a condition forcing the positive formula would have a refinement forcing its negation, a contradiction.
-/
lemma forcingImp_saturated {A B : Set P} (hA : IsLowerSet A)
    (hB : forcingDense B ⊆ B) : forcingDense (forcingImp A B) ⊆ forcingImp A B := by
  intro p hp q hqp hqA
  apply hB
  intro r hrq
  obtain ⟨s, hsr, hs⟩ := hp r (hrq.trans hqp)
  exact ⟨s, hsr, hs s le_rfl (hA (hsr.trans hrq) hqA)⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For universal quantification, apply inductive saturation
    to each name instance.
-/
lemma forcingAll_saturated {C : I → Set P} (hC : ∀ i, forcingDense (C i) ⊆ C i) :
    forcingDense (forcingAll C) ⊆ forcingAll C := by
  intro p hp i
  apply hC i
  intro q hqp
  obtain ⟨r, hrq, hr⟩ := hp q hqp
  exact ⟨r, hrq, hr i⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    A useful consequence of density-saturation is the following refinement rule: if $p$ does not force $\varphi$,
    there is $q\le p$ such that no $r\le q$ forces $\varphi$. Otherwise the conditions forcing $\varphi$ would be dense
    below $p$, and saturation would make $p$ force $\varphi$.
-/
lemma not_forcing_refinement {A : Set P} (hA : forcingDense A ⊆ A) {p : P} (hp : p ∉ A) :
    ∃ q, q ≤ p ∧ q ∈ forcingNeg A := by
  classical
  have h : p ∉ forcingDense A := fun h => hp (hA h)
  simp only [forcingDense, mem_ofPred_eq] at h
  push Not at h
  exact h

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \emph{Implication.} For the given parameters, let $A$ and $B$ be the forcing sets of $\varphi$ and $\psi$.
    The useful dense test is
    $$\{q:q\forces^*\varphi\to\psi\}
    \;\cup\;\{q\in A:\forall r\le q,\;r\notin B\}.$$
    To see density, if $p$ fails to force the implication, some $q\le p$ belongs to $A$ but not to $B$.
    Apply the refinement rule to $B$ and use downward closure of $A$; a further strengthening lies in the second part.
-/
lemma forcingImpTest_dense {A B : Set P} (hA : IsLowerSet A) (hB : forcingDense B ⊆ B) :
    IsCoinitial (forcingImpTest A B) := by
  classical
  intro p
  by_cases hp : p ∈ forcingImp A B
  · exact ⟨p, Or.inl hp, le_rfl⟩
  · simp only [forcingImp, mem_ofPred_eq] at hp
    push Not at hp
    obtain ⟨q, hqp, hqA, hqB⟩ := hp
    obtain ⟨r, hrq, hr⟩ := not_forcing_refinement hB hqB
    exact ⟨r, Or.inr ⟨hA hrq hqA, hr⟩, hrq.trans hqp⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    \emph{Universal.} Write $C_\tau$ for the conditions forcing $\varphi(\tau)$.
    Use the test
    $$\{q:\forall\tau\in M^P,\;q\in C_\tau\}
    \;\cup\;\bigcup_{\tau\in M^P}\{q:\forall r\le q,\;r\notin C_\tau\}.$$
    It is dense: failure of the first part supplies a name for which forcing fails; the refinement rule then supplies
    a condition in the corresponding part of the union.
-/
lemma forcingAllTest_dense {C : I → Set P} (hC : ∀ i, forcingDense (C i) ⊆ C i) :
    IsCoinitial (forcingAllTest C) := by
  classical
  intro p
  by_cases hp : p ∈ forcingAll C
  · exact ⟨p, Or.inl hp, le_rfl⟩
  · change ¬ ∀ i, p ∈ C i at hp
    obtain ⟨i, hi⟩ := not_forall.mp hp
    obtain ⟨q, hqp, hq⟩ := not_forcing_refinement (hC i) hi
    exact ⟨q, Or.inr (mem_iUnion.mpr ⟨i, hq⟩), hqp⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    If a condition in $G$ forces the implication and the antecedent is true, the induction hypothesis gives a condition
    in $G$ forcing the antecedent. A common strengthening forces the consequent, so it is true by induction.
    Conversely, suppose the implication is true in $M[G]$ and meet the displayed test.
    Its second part would force the antecedent to be true and would prevent any condition in the filter from forcing
    the consequent, contradicting induction and directedness. Hence the filter meets the first part.
    This proves both directions of (‡) for implication.
-/
lemma forcingImp_truth (G : Order.PFilter P) {A B : Set P} (hA : IsLowerSet A)
    (hB : IsLowerSet B) {a b : Prop} (ha : a ↔ ∃ p ∈ G, p ∈ A)
    (hb : b ↔ ∃ p ∈ G, p ∈ B) (ht : ∃ p ∈ G, p ∈ forcingImpTest A B) :
    (∃ p ∈ G, p ∈ forcingImp A B) ↔ (a → b) := by
  constructor
  · rintro ⟨p, hpG, hp⟩ h
    obtain ⟨q, hqG, hq⟩ := ha.mp h
    obtain ⟨r, hrG, hrp, hrq⟩ := G.directed p hpG q hqG
    exact hb.mpr ⟨r, hrG, hp r hrp (hA hrq hq)⟩
  · intro h
    obtain ⟨p, hpG, hp | ⟨hpA, hpB⟩⟩ := ht
    · exact ⟨p, hpG, hp⟩
    · obtain ⟨q, hqG, hq⟩ := hb.mp (h (ha.mpr ⟨p, hpG, hpA⟩))
      exact False.elim (pfilter_not_pos_neg G hB hqG hpG hq hpB)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If $p\in G$ forces the universal formula, it forces every name instance.
    Every element of $M[G]$ is the valuation of a name in $M$, so induction makes the universal formula true in the
    actual domain of the extension. Conversely, suppose every element satisfies the formula and meet the displayed test.
    A condition in its second part would rule out every forcing condition for one name instance.
    That instance is true by assumption, so induction and directedness give a contradiction.
    Hence a condition in $G$ lies in the first part and forces the universal formula.
    This proves (‡), including the passage between quantification over names and quantification over elements of $M[G]$.
-/
lemma forcingAll_truth (G : Order.PFilter P) {C : I → Set P} (hC : ∀ i, IsLowerSet (C i))
    {t : I → Prop} (ht : ∀ i, t i ↔ ∃ p ∈ G, p ∈ C i)
    (hmeet : ∃ p ∈ G, p ∈ forcingAllTest C) :
    (∃ p ∈ G, p ∈ forcingAll C) ↔ ∀ i, t i := by
  constructor
  · rintro ⟨p, hpG, hp⟩ i
    exact (ht i).mpr ⟨p, hpG, hp i⟩
  · intro h
    obtain ⟨p, hpG, hp | hp⟩ := hmeet
    · exact ⟨p, hpG, hp⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      obtain ⟨q, hqG, hq⟩ := (ht i).mp (h i)
      exact False.elim (pfilter_not_pos_neg G (hC i) hqG hpG hq hi)

lemma forcingImp_empty (A : Set P) : forcingImp A ∅ = forcingNeg A := rfl

/-- A common strengthening combines witnesses for the two conjuncts. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Conjunction.} If the conjunction is true in $M[G]$, induction gives conditions $p,q\in G$
    forcing its two conjuncts. Choose $r\in G$ with $r\le p,q$. Monotonicity and the conjunction clause
    show that $r$ forces the conjunction. Conversely, a condition forcing the conjunction forces each conjunct,
    so induction makes both true in the extension. This proves (‡), and (†) follows by the general argument.
-/
lemma forcingAnd_truth (G : Order.PFilter P) {A B : Set P}
    (hA : IsLowerSet A) (hB : IsLowerSet B) :
    (∃ p ∈ G, p ∈ A ∩ B) ↔ (∃ p ∈ G, p ∈ A) ∧ (∃ p ∈ G, p ∈ B) := by
  constructor
  · rintro ⟨p, hpG, hpA, hpB⟩
    exact ⟨⟨p, hpG, hpA⟩, ⟨p, hpG, hpB⟩⟩
  · rintro ⟨⟨p, hpG, hpA⟩, ⟨q, hqG, hqB⟩⟩
    obtain ⟨r, hrG, hrp, hrq⟩ := G.directed p hpG q hqG
    exact ⟨r, hrG, hA hrp hpA, hB hrq hqB⟩

/-- The decision test supplies a negative witness when there is no positive one. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Negation.} By induction, $\varphi$ is false in $M[G]$ exactly when no condition in $G$ forces it.
    Meet the dense decision set
    $$D:=\{q:q\forces^*\varphi\}\cup\{q:q\forces^*\neg\varphi\}.$$
    If $\varphi$ is false, the first alternative is impossible, so some condition in $G$ forces its negation.
    Conversely, suppose $p\in G$ forces $\neg\varphi$. If $\varphi$ were true, induction would supply
    $q\in G$ forcing $\varphi$. A common strengthening $r\in G$ of $p,q$ would force $\varphi$ by monotonicity,
    contrary to the negation clause at $p$. This proves (‡), and hence (†), for negation.
-/
lemma forcingNeg_truth (G : Order.PFilter P) {A : Set P} (hA : IsLowerSet A)
    (ht : ∃ p ∈ G, p ∈ forcingDecision A) :
    (∃ p ∈ G, p ∈ forcingNeg A) ↔ ¬ ∃ p ∈ G, p ∈ A := by
  constructor
  · rintro ⟨p, hpG, hp⟩ ⟨q, hqG, hq⟩
    exact pfilter_not_pos_neg G hA hqG hpG hq hp
  · intro h
    obtain ⟨p, hpG, hp | hp⟩ := ht
    · exact False.elim (h ⟨p, hpG, hp⟩)
    · exact ⟨p, hpG, hp⟩

/-- A dense union yields a concrete index after meeting its decision test. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \emph{Existential.} If $M[G]\models\exists x\,\varphi(x)$, choose a witness.
    By the definition of the extension, it is $\tau^G$ for some $\tau\in M^P$.
    Induction supplies $q\in G$ forcing $\varphi(\tau)$. Every strengthening of $q$ is therefore an existential witness
    condition, so $q$ forces the existential formula.
    Conversely, if $p\in G$ forces the existential formula, its witness conditions are dense below $p$.
    Meet their decision test, just as in the membership case, to obtain $q\in G$ and a name $\tau$ with
    $q\forces^*\varphi(\tau)$. Induction gives the witness $\tau^G$ in the extension.
-/
lemma forcingExists_truth (G : Order.PFilter P) {C : I → Set P}
    (hC : ∀ i, IsLowerSet (C i))
    (ht : ∃ p ∈ G, p ∈ forcingDecision (⋃ i, C i)) :
    (∃ p ∈ G, p ∈ forcingDense (⋃ i, C i)) ↔ ∃ i, ∃ p ∈ G, p ∈ C i := by
  constructor
  · rintro ⟨p, hpG, hp⟩
    obtain ⟨q, hqG, hq⟩ := pfilter_dense_witness G hpG hp ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact ⟨i, q, hqG, hi⟩
  · rintro ⟨i, p, hpG, hp⟩
    exact ⟨p, hpG, fun q hqp => ⟨q, le_rfl, mem_iUnion.mpr ⟨i, hC i hqp hp⟩⟩⟩

/-- Saturation makes double forcing negation equal to the original lower set. -/
lemma forcingNeg_neg_eq {A : Set P} (hA : IsLowerSet A) (hsA : forcingDense A ⊆ A) :
    forcingNeg (forcingNeg A) = A := by
  classical
  ext p
  constructor
  · intro hp
    by_contra h
    obtain ⟨q, hqp, hq⟩ := not_forcing_refinement hsA h
    exact hp q hqp hq
  · intro hp q hqp hq
    exact hq q le_rfl (hA hqp hp)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The primitive definition of negation gives its clause immediately. For conjunction, suppose $p$ forces both
    $\varphi$ and $\psi$. No strengthening can force $\varphi\to\neg\psi$, by monotonicity and the implication clause.
    Hence $p$ forces $\neg(\varphi\to\neg\psi)$. Conversely, if $p$ forces this negation but fails to force $\varphi$,
    the refinement rule gives a strengthening with no further condition forcing $\varphi$;
    that strengthening vacuously forces $\varphi\to\neg\psi$, a contradiction.
    If instead $p$ fails to force $\psi$, a strengthening forces $\neg\psi$ and thus $\varphi\to\neg\psi$, again a
    contradiction. This proves the conjunction clause.
-/
lemma forcingNeg_forcingImp_neg {A B : Set P} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hsA : forcingDense A ⊆ A) (hsB : forcingDense B ⊆ B) :
    forcingNeg (forcingImp A (forcingNeg B)) = A ∩ B := by
  classical
  ext p
  constructor
  · intro hp
    constructor
    · by_contra h
      obtain ⟨q, hqp, hq⟩ := not_forcing_refinement hsA h
      exact hp q hqp (fun r hrq hrA => False.elim (hq r hrq hrA))
    · by_contra h
      obtain ⟨q, hqp, hq⟩ := not_forcing_refinement hsB h
      exact hp q hqp (fun r hrq _ => forcingNeg_lower B hrq hq)
  · rintro ⟨hpA, hpB⟩ q hqp hq
    exact hq q le_rfl (hA hqp hpA) q le_rfl (hB hqp hpB)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For disjunction, if $p$ forces $\neg\varphi\to\psi$, take $q\le p$.
    Either some strengthening of $q$ forces $\varphi$, or $q$ forces $\neg\varphi$ and therefore $\psi$.
    Thus the union of the two forcing sets is dense below $p$.
    Conversely, assume this density and take $q\le p$ forcing $\neg\varphi$.
    Below each strengthening of $q$, the dense union supplies a condition forcing one of the disjuncts.
    The first disjunct is impossible, so the conditions forcing $\psi$ are dense below $q$.
    Saturation gives $q\forces^*\psi$, proving the implication clause for $\neg\varphi\to\psi$.
-/
lemma forcingImp_neg_eq_dense_union {A B : Set P}
    (hsB : forcingDense B ⊆ B) : forcingImp (forcingNeg A) B = forcingDense (A ∪ B) := by
  classical
  ext p
  constructor
  · intro hp q hqp
    by_cases h : ∃ r, r ≤ q ∧ r ∈ A
    · obtain ⟨r, hrq, hr⟩ := h
      exact ⟨r, hrq, Or.inl hr⟩
    · exact ⟨q, le_rfl, Or.inr (hp q hqp (fun r hrq hr => h ⟨r, hrq, hr⟩))⟩
  · intro hp q hqp hq
    apply hsB
    intro r hrq
    obtain ⟨s, hsr, hsA | hsB⟩ := hp r (hrq.trans hqp)
    · exact False.elim (hq s (hsr.trans hrq) hsA)
    · exact ⟨s, hsr, hsB⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Finally, $p$ forces $\neg\forall x\,\neg\varphi(x)$ exactly when every $q\le p$ has a strengthening that forces
    $\varphi(\tau)$ for some name $\tau$; this is precisely the existential density clause.
-/
lemma forcingNeg_all_neg (C : I → Set P) :
    forcingNeg (forcingAll (fun i => forcingNeg (C i))) = forcingDense (⋃ i, C i) := by
  classical
  ext p
  constructor
  · intro hp q hqp
    have h := hp q hqp
    change ¬ ∀ i r, r ≤ q → r ∉ C i at h
    push Not at h
    obtain ⟨i, r, hrq, hr⟩ := h
    exact ⟨r, hrq, mem_iUnion.mpr ⟨i, hr⟩⟩
  · intro hp q hqp hq
    obtain ⟨r, hrq, hr⟩ := hp q hqp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hr
    exact hq i r hrq hi

end PolishSpaceBook
