module

public import PolishSpaceBook.LambdaPredecessorMaximum
public import PolishSpaceBook.LambdaNotationSequences

@[expose] public section

/-! # Kleene notations cover every recursive ordinal

A finite-window predecessor maximum supplies a canonical increasing sequence
of lower bounds. Successor iteration makes it strictly increasing even while
the chosen predecessor stays unchanged. A delayed self-index produces its
limit code without first executing the sequence.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaRelative
namespace KleeneNotation
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

noncomputable def maximumSelector {ε : ℕ → ℕ} (W : WellOrderPresentation ε) (z : ℕ) : ℕ :=
  W.predecessorMaximum z.unpair.1 z.unpair.2

private theorem base_none {ε : ℕ → ℕ} (W : WellOrderPresentation ε) (f : ℕ → ℕ)
    {a n : ℕ} (h : W.predecessorMaximum a n = 0) :
    selectedBase (maximumSelector W) f a n = 1 := by
  simp [selectedBase,maximumSelector,h]

private theorem base_some {ε : ℕ → ℕ} (W : WellOrderPresentation ε) (f : ℕ → ℕ)
    {a n b : ℕ} (h : W.predecessorMaximum a n = b+1) :
    selectedBase (maximumSelector W) f a n = f b := by
  simp [selectedBase,maximumSelector,h]

private theorem selected_valid {ε : ℕ → ℕ} (W : WellOrderPresentation ε)
    {a n b : ℕ} (h : W.predecessorMaximum a n = b+1) : W.domain b ∧ W.relation b a := by
  rcases W.predecessorMaximum_spec a n with ⟨hz,_⟩ | ⟨c,hc,_,hd,hr,_⟩
  · omega
  · have : c = b := by omega
    subst c
    exact ⟨hd,hr⟩

/-- Validity and arbitrarily long finite successor chains are proved together. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Induct along $R$ on $a\in D$, proving simultaneously that $g(a)$ is valid and that for every $k$,
    $$\KleeneCandidatePrecedes{\KleeneSuccIter{1}{k}}{g(a)},\qquad
     b\in D,\ bRa\ \Longrightarrow
     \KleeneCandidatePrecedes{\KleeneSuccIter{g(b)}{k}}{g(a)}.$$
    Every $b_a(n)$ is valid by the induction hypotheses, so every $c_a(n)$ is valid. If the selected predecessor stays
    unchanged, one additional successor operation gives the comparison from $c_a(n)$ to $c_a(n+1)$. If it changes to a
    larger predecessor $c$, the induction hypothesis at $c$ places all finite successors of the old base below $g(c)$.
    When the old selection was empty, use the assertion about successors of $1$ instead. Append the successors at the new
    stage. This proves strict increase in the generated candidate relation, so the limit rule makes $g(a)$ valid.

    To prove the two additional assertions at $a$, first use stage $n=k$ for the successors of $1$. If its base is $1$,
    one successor step and the limit step suffice; otherwise use the induction hypothesis at the selected predecessor,
    then append the successor and limit steps. For $bRa$, choose $n$ larger than both the numerical code $b$ and $k$.
    The selected predecessor $c$ is then either $b$ or above it. In the first case the stage supplies more than $k$
    successors of $g(b)$; in the second use the induction hypothesis at $c$. Appending the limit step proves the desired
    comparison. This completes the simultaneous induction. Since the targets are now valid, these comparisons also hold
    in the generated precedence relation on $\KleeneO$.
-/
theorem upperFamily_valid {ε : ℕ → ℕ} (W : WellOrderPresentation ε) (u q : ℕ)
    (hc : ∀ a, NumericalComputes (Term.closedProgram (sequenceIndex u q a))
      (upperSequence (maximumSelector W) (delayedLimit u q) a)) :
    ∀ a : W.Carrier,
      Valid (delayedLimit u q a.val) ∧
      (∀ k, RawPrecedes (iterateSuccessor 1 k) (delayedLimit u q a.val)) ∧
      ∀ b : W.Carrier, W.order b a → ∀ k,
        RawPrecedes (iterateSuccessor (delayedLimit u q b.val) k) (delayedLimit u q a.val) := by
  let f := delayedLimit u q
  intro a₀
  apply ((inferInstance : WellFounded W.order)).induction a₀
  intro a ih
  have hv : ∀ n, Valid (selectedBase (maximumSelector W) f a.val n) := by
    intro n
    rcases W.predecessorMaximum_spec a.val n with ⟨hz,_⟩ | ⟨b,hb,_,hd,hr,_⟩
    · rw [base_none W f hz]
      exact .zero
    · rw [base_some W f hb]
      exact (ih ⟨b,hd⟩ hr).1
  have hsv : ∀ n, Valid (upperSequence (maximumSelector W) f a.val n) :=
    fun n => iterateSuccessor_valid (hv n) (n+1)
  have hsi : ∀ n, RawPrecedes (upperSequence (maximumSelector W) f a.val n)
      (upperSequence (maximumSelector W) f a.val (n+1)) := by
    intro n
    unfold upperSequence
    rcases W.predecessorMaximum_spec a.val n with ⟨hz,_⟩ | ⟨b,hb,_,hd,hr,_⟩
    · rw [base_none W f hz]
      rcases W.predecessorMaximum_spec a.val (n+1) with ⟨hz',_⟩ | ⟨c,hc',_,hcd,hca,_⟩
      · rw [base_none W f hz']
        exact iterateSuccessor_step .zero (n+1)
      · rw [base_some W f hc']
        exact ((ih ⟨c,hcd⟩ hca).2.1 (n+1)).trans
          (iterateSuccessor_precedes (ih ⟨c,hcd⟩ hca).1 (m := 0) (by omega))
    · obtain ⟨c,hc',hbc⟩ := W.predecessorMaximum_step hb
      obtain ⟨hcd,hca⟩ := selected_valid W hc'
      rw [base_some W f hb,base_some W f hc']
      rcases hbc with rfl | hbc
      · exact iterateSuccessor_step (ih ⟨b,hd⟩ hr).1 (n+1)
      · exact ((ih ⟨c,hcd⟩ hca).2.2 ⟨b,hd⟩ hbc (n+1)).trans
          (iterateSuccessor_precedes (ih ⟨c,hcd⟩ hca).1 (m := 0) (by omega))
  have hfa : Valid (f a.val) := Valid.limit (sequenceIndex u q a.val) _ (hc a.val) hsv hsi
  have hedge (n : ℕ) : RawPrecedes (upperSequence (maximumSelector W) f a.val n) (f a.val) :=
    .single (.limit (sequenceIndex u q a.val) n _ ((hc a.val).2 n))
  refine ⟨hfa,?_,?_⟩
  · intro k
    apply Relation.TransGen.trans (b := upperSequence (maximumSelector W) f a.val k) _ (hedge k)
    unfold upperSequence
    rcases W.predecessorMaximum_spec a.val k with ⟨hz,_⟩ | ⟨b,hb,_,hd,hr,_⟩
    · rw [base_none W f hz]
      exact iterateSuccessor_step .zero k
    · rw [base_some W f hb]
      exact ((ih ⟨b,hd⟩ hr).2.1 k).trans
        (iterateSuccessor_precedes (ih ⟨b,hd⟩ hr).1 (m := 0) (by omega))
  · intro b hba k
    let n := b.val + k + 1
    obtain ⟨c,hc',hcd,hca,hbc⟩ := W.predecessorMaximum_cofinal
      (N := n) ⟨b.property,hba⟩ (by dsimp [n]; omega)
    apply Relation.TransGen.trans (b := upperSequence (maximumSelector W) f a.val n) _ (hedge n)
    unfold upperSequence
    rw [base_some W f hc']
    rcases hbc with he | hbc
    · subst c
      exact iterateSuccessor_precedes (ih b hba).1 (by dsimp [n]; omega)
    · exact ((ih ⟨c,hcd⟩ hca).2.2 b hbc k).trans
        (iterateSuccessor_precedes (ih ⟨c,hcd⟩ hca).1 (m := 0) (by omega))

/-- The ordinal position of an element is at most the value of its assigned notation. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Write $\rho_W(a)$ for the ordinal position of $a$ in $W$. Another well-founded induction gives
    $\rho_W(a)\le\KleeneValue{g(a)}$: for every $bRa$, the induction hypothesis and strict increase give
    $\rho_W(b)+1\le\KleeneValue{g(a)}$, and take the supremum over all such $b$.
    If $W$ has order type $\alpha$, add a largest element using the recursive successor presentation already constructed.
    Its position is $\alpha$, so its assigned notation has value at least $\alpha$. One further successor produces a
    notation with value strictly above $\alpha$. The preceding downward-closure proposition supplies a notation of value
    exactly $\alpha$. The characterization of recursive ordinals below $\churchKleeneOrd$ gives the last assertion.
    \end{proof}
-/
theorem typein_le_upperFamily {ε : ℕ → ℕ} (W : WellOrderPresentation ε) (u q : ℕ)
    (hc : ∀ a, NumericalComputes (Term.closedProgram (sequenceIndex u q a))
      (upperSequence (maximumSelector W) (delayedLimit u q) a)) (a : W.Carrier) :
    Ordinal.typein W.order a ≤ value (delayedLimit u q a.val) ((upperFamily_valid W u q hc a).1) := by
  have hv := upperFamily_valid W u q hc
  rw [← WellFounded.rank_eq_typein W.order]
  induction a using ((inferInstance : WellFounded W.order)).induction with
  | h a ih =>
    rw [WellFounded.rank_eq]
    apply Ordinal.iSup_le
    intro b
    exact Order.succ_le_of_lt ((ih b.val b.property).trans_lt
      (value_lt (hv b.val).1 (hv a).1 ((hv a).2.2 b.val b.property 0)))

/-- One numerical map produces upper notations from a supplied maximum-selector index. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: corollary
  title: Uniform upper notations from decision indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    §{sec:lambda-recursive-order-programs} gives a total index map $c(d,r)$ for the finite predecessor selector.
    From its output, the uniform sequence construction computes a template index $u(c(d,r))$, a self-index
    $q(c(d,r))$ and the specialized sequence index $s(c(d,r),a)$. Define
    $$g(d,r,a):=3\cdot5^{s(c(d,r),a)}.$$
    Composition makes this a total numerical map of the three supplied inputs. Under the decision hypotheses, the
    selector computes the finite predecessor maxima for $W$. The sequence program therefore computes exactly the
    sequence in the preceding coverage proof, with base values $g(d,r,b)$. Its simultaneous well-founded induction
    gives validity and the two candidate comparisons. Its final rank comparison gives the bound on $\rho_W(a)$.
    All choices of fixed term representatives are made before the two decision-program indices are supplied.
-/
theorem uniform_upper_notations :
    ∃ G g, NumericalComputes G g ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ c, (Term.decode c).fv = ∅ →
        NumericalComputes (Term.closedProgram c) (maximumSelector W) →
        ∀ a : W.Carrier, ∃ ha : Valid (g (Nat.pair c a.val)),
          Ordinal.typein W.order a ≤ value (g (Nat.pair c a.val)) ha ∧
          (∀ k, RawPrecedes (iterateSuccessor 1 k) (g (Nat.pair c a.val))) ∧
          ∀ b : W.Carrier, W.order b a → ∀ k,
            RawPrecedes (iterateSuccessor (g (Nat.pair c b.val)) k) (g (Nat.pair c a.val)) := by
  obtain ⟨U,Q,J,u,q,hU,hQ,hJ,_,h⟩ := uniform_computed_upper_sequences
  have hg := limitCodeProgram_computes.comp hJ
  refine ⟨_,fun z => delayedLimit (u z.unpair.1) (q z.unpair.1) z.unpair.2,
    hg,fun W c hc hC a => ?_⟩
  have hs := h c hc (maximumSelector W) hC
  have hv := upperFamily_valid W (u c) (q c) hs
  simp only [Nat.unpair_pair]
  exact ⟨(hv a).1,typein_le_upperFamily W (u c) (q c) hs a,(hv a).2⟩

/-- Domain and comparison program codes are the only presentation-dependent inputs. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: corollary
  title: Uniform upper notations from decision indices
-/
theorem uniform_upper_notations_from_deciders :
    ∃ H h, NumericalComputes H h ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r,
        (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram r)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∀ a : W.Carrier, ∃ ha : Valid (h (Nat.pair (Nat.pair d r) a.val)),
          Ordinal.typein W.order a ≤ value (h (Nat.pair (Nat.pair d r) a.val)) ha ∧
          (∀ k, RawPrecedes (iterateSuccessor 1 k) (h (Nat.pair (Nat.pair d r) a.val))) ∧
          ∀ b : W.Carrier, W.order b a → ∀ k,
            RawPrecedes (iterateSuccessor (h (Nat.pair (Nat.pair d r) b.val)) k)
              (h (Nat.pair (Nat.pair d r) a.val)) := by
  obtain ⟨F,f,hF,hf⟩ := WellOrderPresentation.uniform_predecessorMaximum_indices
    (ε := fun _ => 0)
  obtain ⟨G,g,hG,hg⟩ := uniform_upper_notations
  have hh := hG.comp ((hF.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨_,fun z => g (Nat.pair (f z.unpair.1) z.unpair.2),hh,
    fun W d r hd hr hD hR a => ?_⟩
  obtain ⟨hc,hC⟩ := hf W d r hd hr hD hR
  simpa only [Nat.unpair_pair] using hg W (f (Nat.pair d r)) hc hC a

/-- The whole upper-notation function has an index computable from the decision indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The index of the entire upper-notation function is computable from $d,r$ as well. Fix a closed term $H$
    computing $\NatPair{\NatPair{d}{r}}{a}\mapsto g(d,r,a)$ and a named representative of $H$ once, and let $h$
    be its syntax code. The uniform parameter construction in §{sec:lambda-index-recursion} gives
    $$e(d,r):=p\bigl(h,\NatPair{d}{r}\bigr).$$
    Then $P_{e(d,r)}$ computes $a\mapsto g(d,r,a)$ for every pair $d,r$, even if they do not describe a well-order.
    The preceding corollary supplies validity and the ordinal bounds when the decision hypotheses hold.
    Thus later constructions can receive the program index $e(d,r)$ directly, without choosing a new representative
    for each presentation.
-/
theorem uniform_upper_notation_program_indices :
    ∃ (E : AlphaTerm) (e g : ℕ → ℕ), NumericalComputes E e ∧
      (∀ z, (Term.decode (e z)).fv = ∅ ∧
        NumericalComputes (Term.closedProgram (e z)) (fun a => g (Nat.pair z a))) ∧
      ∀ W : WellOrderPresentation (fun _ => 0), ∀ d r,
        (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
        NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
        NumericalComputes (Term.closedProgram r)
          (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
        ∀ a : W.Carrier, ∃ ha : Valid (g (Nat.pair (Nat.pair d r) a.val)),
          Ordinal.typein W.order a ≤ value (g (Nat.pair (Nat.pair d r) a.val)) ha ∧
          (∀ k, RawPrecedes (iterateSuccessor 1 k) (g (Nat.pair (Nat.pair d r) a.val))) ∧
          ∀ b : W.Carrier, W.order b a → ∀ k,
            RawPrecedes (iterateSuccessor (g (Nat.pair (Nat.pair d r) b.val)) k)
              (g (Nat.pair (Nat.pair d r) a.val)) := by
  obtain ⟨H,g,hH,hg⟩ := uniform_upper_notations_from_deciders
  obtain ⟨T,hT⟩ := Quotient.exists_rep H
  have ht : mk T = H := hT
  have hc : T.fv = ∅ := by
    have h := hH.1
    rw [← ht] at h
    exact h
  have hp : Term.closedProgram T.code = H := by
    simpa only [Term.closedProgram,Term.decode_code,hc,ite_true] using ht
  obtain ⟨S,s,hS,hs⟩ := uniform_numerical_parameter_indices
  have he := hS.comp ((numericalConstant_computes T.code).pair numericalIdentity_computes)
  refine ⟨_,fun z => s (Nat.pair T.code z),g,he,?_,hg⟩
  intro z
  obtain ⟨hd,_,h⟩ := hs T.code z (by simpa only [Term.decode_code] using hc)
  exact ⟨hd,h g (by rw [hp]; exact hH)⟩

/-- No effective test of well-foundedness is used in producing these codes. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Notations for recursive ordinals
-/
theorem recursiveOrdinal_has_notation {α : Ordinal}
    (hα : RecursiveOrdinal (fun _ => 0) α) : ∃ (a : ℕ) (ha : Valid a), value a ha = α := by
  obtain ⟨W,rfl⟩ := hα
  let V := W.successor
  obtain ⟨C,hC⟩ := V.exists_pure_predecessorMaximum
  obtain ⟨u,q,hq,hc⟩ := exists_computed_upper_sequences hC
  have hlt : W.orderType < V.orderType := by
    rw [show V.orderType = W.orderType+1 from W.successor_orderType]
    exact lt_add_one _
  obtain ⟨a,ha⟩ := Ordinal.typein_surj (r := V.order) hlt
  have hv := (upperFamily_valid V u q hc a).1
  have hle := typein_le_upperFamily V u q hc a
  rw [ha] at hle
  have hsucc : W.orderType < value (successorCode (delayedLimit u q a.val)) (.succ hv) := by
    rw [value_successor _ hv]
    exact hle.trans_lt (Order.lt_succ _)
  obtain ⟨b,hb,_,he⟩ := value_downward (.succ hv) hsucc
  exact ⟨b,hb,he⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Notations for recursive ordinals
-/
theorem below_churchKleene_has_notation {α : Ordinal}
    (hα : α < recursiveOrdinalBound (fun _ => 0)) :
    ∃ (a : ℕ) (ha : Valid a), value a ha = α :=
  recursiveOrdinal_has_notation (recursiveOrdinal_of_lt_bound hα)

end KleeneNotation
end PolishSpaceBook
