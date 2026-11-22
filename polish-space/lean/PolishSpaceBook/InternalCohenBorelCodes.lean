module

public import PolishSpaceBook.InternalCohenConditions
public import PolishSpaceBook.BorelInternalLeafFamilies
public import PolishSpaceBook.SetTheoryInternalListCodes

@[expose] public section

/-! # Internal Borel codes for dense cylinder families and their closed complements -/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open NamedLambda
open scoped Classical
universe u

/-- Retain a numbered word in D; otherwise repeat a fixed member's index. -/
def cohenLeafIndex (D : Set CohenCondition) (k n : ℕ) : ℕ :=
  if NatListCode.decode n ∈ binaryLift D then n else k

/-- Parameters word family, decoding graph, all finite words, fallback index, input, output. -/
def cohenLeafIndexPredicate : BoundedSetPredicate 6 :=
  .ex 2 (.conj (.pairMember 1 4 6)
    (.disj (.conj (.member 6 0) (.equal 5 4))
      (.conj (.neg (.member 6 0)) (.equal 5 3))))

lemma eval_cohenLeafIndexPredicate (D : Set CohenCondition) (k n : ℕ) (y : ZFSet.{u}) :
    cohenLeafIndexPredicate.eval ![cohenConditionSet D, listDecodeGraph, finiteSequences,
      natOrdinal k, natOrdinal n, y] ↔ y = natOrdinal (cohenLeafIndex D k n) := by
  simp only [cohenLeafIndexPredicate, eval, Fin.snoc]
  change (∃ w ∈ finiteSequences, pair (natOrdinal n) w ∈ listDecodeGraph ∧
    ((w ∈ cohenConditionSet D ∧ y = natOrdinal n) ∨
      (w ∉ cohenConditionSet D ∧ y = natOrdinal k))) ↔ _
  rw [BorelExpression.exists_mem_finiteSequences]
  simp only [pair_mem_listDecodeGraph, exists_eq_left, cohenConditionSet, wordGraph_mem_wordTreeSet]
  by_cases h : NatListCode.decode n ∈ binaryLift D <;> simp [cohenLeafIndex, h]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
theorem cohenLeafIndex_graph_mem (D : Set CohenCondition) (hD : cohenConditionSet D ∈ M) (k : ℕ) :
    pointGraph (cohenLeafIndex D k) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  let ps : Fin 4 → M := ![⟨_, hD⟩,
    ⟨_, listDecodeGraph_mem hM hinf hpair hunion hpower hsep⟩,
    ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩, ⟨_, hn k⟩]
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep cohenLeafIndexPredicate ps
    (fun n => ⟨natOrdinal (cohenLeafIndex D k n), hn _⟩)
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val =
      ![cohenConditionSet D, listDecodeGraph, finiteSequences, natOrdinal k, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_cohenLeafIndexPredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

def cohenOpenCode (D : Set CohenCondition) (k : ℕ) : Code :=
  Code.iUnion fun n => Code.leaf (cohenLeafIndex D k n)

def cohenClosedCode (D : Set CohenCondition) (k : ℕ) : Code :=
  (cohenOpenCode D k).compl

lemma cohenLeafIndex_of_mem {D : Set CohenCondition} {s : CohenCondition} (hs : s ∈ D) (k : ℕ) :
    cohenLeafIndex D k (NatListCode.encode (s.map Bool.toNat)) = NatListCode.encode (s.map Bool.toNat) := by
  have hm : s.map Bool.toNat ∈ binaryLift D := ⟨s, hs, rfl⟩
  simp [cohenLeafIndex, NatListCode.decode_encode, hm]

lemma cohenLeafIndex_spec {D : Set CohenCondition} {s : CohenCondition} (hs : s ∈ D) (n : ℕ) :
    ∃ t ∈ D, cohenLeafIndex D (NatListCode.encode (s.map Bool.toNat)) n =
      NatListCode.encode (t.map Bool.toNat) := by
  by_cases h : NatListCode.decode n ∈ binaryLift D
  · obtain ⟨t, ht, he⟩ := h
    refine ⟨t, ht, ?_⟩
    rw [cohenLeafIndex, ite_eq_left ⟨t, ht, he⟩, he, NatListCode.encode_decode]
  · exact ⟨s, hs, ite_eq_right h⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Use the standard cylinder coding of §{sec:internal-cantor-borel-sets}. Choose $s_*\in D$, put
    $k=\FiniteSequenceCode{s_*}$, and let $s_n\in\finseq{\omega}$ be the word with $\FiniteSequenceCode{s_n}=n$.
    Define
    $$
    \ell_n:=
    \begin{cases}
    n,&s_n\in D,\\
    k,&s_n\notin D.
    \end{cases}
    $$
    Every selected word belongs to $D$, and each word in $D$ is selected at its own index. Hence
    $$
    a:=\BorelUnionCode{\Sequence{\BorelLeafCode{\ell_n}}{n\in\omega}},
    \qquad
    b:=\BorelComplementCode{a}
    $$
    interpret respectively as $U_D$ and its complement in Cantor space.
-/
theorem cohenOpenCode_cantor {D : Set CohenCondition} {s : CohenCondition} (hs : s ∈ D) :
    (cohenOpenCode D (NatListCode.encode (s.map Bool.toNat))).cantor = cylinderCode D := by
  rw [cohenOpenCode, Code.cantor_iUnion]
  ext x
  simp only [Set.mem_iUnion, mem_cylinderCode]
  constructor
  · rintro ⟨n, hx⟩
    obtain ⟨t, ht, he⟩ := cohenLeafIndex_spec hs n
    rw [he] at hx
    exact ⟨t, ht, (Code.cantor_binaryCylinder t) ▸ hx⟩
  · rintro ⟨t, ht, hxt⟩
    refine ⟨NatListCode.encode (t.map Bool.toNat), ?_⟩
    rw [cohenLeafIndex_of_mem ht]
    change x ∈ (Code.binaryCylinder t).cantor
    rwa [Code.cantor_binaryCylinder]

theorem cohenClosedCode_cantor {D : Set CohenCondition} {s : CohenCondition} (hs : s ∈ D) :
    (cohenClosedCode D (NatListCode.encode (s.map Bool.toNat))).cantor = (cylinderCode D)ᶜ := by
  rw [cohenClosedCode, Code.cantor_compl, cohenOpenCode_cantor hs]

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The finite-word decoding graph belongs to $M$. The displayed case distinction is bounded, so Replacement
    collects the entire index sequence in $M$. The leaf constructor has a uniform bounded description;
    another application of Replacement collects the entire sequence of leaf label graphs.
    The internal union and complement constructors then give the label graphs of $a$ and $b$ in $M$.
    Thus the construction uses an internal sequence, not merely separately internal leaves.
    Finally, $U_D$ is dense and open by the Cohen dense-open correspondence, so its complement is closed and nowhere
    dense. The same argument applies inside $M$, using the absolute density test of the preceding lemma.
-/
theorem cohenOpenCode_labelGraph_mem (D : Set CohenCondition) (hD : cohenConditionSet D ∈ M) (k : ℕ) :
    (cohenOpenCode D k).val.labelGraph ∈ M :=
  Code.iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
    (leafFamily_labelGraphs_mem hM hinf hpair hunion hpower hsep hrep _
      (cohenLeafIndex_graph_mem hM hinf hpair hunion hpower hsep hrep D hD k))

include hM hinf hpair hunion hpower hsep hrep in
theorem cohenClosedCode_labelGraph_mem (D : Set CohenCondition) (hD : cohenConditionSet D ∈ M) (k : ℕ) :
    (cohenClosedCode D k).val.labelGraph ∈ M :=
  Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
    (cohenOpenCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep D hD k)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Internal closed codes from dense conditions
-/
include hM hinf hpair hunion hpower hsep hrep in
theorem exists_internal_closedCode_of_cohenDense (D : Set CohenCondition)
    (hD : cohenConditionSet D ∈ M) (hd : CohenDense D) :
    ∃ c : Code, c.val.labelGraph ∈ M ∧ c.cantor = (cylinderCode D)ᶜ ∧
      IsClosed c.cantor ∧ IsNowhereDense c.cantor := by
  obtain ⟨s, hs, _⟩ := hd []
  let c := cohenClosedCode D (NatListCode.encode (s.map Bool.toNat))
  have hc : c.cantor = (cylinderCode D)ᶜ := cohenClosedCode_cantor hs
  refine ⟨c, cohenClosedCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep D hD _, hc, ?_⟩
  rw [hc, isClosed_isNowhereDense_iff_compl, compl_compl]
  exact cohen_dense_cylinderCode hd

end PolishSpaceBook
