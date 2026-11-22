module

public import PolishSpaceBook.SetTheoryInternalFiniteSequences
public import PolishSpaceBook.SetTheoryListCodeStep
public import PolishSpaceBook.SetTheoryInjectionOrder

@[expose] public section

/-! # Internal coding and decoding graphs for finite lists

The least fixed point uses the existing zero/paired-successor numbering.
Induction on the list identifies its unique numerical value. Reversing the
graph gives the decoder, using the already proved encode/decode identities.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas NamedLambda
universe u

def listCodeGraph : ZFSet.{u} :=
  ZFSet.range (fun s : List ℕ => pair (wordGraph s) (natOrdinal (NatListCode.encode s)))

lemma pair_mem_listCodeGraph (s : List ℕ) (n : ℕ) :
    pair (wordGraph s) (natOrdinal n) ∈ (listCodeGraph : ZFSet.{u}) ↔ n = NatListCode.encode s := by
  rw [listCodeGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨hs, hn⟩ := ZFSet.pair_inj.mp ht
    have hs' := wordGraph_injective hs
    subst t
    exact (natOrdinal_injective hn).symm
  · rintro rfl
    exact ⟨s, rfl⟩

/-- The fixed point contains precisely the paired-successor code of each list. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Induction on the finite list $s$ proves
    $$\langle e(s),n\rangle\in C\quad\Longleftrightarrow\quad n=\LambdaListCode{s}.$$
    For the empty list, only the initial clause can apply, giving $n=0$. For $a::s$, the initial clause is impossible.
    The cons lemma uniquely determines the head and tail in the step clause. The induction hypothesis fixes the tail
    code, and the pairing graph and successor condition fix the new code. Conversely, the corresponding initial or
    step clause inserts the required pair. Since every element of $C$ lies in $F\times\omega$, these equivalences
    give $C=E$.
-/
lemma listCodeFixedPoint_eq {C : ZFSet.{u}}
    (hfix : (ZFSet.prod finiteSequences Ordinal.omega0.toZFSet).sep
      (listCodeStep Ordinal.omega0.toZFSet finiteSequences (naturalBinaryGraph Nat.pair) (natOrdinal 0) C) = C) :
    C = listCodeGraph := by
  have hmem (p : ZFSet.{u}) : p ∈ C ↔
      p ∈ ZFSet.prod finiteSequences Ordinal.omega0.toZFSet ∧
        (p = pair (wordGraph []) (natOrdinal 0) ∨ ∃ a : ℕ, ∃ s : List ℕ, ∃ n : ℕ,
          pair (wordGraph s) (natOrdinal n) ∈ C ∧
            p = pair (wordGraph (a :: s)) (natOrdinal (Nat.pair a n + 1))) := by
    exact ((Iff.of_eq (congrArg (fun S => p ∈ S) hfix).symm).trans ZFSet.mem_sep).trans
      (and_congr_right fun _ => listCodeStep_natural C p)
  have hbound (s : List ℕ) (n : ℕ) : pair (wordGraph s) (natOrdinal n) ∈
      ZFSet.prod finiteSequences Ordinal.omega0.toZFSet :=
    ZFSet.pair_mem_prod.mpr ⟨mem_finiteSequences.mpr ⟨s, rfl⟩, mem_omegaOrdinal.mpr ⟨n, rfl⟩⟩
  have hvalue (s : List ℕ) : ∀ n : ℕ, pair (wordGraph s) (natOrdinal n) ∈ C ↔
      n = NatListCode.encode s := by
    induction s with
    | nil =>
      intro n
      constructor
      · intro hp
        rcases ((hmem _).mp hp).2 with he | ⟨a, t, k, _, he⟩
        · exact natOrdinal_injective (ZFSet.pair_inj.mp he).2
        · have he' := wordGraph_injective (ZFSet.pair_inj.mp he).1
          cases he'
      · intro hn
        subst n
        exact (hmem _).mpr ⟨hbound [] _, Or.inl rfl⟩
    | cons a s ih =>
      intro n
      constructor
      · intro hp
        rcases ((hmem _).mp hp).2 with he | ⟨b, t, k, htk, he⟩
        · have he' := wordGraph_injective (ZFSet.pair_inj.mp he).1
          cases he'
        · obtain ⟨hs, hn⟩ := ZFSet.pair_inj.mp he
          have hs' := wordGraph_injective hs
          obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
          have hk := (ih k).mp htk
          simpa only [NatListCode.encode, hk] using natOrdinal_injective hn
      · intro hn
        subst n
        exact (hmem _).mpr ⟨hbound (a :: s) _, Or.inr
          ⟨a, s, NatListCode.encode s, (ih _).mpr rfl, rfl⟩⟩
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp ((hmem p).mp hp).1
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hx
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hy
    exact (pair_mem_listCodeGraph s n).mpr ((hvalue s n).mp hp)
  · intro hp
    obtain ⟨s, rfl⟩ := ZFSet.mem_range.mp hp
    exact (hvalue s _).mpr rfl

/-- The existing list-numbering graph is constructed inside the model. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal finite-list encoding graph
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The displayed quantifiers are bounded by $F$ or $\omega$. The predicates $K$, successor, and nested
    pair membership also have bounded expansions. Thus the step is defined by a $\Delta_0$ formula, and transitivity
    makes its internal interpretation agree with the displayed operation. The internal least-fixed-point theorem in
    §{sec:internal-atomic-forcing} gives $C\in M$ with $C=\Phi(C)$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The counterexample-tree tests use numerical pairing, its projections, and finite-list codes. Their lambda
    implementations were given in §{sec:lambda-numerical-pairing} and §{sec:lambda-finite-lists}. To use these tests
    inside a model, we must also construct their set-coded graphs internally. We begin with the arithmetic and
    pairing operations. In this section, $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set,
    and Separation; Choice and Replacement are not needed for these constructions.
-/
theorem listCodeGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (listCodeGraph : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let F : M := ⟨finiteSequences, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let P : M := ⟨naturalBinaryGraph Nat.pair, naturalPairingGraph_mem hM hinf hpair hunion hpower hsep⟩
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩) Ω.property⟩
  let D : M := ⟨ZFSet.prod F.val Ω.val,
    prod_mem_of_separation hM hpair hunion hpower (hsep _) F.property Ω.property⟩
  let step := listCodeStep Ω.val F.val P.val z.val
  obtain ⟨hC, hfix⟩ := internal_definable_fixed_point hM hsep listCodeStepFormula ![Ω, F, P, z] D step (by
    intro C p _
    have he : Fin.snoc (Fin.snoc ![Ω, F, P, z] C) p = ![Ω, F, P, z, C, p] := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact realize_listCodeStepFormula hM Ω F P z C p) (by
    intro C E hCE p _ hp
    rcases hp with hp | ⟨a, ha, s, hs, t, ht, n, hn, l, hl, k, hk, hp, hc, hnC, hpair, hsucc⟩
    · exact Or.inl hp
    · exact Or.inr ⟨a, ha, s, hs, t, ht, n, hn, l, hl, k, hk, hp, hc, hCE hnC, hpair, hsucc⟩)
  exact listCodeFixedPoint_eq hfix ▸ hC

/-- The actual inverse numbering, stored as a graph on the natural numbers. -/
def listDecodeGraph : ZFSet.{u} :=
  sequenceGraph (fun n => wordGraph (NatListCode.decode n))

lemma pair_mem_listDecodeGraph (n : ℕ) (s : List ℕ) :
    pair (natOrdinal n) (wordGraph s) ∈ (listDecodeGraph : ZFSet.{u}) ↔ s = NatListCode.decode n := by
  rw [listDecodeGraph, pair_mem_sequenceGraph]
  exact wordGraph_injective.eq_iff

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The identities
    $$\LambdaListDecode{\LambdaListCode{s}}=s,\qquad
    \LambdaListCode{\LambdaListDecode{n}}=n$$
    proved in §{sec:lambda-finite-lists} identify this set with $D$.
-/
lemma listDecodeGraph_eq_inverse : (listDecodeGraph : ZFSet.{u}) =
    inverseGraph listCodeGraph finiteSequences Ordinal.omega0.toZFSet := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    apply pair_mem_inverseGraph.mpr
    exact ⟨mem_omegaOrdinal.mpr ⟨n, rfl⟩, mem_finiteSequences.mpr ⟨_, rfl⟩,
      (pair_mem_listCodeGraph _ n).mpr (NatListCode.encode_decode n).symm⟩
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hp).1
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hy
    have he := (pair_mem_listCodeGraph s n).mp (pair_mem_inverseGraph.mp hp).2.2
    rw [he, pair_mem_listDecodeGraph, NatListCode.decode_encode]

/-- Reversing the internal encoding graph gives the whole internal decoder. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Internal finite-list decoding graph
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separate from $\omega\times F$ the reversed pairs of $E$:
    $$\{\langle n,s\rangle\in\omega\times F:\langle s,n\rangle\in E\}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Thus decoding is the actual inverse numbering,
    and its whole graph belongs to the model.
-/
theorem listDecodeGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (listDecodeGraph : ZFSet.{u}) ∈ M := by
  rw [listDecodeGraph_eq_inverse]
  exact inverseGraph_mem hM hpair hunion hpower hsep (listCodeGraph_mem hM hinf hpair hunion hpower hsep)
    (finiteSequences_mem hM hinf hpair hunion hpower hsep) (omegaOrdinal_mem hM hinf (hsep _))

end PolishSpaceBook.SetTheoryModels
