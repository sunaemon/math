module

public import PolishSpaceBook.SetTheoryInternalOmega
public import PolishSpaceBook.SetTheoryFunctionClosure

@[expose] public section

/-! # Finite sequences as actual set-coded function graphs

Finite graphs whose entries lie in a transitive model belong to that model.
Consequently the internal set of finite sequences of natural numbers contains
all actual finite sequences, although its internal power set need not contain
all external subsets of the natural-number product.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma natOrdinal_injective : Function.Injective (natOrdinal : ℕ → ZFSet.{u}) := by
  intro m n h
  have he := Ordinal.toZFSet_injective h
  exact_mod_cast he

/-- A finite range is in the model whenever all of its entries are. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every value of $f$ belongs to $M$ by transitivity, as does every element of its finite domain.
    Pairing therefore puts each ordered pair of the graph in $M$.
    The empty graph belongs to $M$. Starting there, adjoin the finitely many graph entries one at a time,
    using Pairing and Union to form each insertion. This gives the whole graph $f\in M$.
-/
lemma range_fin_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {n : ℕ} (f : Fin n → ZFSet.{u}) (hf : ∀ i, f i ∈ M) : ZFSet.range f ∈ M := by
  induction n with
  | zero =>
    have he : ZFSet.range f = ∅ := by ext z; simp
    rw [he]
    exact empty_mem_of_infinity hM hinf
  | succ n ih =>
    have he : ZFSet.range f = insert (f 0) (ZFSet.range (fun i : Fin n => f i.succ)) := by
      ext z
      simp only [ZFSet.mem_range, ZFSet.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨i.succ, rfl⟩
    rw [he, ZFSet.insert_eq]
    exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair (hf 0))
      (ih (fun i => f i.succ) (fun i => hf i.succ))

/-- Every actual function on a finite ordinal with internal values is internal. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Finite graphs in a transitive model
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every value of $f$ belongs to $M$ by transitivity, as does every element of its finite domain.
    Pairing therefore puts each ordered pair of the graph in $M$.
    The empty graph belongs to $M$. Starting there, adjoin the finitely many graph entries one at a time,
    using Pairing and Union to form each insertion. This gives the whole graph $f\in M$.
-/
lemma finite_function_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {X f : ZFSet.{u}} (hX : X ∈ M) {n : ℕ} (hf : IsFunc (natOrdinal n) X f) : f ∈ M := by
  have hval (i : Fin n) : ∃ b, pair (natOrdinal i.val) b ∈ f :=
    (hf.2 _ (mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩)).exists
  choose v hv using hval
  have he : f = ZFSet.range (fun i : Fin n => pair (natOrdinal i.val) (v i)) := by
    ext z
    rw [ZFSet.mem_range]
    constructor
    · intro hz
      obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hz)
      obtain ⟨i, hi, rfl⟩ := mem_natOrdinal.mp ha
      have hb : b = v ⟨i, hi⟩ :=
        (hf.2 _ (mem_natOrdinal.mpr ⟨i, hi, rfl⟩)).unique hz (hv ⟨i, hi⟩)
      exact ⟨⟨i, hi⟩, by rw [hb]⟩
    · rintro ⟨i, rfl⟩
      exact hv i
  rw [he]
  apply range_fin_mem hM hinf hpair hunion
  intro i
  have hvX := (ZFSet.pair_mem_prod.mp (hf.1 (hv i))).2
  have hnM : natOrdinal i.val ∈ M := by
    have hzero := empty_mem_of_infinity hM hinf
    have all : ∀ k, natOrdinal k ∈ M := by
      intro k
      induction k with
      | zero => simpa only [natOrdinal_zero] using hzero
      | succ k ih =>
        rw [natOrdinal_succ, ZFSet.insert_eq]
        exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair ih) ih
    exact all i.val
  exact orderedPair_mem hM hpair hnM (hM.mem_trans hvX hX)

/-- A finite natural-number word is its graph on a finite ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    For a finite word $s$, put
    $$e(s):=\{\langle i,s(i)\rangle:i<|s|\}.$$
    Thus a word is represented by its graph, not by an additional object with unspecified membership properties.
-/
def wordGraph (s : List ℕ) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin s.length => pair (natOrdinal i.val) (natOrdinal (s.get i)))

lemma mem_wordGraph {s : List ℕ} {p : ZFSet.{u}} :
    p ∈ wordGraph s ↔ ∃ i : Fin s.length, pair (natOrdinal i.val) (natOrdinal (s.get i)) = p :=
  ZFSet.mem_range

lemma pair_mem_wordGraph {s : List ℕ} {i n : ℕ} :
    pair (natOrdinal i) (natOrdinal n) ∈ wordGraph s ↔ ∃ hi : i < s.length, s[i] = n := by
  rw [mem_wordGraph]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨hi, hn⟩ := ZFSet.pair_inj.mp hj
    have hi' := natOrdinal_injective hi
    refine ⟨hi' ▸ j.isLt, ?_⟩
    simpa only [List.get_eq_getElem, hi'] using natOrdinal_injective hn
  · rintro ⟨hi, hn⟩
    exact ⟨⟨i, hi⟩, by simp only [List.get_eq_getElem, hn]⟩

lemma wordGraph_isFunc (s : List ℕ) :
    IsFunc (natOrdinal s.length) Ordinal.omega0.toZFSet (wordGraph s) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr
      ⟨mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩, mem_omegaOrdinal.mpr ⟨s.get i, rfl⟩⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_natOrdinal.mp ha
    refine ⟨natOrdinal s[i], pair_mem_wordGraph.mpr ⟨hi, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨j, hj⟩ := mem_wordGraph.mp hb
    obtain ⟨he, hval⟩ := ZFSet.pair_inj.mp hj
    have he' := natOrdinal_injective he
    simpa only [List.get_eq_getElem, he'] using hval.symm

/-- Inclusion of finite function graphs is exactly the prefix relation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Graph inclusion recognizes prefixes:
    $$e(s)\IncludedIn e(t)\quad\Longleftrightarrow\quad s\prefixOf t.$$
    Indeed, inclusion requires every coordinate of the first word to occur in the second with the same value,
    and every shorter agreeing word has its graph included in the longer one.
-/
lemma wordGraph_subset_iff {s t : List ℕ} : wordGraph s ⊆ wordGraph t ↔ s.IsPrefix t := by
  rw [List.prefix_iff_getElem]
  constructor
  · intro h
    have hlen : s.length ≤ t.length := by
      by_contra hn
      have hi : t.length < s.length := Nat.lt_of_not_ge hn
      have hp := h (pair_mem_wordGraph.mpr ⟨hi, rfl⟩ :
        pair (natOrdinal t.length) (natOrdinal s[t.length]) ∈ wordGraph s)
      obtain ⟨hi', _⟩ := pair_mem_wordGraph.mp hp
      exact Nat.lt_irrefl _ hi'
    refine ⟨hlen, ?_⟩
    intro i hi
    have hp := h (pair_mem_wordGraph.mpr ⟨hi, rfl⟩ :
      pair (natOrdinal i) (natOrdinal s[i]) ∈ wordGraph s)
    obtain ⟨_, he⟩ := pair_mem_wordGraph.mp hp
    exact he.symm
  · rintro ⟨hlen, he⟩ p hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    apply pair_mem_wordGraph.mpr
    exact ⟨lt_of_lt_of_le i.isLt hlen, (he i.val i.isLt).symm⟩

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    This also proves that $e$ is
    injective, so it is a bijection from $\finseq{\omega}$ onto $T$.
-/
lemma wordGraph_injective : Function.Injective (wordGraph : List ℕ → ZFSet.{u}) := by
  intro s t he
  have hst : s.IsPrefix t := wordGraph_subset_iff.mp (fun _ h => he ▸ h)
  have hts : t.IsPrefix s := wordGraph_subset_iff.mp (fun _ h => he.symm ▸ h)
  exact hst.eq_of_length_le hts.length_le

/-- The domain of a function graph is determined by the graph itself. -/
lemma isFunc_domain_unique {A B X Y f : ZFSet.{u}}
    (hf : IsFunc A X f) (hg : IsFunc B Y f) : A = B := by
  apply ZFSet.ext
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb, _⟩ := hf.2 a ha
    exact (ZFSet.pair_mem_prod.mp (hg.1 hb)).1
  · intro ha
    obtain ⟨b, hb, _⟩ := hg.2 a ha
    exact (ZFSet.pair_mem_prod.mp (hf.1 hb)).1

/-- Recognition of all finite words among arbitrary actual function graphs. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Conversely, a function on a finite ordinal is the graph of the word listing its values in domain order.
-/
lemma exists_wordGraph_of_isFunc {n : ℕ} {f : ZFSet.{u}}
    (hf : IsFunc (natOrdinal n) Ordinal.omega0.toZFSet f) :
    ∃ s : List ℕ, s.length = n ∧ wordGraph s = f := by
  have hvalue (i : Fin n) : ∃ k, pair (natOrdinal i.val) (natOrdinal k) ∈ f := by
    obtain ⟨b, hb, _⟩ := hf.2 _ (mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩)
    obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp (ZFSet.pair_mem_prod.mp (hf.1 hb)).2
    exact ⟨k, hb⟩
  choose v hv using hvalue
  refine ⟨List.ofFn v, List.length_ofFn, ?_⟩
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    simpa using hv ⟨i.val, by simpa using i.isLt⟩
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    obtain ⟨i, hi, rfl⟩ := mem_natOrdinal.mp ha
    have hb : b = natOrdinal (v ⟨i, hi⟩) :=
      (hf.2 _ (mem_natOrdinal.mpr ⟨i, hi, rfl⟩)).unique hp (hv ⟨i, hi⟩)
    rw [hb, pair_mem_wordGraph]
    exact ⟨by simpa using hi, by simp⟩

/-- The ambient set of all finite natural-number function graphs. -/
def finiteSequences : ZFSet.{u} :=
  (ZFSet.powerset (ZFSet.prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet)).sep
    (fun f => ∃ n ∈ Ordinal.omega0.toZFSet, IsFunc n Ordinal.omega0.toZFSet f)

lemma mem_finiteSequences {f : ZFSet.{u}} :
    f ∈ finiteSequences ↔ ∃ s : List ℕ, wordGraph s = f := by
  rw [finiteSequences, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n, hn, hf⟩
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hn
    obtain ⟨s, _, hs⟩ := exists_wordGraph_of_isFunc hf
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    refine ⟨ZFSet.mem_powerset.mpr ?_, natOrdinal s.length, mem_omegaOrdinal.mpr ⟨s.length, rfl⟩,
      wordGraph_isFunc s⟩
    intro p hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr
      ⟨mem_omegaOrdinal.mpr ⟨i.val, rfl⟩, mem_omegaOrdinal.mpr ⟨s.get i, rfl⟩⟩

/-- The standard external finite words and their set-coded graphs are equivalent. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    This also proves that $e$ is
    injective, so it is a bijection from $\finseq{\omega}$ onto $T$.
-/
def wordEquiv : List ℕ ≃ (finiteSequences : ZFSet.{u}) :=
  Equiv.ofBijective (fun s => ⟨wordGraph s, mem_finiteSequences.mpr ⟨s, rfl⟩⟩)
    ⟨fun _ _ he => wordGraph_injective (congrArg Subtype.val he), by
      intro f
      obtain ⟨s, hs⟩ := mem_finiteSequences.mp f.property
      exact ⟨s, Subtype.ext hs⟩⟩

@[simp] lemma wordEquiv_val (s : List ℕ) : (wordEquiv s).val = wordGraph s := rfl

end PolishSpaceBook.SetTheoryModels
