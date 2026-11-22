module

public import PolishSpaceBook.RandomGenericReals
public import PolishSpaceBook.CantorDerivativeCoding
public import PolishSpaceBook.LambdaRealEquality
public import PolishSpaceBook.LambdaRealMetric
public import PolishSpaceBook.LambdaRelativeSearch
public import PolishSpaceBook.LambdaInputPrefixes
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! # Exact finite cylinder measures and lower approximations to open measure

The finite algorithm subtracts overlaps by prefix comparison. Its list fold
returns a numerical function, so the whole calculation uses lambda reduction.
-/
namespace PolishSpaceBook.CantorMeasure
open Set MeasureTheory Filter Topology NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Zero is padding; a positive entry is one plus a binary word code. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $\mu$ be the fair-coin probability measure on $\CantorSpace$. The cylinder calculation in
    §{sec:random-forcing-detail} gives $\mu(\cyl{s})=2^{-|s|}$. We now turn this finite formula into a uniform
    calculation for enumerated open sets. Encode binary words as numerical lists. An enumeration entry $a=0$
    denotes the empty set; an entry $a>0$ denotes the cylinder of the word $\LambdaListDecode{a-1}$.
    A valid entry has only binary digits in that decoded word. Write $V_a$ for the set denoted by an entry and put
    $$U_L:=\bigcup_{a\in L}V_a,\qquad U_p:=\bigcup_n V_{p(n)}$$
    for a finite list $L$ of valid entries and a name $p:\NN\to\NN$ of valid entries.
    Padding and repetitions are allowed. In particular, the constant-zero name denotes the empty open set,
    and the entry $1$ denotes the whole space, because $0$ codes the empty word.
-/
def ValidEntry (a : ℕ) : Prop := a = 0 ∨ Binary (a-1)

def entrySet (a : ℕ) : Set (ℕ → Bool) := if a = 0 then ∅ else cyl (decodeWord (a-1))
def finiteOpen (L : List ℕ) : Set (ℕ → Bool) := ⋃ a ∈ L, entrySet a

@[simp] theorem finiteOpen_nil : finiteOpen [] = ∅ := by simp [finiteOpen]
@[simp] theorem finiteOpen_cons (a : ℕ) (L : List ℕ) :
    finiteOpen (a::L) = entrySet a ∪ finiteOpen L := by ext x; simp [finiteOpen]

theorem isOpen_entrySet (a : ℕ) : IsOpen (entrySet a) := by
  unfold entrySet
  split_ifs <;> first | exact isOpen_empty | exact isOpen_cyl _

theorem isOpen_finiteOpen (L : List ℕ) : IsOpen (finiteOpen L) :=
  isOpen_biUnion (fun a _ => isOpen_entrySet a)

/-- Rational code for the part of a cylinder not yet covered by the list. -/
def avoidCode : List ℕ → ℕ → ℕ
  | [],s => (RationalCode.dyadic (NatListCode.decode s).length).natCode
  | a::L,s => if a = 0 then avoidCode L s else
    if (NatListCode.decode (a-1)).IsPrefix (NatListCode.decode s) then 0 else
    if (NatListCode.decode s).IsPrefix (NatListCode.decode (a-1)) then
      rationalDifferenceCode (Nat.pair (avoidCode L s) (avoidCode L (a-1)))
    else avoidCode L s

private theorem prefix_decode_iff {s t : ℕ} (hs : Binary s) (ht : Binary t) :
    (decodeWord s).IsPrefix (decodeWord t) ↔ (NatListCode.decode s).IsPrefix (NatListCode.decode t) := by
  constructor
  · intro h
    simpa only [decodeWord_map hs,decodeWord_map ht] using h.map Bool.toNat
  · exact decodeWord_prefix

private theorem cylinders_disjoint {s t : ℕ} (hs : Binary s) (ht : Binary t)
    (hst : ¬ (NatListCode.decode s).IsPrefix (NatListCode.decode t))
    (hts : ¬ (NatListCode.decode t).IsPrefix (NatListCode.decode s)) :
    Disjoint (cyl (decodeWord s)) (cyl (decodeWord t)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hxs := seqPrefix_eq_of_mem_cyl hx
  have hxt := seqPrefix_eq_of_mem_cyl hy
  rcases le_total (decodeWord s).length (decodeWord t).length with h | h
  · apply hst
    apply (prefix_decode_iff hs ht).mp
    simpa only [hxs,hxt] using seqPrefix_prefixOf_of_le x h
  · apply hts
    apply (prefix_decode_iff ht hs).mp
    simpa only [hxs,hxt] using seqPrefix_prefixOf_of_le x h

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For a binary word $s$, compute the uncovered mass
    $$G_L(s):=\mu\bigl(\SetDifference{\cyl{s}}{U_L}\bigr).$$
    The empty list gives $G_{[]}(s)=2^{-|s|}$. A padding entry changes nothing:
    $G_{0::L}(s)=G_L(s)$. For $a>0$, put $t:=\LambdaListDecode{a-1}$. Then
    $$G_{a::L}(s)=\begin{cases}
    0,&t\prefixOf s,\\
    G_L(s)-G_L(t),&s\prefixOf t\text{ and }t\notPrefixOf s,\\
    G_L(s),&\text{otherwise}.
    \end{cases}$$
    In the first case the new cylinder covers all of $\cyl{s}$. In the second case,
    $\SetDifference{\cyl{t}}{U_L}\IncludedIn\SetDifference{\cyl{s}}{U_L}$, and removing that measurable subset
    subtracts exactly its measure. In the last case the cylinders are disjoint: two prefixes of the same infinite
    sequence are comparable. This proves the recurrence, including equality of the words in the first case.
    Finally, $\mu(U_L)=1-G_L(\emptySeq)$, since $\cyl{\emptySeq}=\CantorSpace$.
-/
theorem avoidCode_value (L : List ℕ) (hL : ∀ a ∈ L, ValidEntry a) (s : ℕ) (hs : Binary s) :
    rationalPoint (avoidCode L s) = fairCoinProduct.real (cyl (decodeWord s) \ finiteOpen L) := by
  induction L generalizing s with
  | nil =>
    simp only [avoidCode,finiteOpen_nil,sdiff_empty,Measure.real,fairCoinProduct_cyl,decodeWord_length,
      rationalPoint_dyadic,ENNReal.toReal_pow]
    norm_num
  | cons a L ih =>
    have htail : ∀ a ∈ L, ValidEntry a := fun a ha => hL a (List.mem_cons_of_mem _ ha)
    have ha := hL a List.mem_cons_self
    by_cases hz : a = 0
    · simp only [avoidCode,hz,ite_true,finiteOpen_cons,entrySet,empty_union]
      exact ih htail s hs
    · have hb : Binary (a-1) := ha.resolve_left hz
      simp only [avoidCode,hz,ite_false,finiteOpen_cons,entrySet]
      by_cases hts : (NatListCode.decode (a-1)).IsPrefix (NatListCode.decode s)
      · rw [ite_eq_left hts,rationalPoint_zero]
        have hsub := cyl_subset_of_prefix (decodeWord_prefix hts)
        have heq : cyl (decodeWord s) \ (cyl (decodeWord (a-1)) ∪ finiteOpen L) = ∅ := by
          apply Set.sdiff_eq_empty.mpr
          exact hsub.trans subset_union_left
        rw [heq]; simp
      · rw [ite_eq_right hts]
        by_cases hst : (NatListCode.decode s).IsPrefix (NatListCode.decode (a-1))
        · rw [ite_eq_left hst,rationalPoint_difference,ih htail s hs,ih htail (a-1) hb]
          have hsub := cyl_subset_of_prefix (decodeWord_prefix hst)
          have heq : cyl (decodeWord s) \ (cyl (decodeWord (a-1)) ∪ finiteOpen L) =
              (cyl (decodeWord s) \ finiteOpen L) \ (cyl (decodeWord (a-1)) \ finiteOpen L) := by
            ext x; simp only [Set.mem_sdiff,mem_union]; tauto
          rw [heq,measureReal_sdiff (Set.sdiff_subset_sdiff_left hsub)
            ((isOpen_cyl _).measurableSet.diff (isOpen_finiteOpen L).measurableSet)]
        · rw [ite_eq_right hst,ih htail s hs]
          congr 1
          have hd := cylinders_disjoint hs hb hst hts
          ext x
          simp only [Set.mem_sdiff,mem_union]
          have hx : x ∈ cyl (decodeWord s) → x ∉ cyl (decodeWord (a-1)) :=
            fun h => Set.disjoint_left.mp hd h
          tauto

/-- The empty word is the whole space; subtract its uncovered part from one. -/
def finiteMeasureCode (L : List ℕ) : ℕ :=
  rationalDifferenceCode (Nat.pair (RationalCode.dyadic 0).natCode (avoidCode L 0))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite cylinder union measures
-/
theorem finiteMeasureCode_value (L : List ℕ) (hL : ∀ a ∈ L, ValidEntry a) :
    rationalPoint (finiteMeasureCode L) = fairCoinProduct.real (finiteOpen L) := by
  rw [finiteMeasureCode,rationalPoint_difference,rationalPoint_dyadic,avoidCode_value L hL 0]
  · have hc : cyl (decodeWord 0) = (univ : Set (ℕ → Bool)) := by
      simp [decodeWord,NatListCode.decode,cyl,prefixOfSeq]
    rw [hc,measureReal_sdiff (subset_univ _) (isOpen_finiteOpen L).measurableSet]
    simp
  · simp [Binary,NatListCode.decode]

/-- Add one enumerated cylinder to the covered part. `A` is its constant program. -/
def avoidStep (A F : AlphaTerm) : AlphaTerm :=
  let W := numericalCompose predecessorTerm A
  let covers := numericalCompose listPrefixTerm (pairNumerical W numericalIdentity)
  let inside := numericalCompose listPrefixTerm (pairNumerical numericalIdentity W)
  let diff := numericalCompose rationalDifferenceProgram (pairNumerical F (numericalCompose F W))
  numericalIfZero A F (numericalIfZero covers (numericalIfZero inside F diff) (numericalConstant 0))

theorem avoidStep_computes (a : ℕ) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : NumericalComputes (avoidStep (numericalConstant a) F)
      (fun s => if a = 0 then f s else
        if (NatListCode.decode (a-1)).IsPrefix (NatListCode.decode s) then 0 else
        if (NatListCode.decode s).IsPrefix (NatListCode.decode (a-1)) then
          rationalDifferenceCode (Nat.pair (f s) (f (a-1))) else f s) := by
  have hA := numericalConstant_computes a
  have hW := predecessor_computes.comp hA
  have hC := listPrefix_computes.comp (hW.pair numericalIdentity_computes)
  have hI := listPrefix_computes.comp (numericalIdentity_computes.pair hW)
  have hD := rationalDifferenceProgram_computes.comp (hF.pair (hF.comp hW))
  have h := numericalIfZero_computes hA hF
    (numericalIfZero_computes hC (numericalIfZero_computes hI hF hD) (numericalConstant_computes 0))
  convert h using 1
  · rfl
  · funext s
    simp only [Nat.unpair_pair,id_eq]
    split_ifs <;> first | rfl | contradiction

def avoidBase : AlphaTerm := numericalCompose rationalDyadicTerm listLengthTerm

def avoidProgram : List ℕ → AlphaTerm
  | [] => avoidBase
  | a::L => avoidStep (numericalConstant a) (avoidProgram L)

theorem avoidProgram_computes (L : List ℕ) : NumericalComputes (avoidProgram L) (avoidCode L) := by
  induction L with
  | nil => exact rationalDyadic_computes.comp listLength_computes
  | cons a L ih => exact avoidStep_computes a ih

private theorem avoidStep_subst (A F W : AlphaTerm) (x : ℕ) (h40 : 40 ≠ x) (h90 : 90 ≠ x)
    (hW : W.Closed) :
    (avoidStep A F).subst x W = avoidStep (A.subst x W) (F.subst x W) := by
  have hw (n : ℕ) : n ∉ W.fv := by rw [hW]; simp
  simp only [avoidStep,numericalIfZero,numericalApply3,numericalCompose,pairNumerical,numericalCombine,
    subst_lam_fresh _ _ 40 x h40 (hw 40),subst_lam_fresh _ _ 90 x h90 (hw 90),subst_app,
    subst_var,ite_eq_right h40,ite_eq_right h90,
    subst_closed _ _ _ predecessor_computes.1,subst_closed _ _ _ listPrefix_computes.1,
    subst_closed _ _ _ numericalIdentity_computes.1,subst_closed _ _ _ rationalDifferenceProgram_computes.1,
    subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ (numericalConstant_computes 0).1]

def avoidHandler : AlphaTerm := lam 60 (lam 61 (avoidStep (lam 40 (var 60)) (var 61)))

theorem avoidHandler_closed : avoidHandler.Closed := by
  unfold avoidHandler Closed avoidStep numericalIfZero numericalApply3 numericalCompose pairNumerical numericalCombine
  simp only [fv_lam,fv_app,fv_var]
  decide

theorem avoidHandler_apply (a : ℕ) (F : AlphaTerm) (hF : F.Closed) :
    Relation.ReflTransGen Beta (app (app avoidHandler (numeral a)) F)
      (avoidStep (numericalConstant a) F) := by
  have h1 : Beta (app avoidHandler (numeral a))
      (lam 61 (avoidStep (numericalConstant a) (var 61))) := by
    change Beta (app (lam 60 (lam 61 (avoidStep (lam 40 (var 60)) (var 61)))) (numeral a)) _
    convert Beta.contract 60 (lam 61 (avoidStep (lam 40 (var 60)) (var 61))) (numeral a) using 1
    simp only [subst_lam_fresh _ (numeral a) 61 60 (by decide) (by rw [numeral_closed]; simp),
      avoidStep_subst _ _ (numeral a) 60 (by decide) (by decide) (numeral_closed a),
      subst_lam_fresh _ (numeral a) 40 60 (by decide) (by rw [numeral_closed]; simp),subst_var]
    rfl
  have h2 : Beta (app (lam 61 (avoidStep (numericalConstant a) (var 61))) F)
      (avoidStep (numericalConstant a) F) := by
    convert Beta.contract 61 (avoidStep (numericalConstant a) (var 61)) F using 1
    simp only [avoidStep_subst _ _ F 61 (by decide) (by decide) hF,
      subst_closed _ _ _ (numericalConstant_computes a).1,subst_var,ite_true]
  exact (Relation.ReflTransGen.single (.app_left _ h1)).trans (.single h2)

def finiteAvoidFold : AlphaTerm := listFold avoidBase avoidHandler

theorem finiteAvoidFold_apply (L : List ℕ) :
    Relation.ReflTransGen Beta (app finiteAvoidFold (numeral (NatListCode.encode L))) (avoidProgram L) :=
  listFold_apply (avoidProgram_computes []).1 avoidHandler_closed avoidProgram .refl
    (fun a L => avoidHandler_apply a _ (avoidProgram_computes L).1) L

def avoidEmptyProgram : AlphaTerm := lam 40 (app (app finiteAvoidFold (var 40)) (numeral 0))

theorem avoidEmptyProgram_computes : NumericalComputes avoidEmptyProgram
    (fun e => avoidCode (NatListCode.decode e) 0) := by
  have hc : finiteAvoidFold.Closed := listFold_closed (avoidProgram_computes []).1 avoidHandler_closed
  refine ⟨?_,fun e => ?_⟩
  · unfold avoidEmptyProgram Closed
    simp only [fv_lam,fv_app,fv_var]; decide
  · have hs : Beta (app avoidEmptyProgram (numeral e)) (app (app finiteAvoidFold (numeral e)) (numeral 0)) := by
      simpa only [avoidEmptyProgram,subst_app,subst_var,ite_true,subst_closed _ _ _ hc,
        subst_closed _ _ _ (numeral_closed 0)] using
        Beta.contract 40 (app (app finiteAvoidFold (var 40)) (numeral 0)) (numeral e)
    have hf := finiteAvoidFold_apply (NatListCode.decode e)
    rw [NatListCode.encode_decode] at hf
    exact (Relation.ReflTransGen.single hs).trans
      ((beta_steps_app_left hf (numeral 0)).trans ((avoidProgram_computes _).2 0))

def finiteMeasureProgram : AlphaTerm := numericalCompose rationalDifferenceProgram
  (pairNumerical (numericalConstant (RationalCode.dyadic 0).natCode) avoidEmptyProgram)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Here is the lambda implementation. Let $D$ be the numerical rational-subtraction program, formed from rational
    addition and negation, and let $c_1:=\RationalCode{1}{0}{0}$. The list fold returns a function on word codes,
    not a single accumulated number. In the following numerical term bodies, $c,h$ are numerical inputs,
    and $F$ is the function
    already computed for the tail. Expand the abbreviations $C,I,J$ inside $H$:
    $$\begin{aligned}
    Z&:=\lambdaab{c}{\LambdaDyadic(\LambdaListLength\,c)},\\
    C(h,c)&:=\LambdaListPrefix(\LambdaNumericPair\,h\,c),\\
    I(h,F,c)&:=\LambdaZeroTest\,(C(c,h))\,(Fc)\,
     \bigl(D(\LambdaNumericPair\,(Fc)\,(Fh))\bigr),\\
    J(h,F,c)&:=\LambdaZeroTest\,(C(h,c))\,I(h,F,c)\,\ChurchNumeral{0},\\
    H&:=\lambdaab{a}{\lambdaab{F}{\lambdaab{c}{
     \LambdaZeroTest\,a\,(Fc)\,J(\LambdaPred\,a,F,c)}}},\\
    M&:=\lambdaab{v}{D\bigl(\LambdaNumericPair\,\ChurchNumeral{c_1}\,
     ((\LambdaListFold{Z}{H}\,v)\ChurchNumeral{0})\bigr)}.
    \end{aligned}$$
    The prefix routine returns $1$ for a prefix and $0$ otherwise; the zero test chooses its first branch on zero.
    Thus the handler implements the recurrence exactly. Induction on the list, using the list-fold reductions,
    shows that its value is a closed numerical function which, on input $\ChurchNumeral{\LambdaListCode{s}}$,
    computes a rational code for $G_L(s)$ for every binary word $s$.
    The dyadic, prefix, and rational routines all terminate. Applying the resulting function to the empty-word code
    and subtracting from one proves the claim about $M$.
    \end{proof}
-/
theorem finiteMeasureProgram_computes : NumericalComputes finiteMeasureProgram
    (fun e => finiteMeasureCode (NatListCode.decode e)) :=
  rationalDifferenceProgram_computes.comp
    ((numericalConstant_computes _).pair avoidEmptyProgram_computes)

/-- Open-set names permit arbitrarily many empty stages and repeated cylinders. -/
def ValidOpenName (p : ℕ → ℕ) : Prop := ∀ n, ValidEntry (p n)
def namedOpen (p : ℕ → ℕ) : Set (ℕ → Bool) := ⋃ n, entrySet (p n)
def stageOpen (p : ℕ → ℕ) (n : ℕ) : Set (ℕ → Bool) := ⋃ i < n, entrySet (p i)
def lowerMeasureCode (p : ℕ → ℕ) (n : ℕ) : ℕ := finiteMeasureCode (seqPrefix p n)

theorem isOpen_namedOpen (p : ℕ → ℕ) : IsOpen (namedOpen p) :=
  isOpen_iUnion (fun n => isOpen_entrySet (p n))

theorem finiteOpen_prefix (p : ℕ → ℕ) (n : ℕ) : finiteOpen (seqPrefix p n) = stageOpen p n := by
  ext x
  simp [finiteOpen,seqPrefix,stageOpen,Fin.exists_iff]

theorem stageOpen_mono (p : ℕ → ℕ) : Monotone (stageOpen p) := by
  intro n m hnm x hx
  simp only [stageOpen,mem_iUnion] at hx ⊢
  obtain ⟨i,hin,hx⟩ := hx
  exact ⟨i,lt_of_lt_of_le hin hnm,hx⟩

theorem iUnion_stageOpen (p : ℕ → ℕ) : (⋃ n, stageOpen p n) = namedOpen p := by
  ext x
  simp only [stageOpen,namedOpen,mem_iUnion]
  constructor
  · rintro ⟨n,i,_,hx⟩; exact ⟨i,hx⟩
  · rintro ⟨i,hx⟩; exact ⟨i+1,i,by omega,hx⟩

theorem lowerMeasureCode_value {p : ℕ → ℕ} (hp : ValidOpenName p) (n : ℕ) :
    rationalPoint (lowerMeasureCode p n) = fairCoinProduct.real (stageOpen p n) := by
  rw [lowerMeasureCode,finiteMeasureCode_value,finiteOpen_prefix]
  intro a ha
  simp only [seqPrefix,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact hp i

def lowerMeasureProgram : AlphaTerm := mapOutputProgram finiteMeasureProgram prefixProgram

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Read the first $n$ enumeration entries into the list $L_n=(p(0),\ldots,p(n-1))$, with $L_0=[]$, and apply $M$.
    Only these finitely many input queries are used. The closed term
    $$B:=\lambdaab{o}{\lambdaab{n}{M(\LambdaInputPrefix\,o\,n)}}$$
    returns the code $b_p(n)$ with $q_{b_p(n)}=\mu(U_{L_n})$. The finite unions increase and have union $U_p$.
    Monotonicity and continuity from below of the finite measure give the asserted bounds and limit.
    If a closed numerical term computes $p$, substituting it for the input function turns the same calculation into
    ordinary beta reductions. Thus a computable open name gives a computable increasing rational approximation.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    This proposition separates uniform lower computation from uniform Cauchy-name computation. It does not by
    itself exhibit a single computably enumerated open set of noncomputable measure: the two sets in its proof
    have rational measures. For randomness tests, a uniform algorithm for their measures is additional information;
    it cannot be obtained uniformly from their open enumerations.
-/
theorem lowerMeasureProgram_computes : UniformNumericalComputes lowerMeasureProgram lowerMeasureCode := by
  have hp : UniformNumericalComputes prefixProgram
      (fun p n => NatListCode.encode (seqPrefix p n)) := ⟨prefixProgram_closed,prefixProgram_runs⟩
  change UniformNumericalComputes lowerMeasureProgram (fun p n => finiteMeasureCode (seqPrefix p n))
  simpa only [lowerMeasureProgram,NatListCode.decode_encode] using
    hp.map finiteMeasureProgram_computes

theorem lowerMeasureProgram_on_computable {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (app lowerMeasureProgram P) (lowerMeasureCode p) :=
  ⟨closed_app lowerMeasureProgram_computes.1 hp.1,
    fun n => (lowerMeasureProgram_computes.2 p n).apply_numerical lowerMeasureProgram_computes.1 hp⟩

theorem lowerMeasureCode_mono {p : ℕ → ℕ} (hp : ValidOpenName p) :
    Monotone (fun n => rationalPoint (lowerMeasureCode p n)) := by
  intro n m hnm
  dsimp only
  rw [lowerMeasureCode_value hp n,lowerMeasureCode_value hp m]
  exact measureReal_mono (stageOpen_mono p hnm)

theorem lowerMeasureCode_bounds {p : ℕ → ℕ} (hp : ValidOpenName p) (n : ℕ) :
    0 ≤ rationalPoint (lowerMeasureCode p n) ∧
      rationalPoint (lowerMeasureCode p n) ≤ fairCoinProduct.real (namedOpen p) := by
  rw [lowerMeasureCode_value hp n]
  refine ⟨measureReal_nonneg,measureReal_mono ?_⟩
  rw [← iUnion_stageOpen]
  exact subset_iUnion (stageOpen p) n

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: theorem
  title: Computing open measure from below
-/
theorem lowerMeasureCode_tendsto {p : ℕ → ℕ} (hp : ValidOpenName p) :
    Tendsto (fun n => rationalPoint (lowerMeasureCode p n)) atTop
      (𝓝 (fairCoinProduct.real (namedOpen p))) := by
  simp_rw [lowerMeasureCode_value hp]
  have h := (ENNReal.tendsto_toReal (show fairCoinProduct (⋃ n, stageOpen p n) ≠ ⊤ by finiteness)).comp
    (tendsto_measure_iUnion_atTop (μ := fairCoinProduct) (stageOpen_mono p))
  simpa only [iUnion_stageOpen,Function.comp_def,Measure.real] using h

/-- A hypothetical two-sided measure computation, even restricted to computable open names. -/
def ComputesOpenMeasure (P : AlphaTerm) : Prop :=
  ∀ p : ℕ → ℕ, ValidOpenName p → (∃ Q, NumericalComputes Q p) →
    ∃ q : realRepresentation.domain, (∀ n, OracleRuns p P n (q.val n)) ∧
      realRepresentation.toFun q = fairCoinProduct.real (namedOpen p)

def delayedWholeName (N n : ℕ) : ℕ := if n < N then 0 else 1

theorem delayedWholeName_computable (N : ℕ) : ∃ Q, NumericalComputes Q (delayedWholeName N) := by
  have ht := numericalIdentity_computes.combine (numericalConstant_computes N)
    strictLessTerm_closed (fun a b => if a < b then 1 else 0) strictLessTerm_apply
  have h := numericalIfZero_computes ht (numericalConstant_computes 1) (numericalConstant_computes 0)
  refine ⟨_,h.1,fun n => ?_⟩
  by_cases hn : n < N <;> simpa [delayedWholeName,hn] using h.2 n

theorem delayedWholeName_valid (N : ℕ) : ValidOpenName (delayedWholeName N) := by
  intro n
  unfold delayedWholeName
  split_ifs <;> simp [ValidEntry,Binary,NatListCode.decode]

theorem delayedWholeName_open (N : ℕ) : namedOpen (delayedWholeName N) = univ := by
  apply eq_univ_of_forall
  intro x
  apply mem_iUnion.mpr
  refine ⟨N,?_⟩
  simp [delayedWholeName,entrySet,decodeWord,NatListCode.decode,cyl,prefixOfSeq]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Suppose that $P$ is such a program. On the constant-zero enumeration it names measure zero. Its output at
    coordinate $2$ returns a code $c$ after finitely many queries. Choose $N$ larger than all queried coordinates.
    The computable enumeration
    $$p_N(n):=\begin{cases}0,&n<N,\\1,&n\ge N\end{cases}$$
    agrees with that input below $N$, but denotes the whole space. A numerical comparison with the fixed $N$ and
    a zero test compute this enumeration, so it is among the promised inputs. Finite use and output uniqueness
    force the same code $c$ at coordinate $2$ of its output. The two Cauchy error bounds would give
    $$|q_c|\le1/4,\qquad |q_c-1|\le1/4.$$
    This is impossible.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: No uniform exact open measure
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    This proposition separates uniform lower computation from uniform Cauchy-name computation. It does not by
    itself exhibit a single computably enumerated open set of noncomputable measure: the two sets in its proof
    have rational measures. For randomness tests, a uniform algorithm for their measures is additional information;
    it cannot be obtained uniformly from their open enumerations.
-/
theorem no_uniform_open_measure (P : AlphaTerm) : ¬ ComputesOpenMeasure P := by
  intro hP
  have hz : ValidOpenName (fun _ => 0) := fun _ => Or.inl rfl
  obtain ⟨q₀,hq₀,hv₀⟩ := hP (fun _ => 0) hz ⟨_,numericalConstant_computes 0⟩
  have hval₀ : realRepresentation.toFun q₀ = 0 := by
    simpa [namedOpen,entrySet] using hv₀
  obtain ⟨N,hN⟩ := (hq₀ 2).finite_use
  obtain ⟨q₁,hq₁,hv₁⟩ := hP (delayedWholeName N) (delayedWholeName_valid N) (delayedWholeName_computable N)
  have hval₁ : realRepresentation.toFun q₁ = 1 := by
    simpa [delayedWholeName_open] using hv₁
  have heq : q₁.val 2 = q₀.val 2 := (hq₁ 2).output_unique
    (hN (delayedWholeName N) (fun n hn => ite_eq_left hn))
  have h₀ := cauchyRepresentation_dist_le rationalPoint q₀ 2
  have h₁ := cauchyRepresentation_dist_le rationalPoint q₁ 2
  change dist (rationalPoint (q₀.val 2)) (realRepresentation.toFun q₀) ≤ _ at h₀
  change dist (rationalPoint (q₁.val 2)) (realRepresentation.toFun q₁) ≤ _ at h₁
  rw [hval₀,Real.dist_eq,abs_le] at h₀
  rw [hval₁,heq,Real.dist_eq,abs_le] at h₁
  norm_num at h₀ h₁
  linarith

/-- A strict lower bound is witnessed by a finite stage. -/
theorem exists_stage_above_iff {p : ℕ → ℕ} (hp : ValidOpenName p) (r : ℝ) :
    (∃ n, r < rationalPoint (lowerMeasureCode p n)) ↔ r < fairCoinProduct.real (namedOpen p) := by
  constructor
  · rintro ⟨n,hn⟩; exact hn.trans_le (lowerMeasureCode_bounds hp n).2
  · intro h
    exact ((lowerMeasureCode_tendsto hp).eventually (eventually_gt_nhds h)).exists

def lowerBoundTest : AlphaTerm := mapOutputProgram rationalLessTerm
  (pairOutputProgram (liftNumericalProgram (numericalProjectionTerm true))
    (reindexProgram lowerMeasureProgram (numericalProjectionTerm false)))

theorem lowerBoundTest_computes : UniformNumericalComputes lowerBoundTest
    (fun p z => if (RationalCode.ofNat z.unpair.1).value <
      (RationalCode.ofNat (lowerMeasureCode p z.unpair.2)).value then 1 else 0) := by
  simpa only [lowerBoundTest,Nat.unpair_pair,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false] using
    (((projection_computes true).uniform).pair
      (lowerMeasureProgram_computes.reindex (projection_computes false))).map rationalLess_computes

def lowerBoundSearch : AlphaTerm := relativeSearchProgram lowerBoundTest

theorem lowerBoundSearch_closed : lowerBoundSearch.Closed :=
  relativeSearchProgram_closed lowerBoundTest_computes.1

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For the strict comparison, search stages $n$ using the total test
    $$T:=\lambdaab{o}{\lambdaab{z}{\LambdaRationalLess\bigl(\LambdaNumericPair\,
     (\LambdaNumericProjection{1}z)\,(Bo(\LambdaNumericProjection{2}z))\bigr)}}.$$
    On input $\NatPair{r}{n}$ it returns $1$ exactly when $q_r<q_{b_p(n)}$. Apply $\LambdaRelativeSearch{T}$.
    Every stage terminates, and the bounds and limit prove
    $$q_r<\mu(U_p)\quad\Longleftrightarrow\quad\exists n\ (q_r<q_{b_p(n)}).$$
    The search therefore returns one exactly in the claimed case, with no numerical output otherwise.
    \end{proof}
-/
theorem lowerBoundSearch_runs_iff {p : ℕ → ℕ} (hp : ValidOpenName p) (r m : ℕ) :
    OracleRuns p lowerBoundSearch r m ↔ m = 1 ∧ rationalPoint r < fairCoinProduct.real (namedOpen p) := by
  have ht : LambdaRelative.Computes p lowerBoundTest (fun z : ℕ =>
      if (RationalCode.ofNat z.unpair.1).value <
        (RationalCode.ofNat (lowerMeasureCode p z.unpair.2)).value then 1 else 0) :=
    ⟨lowerBoundTest_computes.1,lowerBoundTest_computes.2 p⟩
  rw [lowerBoundSearch,relativeSearchProgram_runs_iff ht]
  have hc (n : ℕ) :
      (if (RationalCode.ofNat r).value < (RationalCode.ofNat (lowerMeasureCode p n)).value
        then 1 else 0 : ℕ) ≠ 0 ↔ rationalPoint r < rationalPoint (lowerMeasureCode p n) := by
    simp only [rationalPoint,Rat.cast_lt]
    split_ifs <;> simp_all
  simp only [Nat.unpair_pair,hc,exists_stage_above_iff hp]

end PolishSpaceBook.CantorMeasure
