module

public import PolishSpaceBook.LambdaMeasuredOpenOperations

@[expose] public section

/-! # Finding an enumerated cylinder containing a computable point
Search the open name and compare each word with a finite prefix of the point.
The returned word is produced by an actual closed numerical lambda term.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def pointEntryHit (p f : ℕ → ℕ) (s : ℕ) : ℕ :=
  if p s = 0 then 0 else
    if p s-1 = NatListCode.encode (seqPrefix f (NatListCode.decode (p s-1)).length) then 1 else 0

def pointEntryHitProgram (P X : AlphaTerm) : AlphaTerm :=
  let W := numericalCompose predecessorTerm P
  let L := numericalCompose listLengthTerm W
  numericalIfZero P (numericalConstant 0)
    (numericalCombine equalityTerm W (numericalCompose (app prefixProgram X) L))

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Finding a cylinder at a computable point
-/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    Let $P$ compute $p$ and let $X$ compute the bits of $x$.
    At stage $s$, skip the entry if $p(s)=0$. Otherwise decode $p(s)-1$ as a binary word and compare it with
    the equally long prefix of $x$. This is a finite calculation. Some comparison succeeds because $x\in U_p$.
    For the terms, use
    $$\begin{aligned}
    D&:=\lambdaab{s}{\LambdaPred(Ps)},\\
    F&:=\lambdaab{s}{\LambdaInputPrefix\,X\,(\LambdaListLength(Ds))},\\
    T&:=\lambdaab{s}{\LambdaZeroTest\,(Ps)\,\ChurchNumeral{0}\,(\LambdaEqual\,(Ds)\,(Fs))},\\
    W&:=\LambdaResultSearch\,
     (\lambdaab{s}{\LambdaZeroTest\,(Ts)\,\ChurchNumeral{1}\,\ChurchNumeral{0}})\,D.
    \end{aligned}$$
    The search test is zero precisely when a nonempty enumeration entry contains the point.
    At the first such stage, $D$ returns the word code, so $W\to_\beta^*\ChurchNumeral{\LambdaListCode{w}}$.
    The entry is one of those defining $U_p$, which proves the required containment.
-/
theorem pointEntryHitProgram_computes {P X : AlphaTerm} {p f : ℕ → ℕ}
    (hp : NumericalComputes P p) (hf : NumericalComputes X f) :
    NumericalComputes (pointEntryHitProgram P X) (pointEntryHit p f) := by
  have hw := predecessor_computes.comp hp
  have hlen := listLength_computes.comp hw
  have hpre : NumericalComputes (app prefixProgram X) (fun k => NatListCode.encode (seqPrefix f k)) :=
    ⟨closed_app prefixProgram_closed hf.1,
      fun k => (prefixProgram_runs f k).apply_numerical prefixProgram_closed hf⟩
  have htest := hw.combine (hpre.comp hlen) equalityTerm_closed
    (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have h := numericalIfZero_computes hp (numericalConstant_computes 0) htest
  change NumericalComputes _ (fun s => if p s = 0 then 0 else
    if p s-1 = NatListCode.encode (seqPrefix f (NatListCode.decode (p s-1)).length) then 1 else 0)
  exact h

theorem pointEntryHit_iff {p : ℕ → ℕ} (hv : ValidOpenName p) (x : ℕ → Bool) (s : ℕ) :
    pointEntryHit p (fun k => (x k).toNat) s ≠ 0 ↔ x ∈ entrySet (p s) := by
  by_cases hz : p s = 0
  · simp [pointEntryHit,entrySet,hz]
  have hb : Binary (p s-1) := (hv s).resolve_left hz
  have he (k : ℕ) : NatListCode.encode (seqPrefix (fun i => (x i).toNat) k) =
      encodeWord (seqPrefix x k) := by simp [encodeWord,seqPrefix,List.map_ofFn,Function.comp_def]
  have hlen : (decodeWord (p s-1)).length = (NatListCode.decode (p s-1)).length := by simp [decodeWord]
  simp only [pointEntryHit,hz,ite_false,he,entrySet]
  constructor
  · intro h
    have hc : p s-1 = encodeWord (seqPrefix x (NatListCode.decode (p s-1)).length) := by
      split_ifs at h with hc
      · exact hc
      · exact (h rfl).elim
    rw [hc,decodeWord_encodeWord]
    exact mem_cyl_seqPrefix _ _
  · intro hx
    have hc := congrArg encodeWord (seqPrefix_eq_of_mem_cyl hx)
    rw [hlen,encodeWord_decodeWord hb] at hc
    simp [hc]

def pointCylinderProgram (P X : AlphaTerm) : AlphaTerm :=
  numericalResultSearch (numericalCompose (pointEntryHitProgram P X) (numericalProjectionTerm false))
    (numericalCompose predecessorTerm P)

/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: statement
  kind: lemma
  title: Finding a cylinder at a computable point
-/
theorem computable_point_cylinder {P X : AlphaTerm} {p : ℕ → ℕ} {x : ℕ → Bool}
    (hp : NumericalComputes P p) (hv : ValidOpenName p)
    (hx : NumericalComputes X (fun k => (x k).toNat)) (hmem : x ∈ namedOpen p) :
    (pointCylinderProgram P X).Closed ∧ ∃ w : List Bool,
      Relation.ReflTransGen Beta (app (pointCylinderProgram P X) (numeral 0)) (numeral (encodeWord w)) ∧
      x ∈ cyl w ∧ cyl w ⊆ namedOpen p := by
  let f := fun k => (x k).toNat
  have hex : ∃ s, pointEntryHit p f s ≠ 0 := by
    obtain ⟨s,hs⟩ := mem_iUnion.mp hmem
    exact ⟨s,(pointEntryHit_iff hv x s).mpr hs⟩
  let s := Nat.find hex
  have hhit := Nat.find_spec hex
  have hs : x ∈ entrySet (p s) := (pointEntryHit_iff hv x s).mp hhit
  have hz : p s ≠ 0 := by intro hz; simp [entrySet,hz] at hs
  have hb : Binary (p s-1) := (hv s).resolve_left hz
  have ht := (pointEntryHitProgram_computes hp hx).comp (projection_computes false)
  have hr := predecessor_computes.comp hp
  refine ⟨numericalResultSearch_closed ht hr,decodeWord (p s-1),?_,?_,?_⟩
  · rw [encodeWord_decodeWord hb]
    exact numericalResultSearch_hit ht hr 0 s (by simpa using hhit)
      (fun k hk => by simpa using not_ne_iff.mp (Nat.find_min hex hk))
  · simpa [entrySet,hz] using hs
  · have hh := subset_iUnion (fun i => entrySet (p i)) s
    simpa only [entrySet,hz,ite_false,namedOpen] using hh

end PolishSpaceBook.LambdaRandomness
