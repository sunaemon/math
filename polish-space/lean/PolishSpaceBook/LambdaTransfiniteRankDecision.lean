module

public import PolishSpaceBook.LambdaRankMatrix
public import PolishSpaceBook.LambdaRankJumpReaders
public import PolishSpaceBook.LambdaHyperarithmeticInclusion

@[expose] public section

/-! # Uniform rank decisions along a recursive well order

A self-indexed total compiler constructs the program indices. Well-founded
induction then verifies each guarded matrix using the already verified lower
programs and the computed readers. No program tests well-foundedness.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaRelative KleeneNotation
namespace RankBound
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
attribute [local instance] Classical.propDecidable

private theorem pure_bit_program {R : ℕ → Prop} (hR : DecidablePredicate (fun _ => 0) R) :
    ∃ P, NumericalComputes P (fun n => if R n then 1 else 0) := by
  obtain ⟨P,hP⟩ := hR
  have h : Computes (fun _ => 0) P (fun n : ℕ => if R n then 1 else 0) :=
    ⟨hP.1,fun n => by simpa only [Encodable.encode_nat] using hP.runs n⟩
  exact ⟨_,h.toNumerical (numericalConstant_computes 0)⟩

private theorem jump_value_congr (A : Set ℕ) {a b : ℕ} {ha : Valid a} {hb : Valid b}
    (h : a = b) : iteratedJump A a ha = iteratedJump A b hb := by
  subst b
  rfl

def StageHolds (W : WellOrderPresentation (fun _ => 0)) (E : ℕ → ℕ → Prop)
    (a : W.Carrier) (s : ℕ) : Prop := Holds W.order ((inferInstance : WellFounded W.order)) E a s

/-- The index compiler is total on all naturals; decision correctness is asserted on D. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Uniform recursive rank decisions
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix the preceding notation assignment $g$ and reader-index function $i$. At stage $a$, the reader
    $P_{i(a)}$ supplied with $\chi_{\IteratedJump{A}{g(a)}}$ computes every lower input function
    $\chi_{(\IteratedJump{A}{g(b)})''}$ for $b\in D$ with $bRa$.
    Construct a fixed matrix program with numerical inputs $q,a,s,t,b$. It returns one when $E(t,s)$ is
    false. Otherwise it returns zero unless $b\in D$ and $bRa$. In the remaining case it evaluates
    $P_q\ChurchNumeral{b}$ to obtain a program index, then runs that program on $t$ with the lower input
    function supplied by the reader. These tests precede the lower-program call.

    Let $c(q,a)$ be the syntax code obtained by inserting $q,a$ into this matrix template. It is a total
    computable function, whether or not the resulting matrix terminates. With the quantifier compilers
    $\xi,\upsilon$ from §{sec:hyperarithmetic-hierarchy}, put
    $$d_q(a):=\upsilon(\xi(c(q,a))).$$
    The self-reference construction in §{sec:lambda-rank-decision-programs} supplies an index $q$ for which
    $$P_q\ChurchNumeral{a}\to_\beta^*\ChurchNumeral{d_q(a)}$$
    for every $a$. This computation constructs only syntax codes. Set $d=d_q$; its totality does not depend
    on termination of any lower-stage decision.

    Fix $A$ and induct on $a$ along $W$. At each predecessor $b$, the induction hypothesis identifies the
    program whose index $P_q$ returns with a decider for $Q_b$. Thus every matrix trial at $a$ terminates,
    and the matrix decides
    $$\neg E(t,s)\ \lor\ \bigl(b\in D\land bRa\land t\in Q_b\bigr).$$
    The compiled program with index $d(a)$ decides its $\forall t\,\exists b$ quantification using two
    jumps of $\chi_{\IteratedJump{A}{g(a)}}$. The bounded-rank recursion identifies this predicate with
    $s\in Q_a$. This proves the induction, including stages with no predecessor. All templates and indices
    were fixed before $A$ was supplied.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    We can now construct the rank-decision indices uniformly. The source relation may have infinite
    branches; the predicate being decided includes well-foundedness below the given node.
-/
theorem recursive_rank_deciders (W : WellOrderPresentation (fun _ => 0)) (E : ℕ → ℕ → Prop)
    (hE : DecidablePredicate (fun _ => 0) (fun z : ℕ => E z.unpair.1 z.unpair.2)) :
    ∃ (G Q : AlphaTerm) (g r : ℕ → ℕ), NumericalComputes G g ∧ NumericalComputes Q r ∧
      ∃ hv : ∀ a : W.Carrier, Valid (g a.val), ∀ (A : Set ℕ) (a : W.Carrier),
        Decides (jumpName (jumpName (characteristic (iteratedJump A (g a.val) (hv a)))))
          (Term.closedProgram (r a.val)) (StageHolds W E a) := by
  obtain ⟨P,hP⟩ := pure_bit_program hE
  have hd := W.domain_decidable.precompNumerical (projection_computes true)
    (g := fun z : ℕ => z.unpair.1) (by simp)
  have hr := W.relation_decidable.precompNumerical numericalIdentity_computes
    (g := fun z : ℕ => (z.unpair.1,z.unpair.2)) (fun z => (Nat.pair_unpair z).symm)
  obtain ⟨C,hC⟩ := pure_bit_program (hd.and hr)
  obtain ⟨G,I,g,i,hG,hI,hv,hi⟩ := recursive_order_twoJump_readers W
  have hM := rankMatrixProgram_closed hP hC hI
  obtain ⟨q,r,hq,hcompile⟩ := quantified_self_family (rankMatrixProgram P C I) hM
  refine ⟨G,Term.closedProgram q,g,r,hG,hq,hv,fun A a₀ => ?_⟩
  apply ((inferInstance : WellFounded W.order)).induction a₀
  intro a ih
  let ε := characteristic (iteratedJump A (g a.val) (hv a))
  let L := fun b t => ∃ hb : W.domain b, StageHolds W E ⟨b,hb⟩ t
  have hm := rankMatrixProgram_decides (e := E) (c := fun b a => W.domain b ∧ W.relation b a)
    hP hC hI q a.val ε L (by
    intro s t b hb
    let b' : W.Carrier := ⟨b,hb.1⟩
    let η := jumpName (jumpName (characteristic (iteratedJump A (g b) (hv b'))))
    have hread (k : ℕ) : OracleRuns ε (Term.closedProgram (i a.val)) (Nat.pair b k) (η k) := by
      have h := (hi a A).2 (Nat.pair b k)
      have hout : predecessorJumpRows W g hv A a (Nat.pair b k) = η k := by
        simp only [predecessorJumpRows,Nat.unpair_pair,dite_eq_left hb]
        apply congrArg (fun B : Set ℕ => jumpName (jumpName (characteristic B)) k)
        exact jump_value_congr A (congrArg g (congrArg Prod.fst (Nat.unpair_pair b k)))
      simpa only [Encodable.encode_nat,hout] using h
    have hbdec := ih b' hb.2
    have hL : L b t ↔ StageHolds W E b' t := by
      constructor
      · rintro ⟨_,h⟩; exact h
      · intro h; exact ⟨hb.1,h⟩
    have hout := lowerRunProgram_runs hI hq a.val s t b _ hread (hbdec.runs t)
    simpa only [propext hL] using hout)
  have ht := hcompile a.val ε (fun s t b => ¬ E t s ∨ ((W.domain b ∧ W.relation b a.val) ∧ L b t)) hm
  have he : (fun s => ∀ t, ∃ b, ¬ E t s ∨ ((W.domain b ∧ W.relation b a.val) ∧ L b t)) =
      StageHolds W E a := by
    funext s
    apply propext
    rw [StageHolds,iff_children]
    constructor
    · intro hs t het
      obtain ⟨b,hb⟩ := hs t
      rcases hb with hne | ⟨⟨hd,hr⟩,⟨hd',hb⟩⟩
      · exact (hne het).elim
      · exact ⟨⟨b,hd⟩,hr,hb⟩
    · intro hs t
      by_cases het : E t s
      · obtain ⟨b,hba,hb⟩ := hs t het
        exact ⟨b.val,Or.inr ⟨⟨b.property,hba⟩,b.property,hb⟩⟩
      · exact ⟨0,Or.inl het⟩
  rw [he] at ht
  exact ht


/-- Each fixed recursive rank layer is computable from an actual iterated jump. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Hyperarithmetic rank layers
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take $A=\emptyset$. The successor equations identify
    $\IteratedJump{\emptyset}{\KleeneSuccIter{g(a)}{2}}$ with $(\IteratedJump{\emptyset}{g(a)})''$.
    The theorem supplies a total decision program relative to this iterated jump. Its output is the
    characteristic function of $Q_a$, as required by the definition of hyperarithmeticity.
    \end{proof}
-/
theorem rank_layer_hyperarithmetic (W : WellOrderPresentation (fun _ => 0)) (E : ℕ → ℕ → Prop)
    (hE : DecidablePredicate (fun _ => 0) (fun z : ℕ => E z.unpair.1 z.unpair.2)) (a : W.Carrier) :
    Hyperarithmetic {s | StageHolds W E a s} := by
  obtain ⟨G,Q,g,r,hG,hQ,hv,hd⟩ := recursive_rank_deciders W E hE
  let b := successorCode (successorCode (g a.val))
  have hb : Valid b := .succ (.succ (hv a))
  have he : characteristic (iteratedJump ∅ b hb) =
      jumpName (jumpName (characteristic (iteratedJump ∅ (g a.val) (hv a)))) := by
    dsimp only [b,jumpName]
    rw [iteratedJump_successor ∅ _ (.succ (hv a)),iteratedJump_successor ∅ _ (hv a)]
  refine ⟨b,hb,Term.closedProgram (r a.val),(hd ∅ a).1,fun s => ?_⟩
  rw [he]
  by_cases hs : StageHolds W E a s
  · simpa only [characteristic,Set.mem_ofPred_eq,ite_eq_left hs,Encodable.encode_nat] using ((hd ∅ a).2 s).1 hs
  · simpa only [characteristic,Set.mem_ofPred_eq,ite_eq_right hs,Encodable.encode_nat] using ((hd ∅ a).2 s).2 hs

end RankBound
end PolishSpaceBook
