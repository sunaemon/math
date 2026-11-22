module

public import PolishSpaceBook.LambdaRecursiveOrdinals
public import PolishSpaceBook.LambdaListPrefixes
public import PolishSpaceBook.LambdaTemplateIndices

@[expose] public section

/-! # Computing greatest predecessors in finite numerical windows

Zero means that the window contains no predecessor. A selected number b is
encoded by b+1, keeping absence distinct from the possible predecessor zero.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative.WellOrderPresentation
variable {ε : ℕ → ℕ}
attribute [local instance] Classical.propDecidable

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a recursive well-order presentation $W=(D,R)$, with pure numerical decision terms for membership and comparison.
    We use $D,R$ for these terms as well. The constant-zero input parameter can be eliminated by the preceding lemma.
    The following finite procedure is defined for every numerical $a,n$, even if $a$ is outside the domain.
    Start with $\KleenePredMax{a}{0}=0$. At stage $k$, let $r$ be the current state. If $k$ is not in the domain or $kRa$
    fails, keep $r$. Otherwise replace zero by $k+1$; if $r=b+1$, replace it by $k+1$ exactly when $bRk$, and keep it
    otherwise. Thus positive states encode selected predecessors, while zero means that none has been found.
-/
noncomputable def predecessorStep (W : WellOrderPresentation ε) (a k r : ℕ) : ℕ := by
  classical
  exact if W.domain k ∧ W.relation k a then
    if r = 0 ∨ W.relation (r-1) k then k+1 else r
  else r

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a recursive well-order presentation $W=(D,R)$, with pure numerical decision terms for membership and comparison.
    We use $D,R$ for these terms as well. The constant-zero input parameter can be eliminated by the preceding lemma.
    The following finite procedure is defined for every numerical $a,n$, even if $a$ is outside the domain.
    Start with $\KleenePredMax{a}{0}=0$. At stage $k$, let $r$ be the current state. If $k$ is not in the domain or $kRa$
    fails, keep $r$. Otherwise replace zero by $k+1$; if $r=b+1$, replace it by $k+1$ exactly when $bRk$, and keep it
    otherwise. Thus positive states encode selected predecessors, while zero means that none has been found.
-/
noncomputable def predecessorMaximum (W : WellOrderPresentation ε) (a : ℕ) : ℕ → ℕ :=
  primitiveRec 0 (W.predecessorStep a)

private theorem compare (W : WellOrderPresentation ε) {b c : ℕ}
    (hb : W.domain b) (hc : W.domain c) : b = c ∨ W.relation b c ∨ W.relation c b := by
  have h := trichotomous_of W.order (⟨b,hb⟩ : W.Carrier) ⟨c,hc⟩
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inr h)

private theorem transitive (W : WellOrderPresentation ε) {b c d : ℕ}
    (hb : W.domain b) (hc : W.domain c) (hd : W.domain d)
    (hbc : W.relation b c) (hcd : W.relation c d) : W.relation b d :=
  trans_of W.order (a := ⟨b,hb⟩) (b := ⟨c,hc⟩) (c := ⟨d,hd⟩) hbc hcd

/-- The window is the set of natural-number codes strictly below N. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite predecessor maxima
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The membership and comparison bits make $A$ the conjunction of the two tests. The nested numerical comparisons then
    implement precisely the stated update, so numerical primitive recursion proves termination and the output formula.
    For the maximum property, induct on the window size. At the new number, an empty selection becomes that number. If an
    old maximum exists and precedes the new number, transitivity makes the new number a maximum. Otherwise linearity on
    the domain shows that the new number is at or below the old maximum. Rejected numbers leave the invariant unchanged.
    These same update cases prove monotonicity of the selection. A predecessor with code $b$ lies in every window of size
    larger than $b$, so the maximum property proves the final assertion. Only the finite scan is computed; well-foundedness
    is not tested.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Fix a recursive well-order presentation $W=(D,R)$. For each natural number $a$ and bound $n$, inspect the numbers
    $k<n$ with $k\in D$ and $kRa$. Let $\KleenePredMax{a}{n}$ be zero if there are none, and $b+1$ if $b$ is their
    $R$-greatest member. The extra one distinguishes a selected zero from an empty set. The finite scan is computable,
    its selected member can only stay unchanged or increase, and every predecessor of $a$ is eventually at or below the
    selected member. §{sec:lambda-recursive-order-programs} constructs the scan from the membership and comparison terms.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix a recursive well-order presentation $W=(D,R)$, with pure numerical decision terms for membership and comparison.
    We use $D,R$ for these terms as well. The constant-zero input parameter can be eliminated by the preceding lemma.
    The following finite procedure is defined for every numerical $a,n$, even if $a$ is outside the domain.
    Start with $\KleenePredMax{a}{0}=0$. At stage $k$, let $r$ be the current state. If $k$ is not in the domain or $kRa$
    fails, keep $r$. Otherwise replace zero by $k+1$; if $r=b+1$, replace it by $k+1$ exactly when $bRk$, and keep it
    otherwise. Thus positive states encode selected predecessors, while zero means that none has been found.
-/
theorem predecessorMaximum_spec (W : WellOrderPresentation ε) (a N : ℕ) :
    (W.predecessorMaximum a N = 0 ∧ ∀ k < N, ¬ (W.domain k ∧ W.relation k a)) ∨
    ∃ b, W.predecessorMaximum a N = b+1 ∧ b < N ∧ W.domain b ∧ W.relation b a ∧
      ∀ k < N, W.domain k ∧ W.relation k a → k = b ∨ W.relation k b := by
  classical
  induction N with
  | zero => exact Or.inl ⟨rfl,by simp⟩
  | succ N ih =>
    change (W.predecessorStep a N (W.predecessorMaximum a N) = 0 ∧ _) ∨ _
    by_cases hn : W.domain N ∧ W.relation N a
    · rcases ih with ⟨hz,hempty⟩ | ⟨b,hb,hbn,hbd,hba,hmax⟩
      · refine Or.inr ⟨N,?_,by omega,hn.1,hn.2,?_⟩
        · change W.predecessorStep a N (W.predecessorMaximum a N) = N+1
          simp [predecessorStep,hz,hn]
        · intro k hk hka
          by_cases hkN : k < N
          · exact (hempty k hkN hka).elim
          · exact Or.inl (by omega)
      · by_cases hbn' : W.relation b N
        · refine Or.inr ⟨N,?_,by omega,hn.1,hn.2,?_⟩
          · change W.predecessorStep a N (W.predecessorMaximum a N) = N+1
            simp [predecessorStep,hb,hn,hbn']
          · intro k hk hka
            by_cases hkN : k < N
            · rcases hmax k hkN hka with rfl | hkb
              · exact Or.inr hbn'
              · exact Or.inr (transitive W hka.1 hbd hn.1 hkb hbn')
            · exact Or.inl (by omega)
        · refine Or.inr ⟨b,?_,by omega,hbd,hba,?_⟩
          · change W.predecessorStep a N (W.predecessorMaximum a N) = b+1
            simp [predecessorStep,hb,hn,hbn']
          · intro k hk hka
            by_cases hkN : k < N
            · exact hmax k hkN hka
            · have he : k = N := by omega
              subst k
              rcases compare W hbd hn.1 with he | hlt | hgt
              · exact Or.inl he.symm
              · exact (hbn' hlt).elim
              · exact Or.inr hgt
    · have he : W.predecessorMaximum a (N+1) = W.predecessorMaximum a N := by
        change W.predecessorStep a N (W.predecessorMaximum a N) = _
        simp [predecessorStep,hn]
      rcases ih with ⟨hz,hempty⟩ | ⟨b,hb,hbn,hbd,hba,hmax⟩
      · refine Or.inl ⟨he.trans hz,?_⟩
        intro k hk hka
        by_cases hkN : k < N
        · exact hempty k hkN hka
        · have : k = N := by omega
          exact hn (this ▸ hka)
      · refine Or.inr ⟨b,he.trans hb,by omega,hbd,hba,?_⟩
        intro k hk hka
        by_cases hkN : k < N
        · exact hmax k hkN hka
        · have : k = N := by omega
          exact (hn (this ▸ hka)).elim

/-- Once a predecessor has appeared, its running maximum can only stay or increase. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite predecessor maxima
-/
theorem predecessorMaximum_step (W : WellOrderPresentation ε) {a n b : ℕ}
    (hb : W.predecessorMaximum a n = b+1) :
    ∃ c, W.predecessorMaximum a (n+1) = c+1 ∧
      (b = c ∨ W.relation b c) := by
  classical
  change ∃ c, W.predecessorStep a n (W.predecessorMaximum a n) = c+1 ∧ _
  rw [hb]
  by_cases hn : W.domain n ∧ W.relation n a
  · by_cases hr : W.relation b n
    · exact ⟨n,by simp [predecessorStep,hn,hr],Or.inr hr⟩
    · exact ⟨b,by simp [predecessorStep,hn,hr],Or.inl rfl⟩
  · exact ⟨b,by simp [predecessorStep,hn],Or.inl rfl⟩

/-- Every predecessor is eventually at or below the selected predecessor. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite predecessor maxima
-/
theorem predecessorMaximum_cofinal (W : WellOrderPresentation ε) {a b N : ℕ}
    (hb : W.domain b ∧ W.relation b a) (hN : b < N) :
    ∃ c, W.predecessorMaximum a N = c+1 ∧ W.domain c ∧ W.relation c a ∧
      (b = c ∨ W.relation b c) := by
  rcases W.predecessorMaximum_spec a N with ⟨_,h⟩ | ⟨c,hc,_,hcd,hca,hm⟩
  · exact (h b hN hb).elim
  · exact ⟨c,hc,hcd,hca,hm b hN hb⟩

/-- Input to the update program is (a,(k,r)). -/
def maximumStage := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
def maximumState := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the update, extract $a,k,r$ from the numerical input $\NatPair{a}{\NatPair{k}{r}}$ by projections and expand
    $$\begin{aligned}
    A&:=\LambdaMul\,(Dk)\,(R(\LambdaNumericPair\,k\,a)),\\
    B&:=R(\LambdaNumericPair\,(\LambdaPred\,r)\,k),\\
    J&:=\LambdaLeCase{\ChurchNumeral{1}}{A}{
     \bigl(\LambdaLeCase{r}{\ChurchNumeral{0}}{\LambdaSucc\,k}{
     (\LambdaLeCase{\ChurchNumeral{1}}{B}{\LambdaSucc\,k}{r})}\bigr)}{r}.
    \end{aligned}$$
    Use the closed composition term for this update in numerical primitive recursion with initial value zero. Denote the
    resulting closed program by $C$; its input is $\NatPair{a}{n}$.
-/
def predecessorStepProgram (D R : AlphaTerm) : AlphaTerm :=
  numericalIfLe (numericalConstant 1)
    (mulNumerical (numericalCompose D maximumStage)
      (numericalCompose R (pairNumerical maximumStage (numericalProjectionTerm true))))
    (numericalIfLe maximumState (numericalConstant 0)
      (numericalCompose successorTerm maximumStage)
      (numericalIfLe (numericalConstant 1)
        (numericalCompose R (pairNumerical (numericalCompose predecessorTerm maximumState) maximumStage))
        (numericalCompose successorTerm maximumStage) maximumState))
    maximumState

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the update, extract $a,k,r$ from the numerical input $\NatPair{a}{\NatPair{k}{r}}$ by projections and expand
    $$\begin{aligned}
    A&:=\LambdaMul\,(Dk)\,(R(\LambdaNumericPair\,k\,a)),\\
    B&:=R(\LambdaNumericPair\,(\LambdaPred\,r)\,k),\\
    J&:=\LambdaLeCase{\ChurchNumeral{1}}{A}{
     \bigl(\LambdaLeCase{r}{\ChurchNumeral{0}}{\LambdaSucc\,k}{
     (\LambdaLeCase{\ChurchNumeral{1}}{B}{\LambdaSucc\,k}{r})}\bigr)}{r}.
    \end{aligned}$$
    Use the closed composition term for this update in numerical primitive recursion with initial value zero. Denote the
    resulting closed program by $C$; its input is $\NatPair{a}{n}$.
-/
def predecessorMaximumProgram (D R : AlphaTerm) : AlphaTerm :=
  numericalRecursion (numericalConstant 0) (predecessorStepProgram D R)

set_option maxRecDepth 4096 in
 /-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Finite predecessor maxima
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the update, extract $a,k,r$ from the numerical input $\NatPair{a}{\NatPair{k}{r}}$ by projections and expand
    $$\begin{aligned}
    A&:=\LambdaMul\,(Dk)\,(R(\LambdaNumericPair\,k\,a)),\\
    B&:=R(\LambdaNumericPair\,(\LambdaPred\,r)\,k),\\
    J&:=\LambdaLeCase{\ChurchNumeral{1}}{A}{
     \bigl(\LambdaLeCase{r}{\ChurchNumeral{0}}{\LambdaSucc\,k}{
     (\LambdaLeCase{\ChurchNumeral{1}}{B}{\LambdaSucc\,k}{r})}\bigr)}{r}.
    \end{aligned}$$
    Use the closed composition term for this update in numerical primitive recursion with initial value zero. Denote the
    resulting closed program by $C$; its input is $\NatPair{a}{n}$.
-/
theorem predecessorMaximumProgram_computes (W : WellOrderPresentation ε)
    {D R : AlphaTerm}
    (hD : NumericalComputes D (fun n => if W.domain n then 1 else 0))
    (hR : NumericalComputes R (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0)) :
    NumericalComputes (predecessorMaximumProgram D R)
      (fun z => W.predecessorMaximum z.unpair.1 z.unpair.2) := by
  classical
  have hk := (projection_computes true).comp (projection_computes false)
  have hr := (projection_computes false).comp (projection_computes false)
  have hnext := successor_computes.comp hk
  have htest := (hD.comp hk).mul (hR.comp (hk.pair (projection_computes true)))
  have hcompare := hR.comp ((predecessor_computes.comp hr).pair hk)
  have hinner := hr.ifLe (numericalConstant_computes 0) hnext
    ((numericalConstant_computes 1).ifLe hcompare hnext hr)
  have hstep := (numericalConstant_computes 1).ifLe htest hinner hr
  have hstep' : NumericalComputes (predecessorStepProgram D R)
      (fun z => W.predecessorStep z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2) := by
    convert hstep using 1 <;> try rfl
    funext z
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.unpair_pair,Nat.succ_eq_add_one]
    unfold predecessorStep
    by_cases hd : W.domain z.unpair.2.unpair.1 <;>
      by_cases hk : W.relation z.unpair.2.unpair.1 z.unpair.1 <;>
      by_cases hr : z.unpair.2.unpair.2 = 0 <;>
      by_cases hc : W.relation (z.unpair.2.unpair.2-1) z.unpair.2.unpair.1 <;>
      simp [hd,hk,hr,hc]
  simpa only [predecessorMaximumProgram,predecessorMaximum,Nat.unpair_pair] using
    numericalRecursion_computes (numericalConstant_computes 0) hstep'

/-- The zero input parameter is replaced by its closed constant implementation. -/
theorem exists_pure_predecessorMaximum (W : WellOrderPresentation (fun _ => 0)) :
    ∃ C : AlphaTerm, NumericalComputes C
      (fun z => W.predecessorMaximum z.unpair.1 z.unpair.2) := by
  obtain ⟨D,hD⟩ := W.domain_decidable
  obtain ⟨R,hR⟩ := W.relation_decidable
  have hd := hD.toPure (numericalConstant_computes 0)
  have hr := hR.toPure (numericalConstant_computes 0)
  have hdc : NumericalComputes (app D (numericalConstant 0))
      (fun n => if W.domain n then 1 else 0) := by
    refine ⟨hd.1,fun n => ?_⟩
    dsimp only
    split_ifs with hn
    · exact (hd.2 n).1 hn
    · exact (hd.2 n).2 hn
  have hrc : NumericalComputes (app R (numericalConstant 0))
      (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) := by
    refine ⟨hr.1,fun z => ?_⟩
    dsimp only
    split_ifs with hz
    · simpa [Encodable.encode,Encodable.encodeSigma,Nat.pair_unpair] using
        (hr.2 (z.unpair.1,z.unpair.2)).1 hz
    · simpa [Encodable.encode,Encodable.encodeSigma,Nat.pair_unpair] using
        (hr.2 (z.unpair.1,z.unpair.2)).2 hz
  exact ⟨_,W.predecessorMaximumProgram_computes hdc hrc⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem predecessorMaximumProgram_subst (D R P : AlphaTerm) (hP : P.Closed)
    (x : ℕ) (hx : 42 < x) :
    (predecessorMaximumProgram D R).subst x P =
      predecessorMaximumProgram (D.subst x P) (R.subst x P) := by
  have hp (i : ℕ) : i ∉ P.fv := by rw [hP]; simp
  have h9 : 9 ≠ x := by omega
  have h10 : 10 ≠ x := by omega
  have h40 : 40 ≠ x := by omega
  have h41 : 41 ≠ x := by omega
  have h42 : 42 ≠ x := by omega
  simp only [predecessorMaximumProgram, predecessorStepProgram,
    numericalRecursion, uncurryNumerical, numericalCombine, parameterRecursor,
    curryThird, curryNumerical, numericalIfLe, numericalCompose, numericalConstant,
    mulNumerical, pairNumerical, maximumStage, maximumState,
    subst_lam_fresh _ _ 9 x h9 (hp 9), subst_lam_fresh _ _ 10 x h10 (hp 10),
    subst_lam_fresh _ _ 40 x h40 (hp 40), subst_lam_fresh _ _ 41 x h41 (hp 41),
    subst_lam_fresh _ _ 42 x h42 (hp 42), subst_app, chooseLeBody_subst,
    subst_closed _ _ _ recursorTerm_closed, subst_closed _ _ _ numericalPairTerm_closed,
    subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ predecessorTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false),
    subst_closed _ _ _ (numeral_closed 0), subst_closed _ _ _ (numeral_closed 1),
    subst_var, h9, h10, h40, h41, h42, ite_false]

/-- No truth or totality test is made while constructing the selector's index. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform predecessor-selector indices
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Write $C(D,R)$ for the finite-scan program just constructed. Replace its two decision terms by free variables
    $x_{86},x_{87}$ and fix a named representative $M$ of the resulting expression. The two-input substitution
    construction of §{sec:lambda-code-substitution} computes $c(d,r)$ by inserting the terms decoded from $d,r$
    in those two places, in that order. The chosen variables are distinct from the binders introduced by the
    composition and numerical-recursion expressions. When the inserted terms are closed, substitution passes under
    those binders and preserves all closed arithmetic and projection components. The second substitution also
    preserves the first inserted term. Thus the decoded output is alpha-equivalent to $C(P_d,P_r)$.
    The preceding finite-predecessor lemma proves that this is a closed program with the required numerical values.
    Only the two syntactic substitutions are performed while computing the index; the decision programs are run
    later, when the generated program is applied to a numerical input.
-/
theorem uniform_predecessorMaximum_indices :
    ∃ F f, NumericalComputes F f ∧ ∀ W : WellOrderPresentation ε, ∀ d r,
      (Term.decode d).fv = ∅ → (Term.decode r).fv = ∅ →
      NumericalComputes (Term.closedProgram d) (fun n => if W.domain n then 1 else 0) →
      NumericalComputes (Term.closedProgram r)
        (fun z => if W.relation z.unpair.1 z.unpair.2 then 1 else 0) →
      (Term.decode (f (Nat.pair d r))).fv = ∅ ∧
      NumericalComputes (Term.closedProgram (f (Nat.pair d r)))
        (fun z => W.predecessorMaximum z.unpair.1 z.unpair.2) := by
  obtain ⟨F,f,hF,hf⟩ := uniform_binary_template_indices
    (predecessorMaximumProgram (var 86) (var 87)) 86 87
  refine ⟨F,f,hF,fun W d r hd hr hD hR => ?_⟩
  have hdp : AlphaTerm.mk (Term.decode d) = Term.closedProgram d := by
    simp only [Term.closedProgram, hd, ite_true]
  have hrp : AlphaTerm.mk (Term.decode r) = Term.closedProgram r := by
    simp only [Term.closedProgram, hr, ite_true]
  have hm := hf d r
  rw [hdp,hrp,predecessorMaximumProgram_subst _ _ _ (Term.closedProgram_closed d) 86 (by decide),
    predecessorMaximumProgram_subst _ _ _ (Term.closedProgram_closed r) 87 (by decide)] at hm
  norm_num only [subst_var, ite_true, ite_false,
    subst_closed _ _ _ (Term.closedProgram_closed d)] at hm
  have h := W.predecessorMaximumProgram_computes hD hR
  have hc : (Term.decode (f (Nat.pair d r))).fv = ∅ := by
    have hh := h.1
    rw [← hm] at hh
    exact hh
  refine ⟨hc,?_⟩
  have hp : Term.closedProgram (f (Nat.pair d r)) =
      AlphaTerm.mk (Term.decode (f (Nat.pair d r))) := ite_eq_left hc
  rw [hp,hm]
  exact h

end LambdaRelative.WellOrderPresentation
end PolishSpaceBook
