module

public import PolishSpaceBook.LambdaJumpCompiler
public import PolishSpaceBook.LambdaRecursionTheorem

@[expose] public section

/-! # A total self-indexed family of quantified stage programs

The compiler inserts the self-index and stage as numerals in a fixed program.
It constructs syntax without running that program. Self-reference therefore
produces a total numerical index family before any induction proves that its
compiled programs terminate.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A fixed relative template receives q,a,z through the code (q,(a,z)). -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    We first separate the total production of program indices from execution of the programs. For a fixed
    closed relative program $T$, define the two specializations
    $$\begin{aligned}
    T_q&:=\lambdaab{o}{\lambdaab{z}{To(\LambdaNumericPair\,\ChurchNumeral{q}\,z)}},\\
    T_{q,a}&:=\lambdaab{o}{\lambdaab{z}{T_qo(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.
    \end{aligned}$$
    Thus $T_{q,a}$ receives $z$ by passing the code $\NatPair{q}{\NatPair{a}{z}}$ to $T$.
    The syntax constructors compute the code $c(q,a)$ of $T_{q,a}$ jointly in $q,a$. In the specialization
    code recipe, the program-code input may itself be the result of the first specialization; application,
    abstraction, and numeral-code construction are total numerical operations.
-/
theorem double_specialization_indices (P : AlphaTerm) (hP : P.Closed) :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧ ∀ q a,
      Term.closedProgram (f (Nat.pair q a)) = specializePairProgram (specializePairProgram P q) a := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep P
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  have ht : mk T = P := hT
  have hb : mk B = numericalPairTerm := hB
  have hfirst := (pairSpecializationCode_computes T.code B.code).comp (projection_computes true)
  have h := (pairCodeProgram_computes B.code).comp (hfirst.pair (projection_computes false))
  refine ⟨_,_,h,fun q a => ?_⟩
  simp only [Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false]
  rw [← Term.specializePairSyntax_code]
  rw [Term.closedProgram_pairSpecializationCode (Term.specializePairSyntax T B q) B]
  · rw [Term.mk_specializePairSyntax T B hb q,ht]
  · rw [Term.mk_specializePairSyntax T B hb q,ht]
    exact specializePairProgram_closed hP q
  · exact hb

/-- A total numerical code constructor yields a total family containing its own index. -/
theorem exists_self_indexed_family {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) :
    ∃ q, NumericalComputes (Term.closedProgram q) (fun a => f (Nat.pair q a)) := by
  obtain ⟨q,hq⟩ := exists_self_reference (curryNumerical F) (curryNumerical_closed hF.1)
  refine ⟨q,Term.closedProgram_closed q,fun a => ?_⟩
  exact (hq (numeral a) (by rw [numeral_closed]; simp)).trans
    ((curryNumerical_apply hF.1 q a).trans (hF.2 (Nat.pair q a)))

/-- The input template's code is a numerical parameter of the self-index construction. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose the joint specialization map $\kappa$ from §{sec:lambda-pair-tree-programs} once, and put
    $$c(u,v,a):=\kappa(\kappa(u,v),a),\qquad
     f(u,z):=\upsilon\bigl(\xi(c(u,p_1(z),p_2(z)))\bigr).$$
    Here $p_1,p_2$ are the numerical projections and the quantifier-index maps are fixed. Composition gives one
    closed numerical term computing $f$ on paired input; fix a named representative with syntax code $h$.
    The numerical parameter construction in §{sec:lambda-index-recursion} computes
    $$v(u):=p(h,u),$$
    so that $P_{v(u)}$ computes $z\mapsto f(u,z)$ for every numerical input $u$.
    Let $\tau$ be the uniform self-indexed numerical-family map from the same section. Define
    $$q(u):=\tau(v(u)),\qquad d(u,a):=f\bigl(u,\NatPair{q(u)}{a}\bigr).$$
    The self-indexed family theorem proves that $P_{q(u)}$ computes the displayed value for every stage.
    Both maps are total compositions of numerical code constructors. If the input syntax is closed, two
    specializations identify $P_{c(u,q(u),a)}$ with $T_{q(u),a}$. Applying the two quantifier-index transformations
    then proves the decision assertion relative to the second jump of the supplied input function. All fixed representatives
    are chosen before
    the template code is supplied, and no specialized program is executed while generating an index.
    \end{proof}
-/
theorem uniform_compiled_self_families {J : AlphaTerm} {j : ℕ → ℕ}
    (hJ : NumericalComputes J j) :
    ∃ (Q R : AlphaTerm) (q r : ℕ → ℕ), NumericalComputes Q q ∧ NumericalComputes R r ∧
      (∀ u, NumericalComputes (Term.closedProgram (q u)) (fun a => r (Nat.pair u a))) ∧
      ∀ u, (Term.decode u).fv = ∅ → ∀ a, ∃ c,
        Term.closedProgram c = specializePairProgram
          (specializePairProgram (Term.closedProgram u) (q u)) a ∧
        r (Nat.pair u a) = j c := by
  obtain ⟨S,s,hS,hs⟩ := uniform_pair_specialization_indices
  have hu := projection_computes true
  have hq := (projection_computes true).comp (projection_computes false)
  have ha := (projection_computes false).comp (projection_computes false)
  have hfirst := hS.comp (hu.pair hq)
  have hF := hJ.comp (hS.comp (hfirst.pair ha))
  let f (z : ℕ) := j (s (Nat.pair (s (Nat.pair z.unpair.1 z.unpair.2.unpair.1)) z.unpair.2.unpair.2))
  obtain ⟨T,hT⟩ := Quotient.exists_rep (numericalCompose J
    (numericalCompose S (pairNumerical
      (numericalCompose S (pairNumerical (numericalProjectionTerm true)
        (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))))
  have hT' : mk T = _ := hT
  have ht : NumericalComputes (mk T) f := by rw [hT']; exact hF
  have hct : T.fv = ∅ := ht.1
  have hc : (Term.decode T.code).fv = ∅ := by simpa only [Term.decode_code] using hct
  have hp : Term.closedProgram T.code = mk T := by
    simp only [Term.closedProgram,Term.decode_code,hct,ite_true]
  have htc : NumericalComputes (Term.closedProgram T.code) f := by rw [hp]; exact ht
  obtain ⟨N,n,hN,hn⟩ := uniform_numerical_parameter_indices
  let v (u : ℕ) := n (Nat.pair T.code u)
  have hV := hN.comp ((numericalConstant_computes T.code).pair numericalIdentity_computes)
  have hv (u : ℕ) : (Term.decode (v u)).fv = ∅ ∧
      NumericalComputes (Term.closedProgram (v u)) (fun z => f (Nat.pair u z)) := by
    obtain ⟨hcl,_,h⟩ := hn T.code u hc
    exact ⟨hcl,h f htc⟩
  obtain ⟨Q₀,q₀,hQ₀,hq₀⟩ := uniform_self_indexed_family_indices
  let q (u : ℕ) := q₀ (v u)
  have hQ := hQ₀.comp hV
  let r (z : ℕ) := j (s (Nat.pair (s (Nat.pair z.unpair.1 (q z.unpair.1))) z.unpair.2))
  have hR := hJ.comp (hS.comp
    ((hS.comp ((projection_computes true).pair (hQ.comp (projection_computes true)))).pair
      (projection_computes false)))
  refine ⟨_,_,q,r,hQ,hR,?_,fun u huc a => ?_⟩
  · intro u
    have h := hq₀ (v u) (hv u).1 (fun z => f (Nat.pair u z)) (hv u).2
    simpa only [f,r,q,Nat.unpair_pair] using h
  · obtain ⟨hc₁,hp₁⟩ := hs u (q u) huc
    obtain ⟨_,hp₂⟩ := hs (s (Nat.pair u (q u))) a hc₁
    refine ⟨s (Nat.pair (s (Nat.pair u (q u))) a),?_,?_⟩
    · rw [hp₂,hp₁]
    · simp only [r,Nat.unpair_pair]

/-- Uniform universal quantification includes a total generator for the self-index itself. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: corollary
  title: Self-indexed universal families
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use the preceding construction with
    $$f(u,z):=\upsilon(c(u,p_1(z),p_2(z))),\qquad
     r(u,a):=f\bigl(u,\NatPair{q(u)}{a}\bigr).$$
    Omitting the existential-quantifier transformation leaves the same total code construction and self-reference
    reductions. One application of the universal-quantifier compiler proves the decision assertion at one jump.
-/
theorem uniform_universally_quantified_self_families :
    ∃ (Q R : AlphaTerm) (q r : ℕ → ℕ), NumericalComputes Q q ∧ NumericalComputes R r ∧
      (∀ u, NumericalComputes (Term.closedProgram (q u)) (fun a => r (Nat.pair u a))) ∧
      ∀ u, (Term.decode u).fv = ∅ → ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → Prop),
        Decides ε (specializePairProgram (specializePairProgram (Term.closedProgram u) (q u)) a)
          (fun z : ℕ => M z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (r (Nat.pair u a))) (fun n => ∀ b, M n b) := by
  obtain ⟨J,j,hJ,hj⟩ := universal_jump_index_transform
  obtain ⟨Q,R,q,r,hQ,hR,hself,h⟩ := uniform_compiled_self_families hJ
  refine ⟨Q,R,q,r,hQ,hR,hself,fun u hu a ε M hd => ?_⟩
  obtain ⟨c,hc,hr⟩ := h u hu a
  rw [hr]
  exact hj c ε M (by rwa [hc])

/-- The same construction accepts the two-quantifier index transformation. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Self-indexed quantified families
-/
theorem uniform_quantified_self_families :
    ∃ (Q R : AlphaTerm) (q r : ℕ → ℕ), NumericalComputes Q q ∧ NumericalComputes R r ∧
      (∀ u, NumericalComputes (Term.closedProgram (q u)) (fun a => r (Nat.pair u a))) ∧
      ∀ u, (Term.decode u).fv = ∅ → ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → ℕ → Prop),
        Decides ε (specializePairProgram (specializePairProgram (Term.closedProgram u) (q u)) a)
          (fun z : ℕ => M z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) →
        Decides (jumpName (jumpName ε)) (Term.closedProgram (r (Nat.pair u a)))
          (fun n => ∀ t, ∃ b, M n t b) := by
  obtain ⟨J,j,hJ,hj⟩ := forall_exists_jump_index_transform
  obtain ⟨Q,R,q,r,hQ,hR,hself,h⟩ := uniform_compiled_self_families hJ
  refine ⟨Q,R,q,r,hQ,hR,hself,fun u hu a ε M hd => ?_⟩
  obtain ⟨c,hc,hr⟩ := h u hu a
  rw [hr]
  exact hj c ε M (by rwa [hc])

/-- One self-indexed compiler works at every stage and every input parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For a fixed closed template $T$, choose one named representative with code $u$.
    Specializing either construction to this code gives a total index family computed by $P_{q(u)}$.
    Thus the same construction supplies the fixed-template families used below.
-/
theorem quantified_self_family (P : AlphaTerm) (hP : P.Closed) :
    ∃ (q : ℕ) (r : ℕ → ℕ), NumericalComputes (Term.closedProgram q) r ∧
      ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → ℕ → Prop),
        Decides ε (specializePairProgram (specializePairProgram P q) a)
          (fun z : ℕ => M z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2) →
        Decides (jumpName (jumpName ε)) (Term.closedProgram (r a)) (fun n => ∀ t, ∃ b, M n t b) := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep P
  have ht : mk T = P := hT
  have hc : T.fv = ∅ := by
    have h := hP
    rw [← ht] at h
    exact h
  have hu : (Term.decode T.code).fv = ∅ := by simpa only [Term.decode_code] using hc
  have hp : Term.closedProgram T.code = P := by
    simpa only [Term.closedProgram,Term.decode_code,hc,ite_true] using ht
  obtain ⟨Q,R,q,r,hQ,hR,hself,h⟩ := uniform_quantified_self_families
  refine ⟨q T.code,fun a => r (Nat.pair T.code a),hself T.code,fun a ε M hd => ?_⟩
  exact h T.code hu a ε M (by rwa [hp])

/-- The same delayed specialization supports a single universal quantifier. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For a fixed closed template $T$, choose one named representative with code $u$.
    Specializing either construction to this code gives a total index family computed by $P_{q(u)}$.
    Thus the same construction supplies the fixed-template families used below.
-/
theorem universally_quantified_self_family (P : AlphaTerm) (hP : P.Closed) :
    ∃ (q : ℕ) (r : ℕ → ℕ), NumericalComputes (Term.closedProgram q) r ∧
      ∀ (a : ℕ) (ε : ℕ → ℕ) (M : ℕ → ℕ → Prop),
        Decides ε (specializePairProgram (specializePairProgram P q) a)
          (fun z : ℕ => M z.unpair.1 z.unpair.2) →
        Decides (jumpName ε) (Term.closedProgram (r a)) (fun n => ∀ b, M n b) := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep P
  have ht : mk T = P := hT
  have hc : T.fv = ∅ := by
    have h := hP
    rw [← ht] at h
    exact h
  have hu : (Term.decode T.code).fv = ∅ := by simpa only [Term.decode_code] using hc
  have hp : Term.closedProgram T.code = P := by
    simpa only [Term.closedProgram,Term.decode_code,hc,ite_true] using ht
  obtain ⟨Q,R,q,r,hQ,hR,hself,h⟩ := uniform_universally_quantified_self_families
  refine ⟨q T.code,fun a => r (Nat.pair T.code a),hself T.code,fun a ε M hd => ?_⟩
  exact h T.code hu a ε M (by rwa [hp])

end LambdaRelative
end PolishSpaceBook
