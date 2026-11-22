module

public import PolishSpaceBook.LambdaCodeSubstitution
public import PolishSpaceBook.LambdaNumericalFunctions

@[expose] public section

/-! # Uniform indices obtained by substituting into a fixed term

Only the template representative is fixed by choice. The input term is supplied
by its numerical syntax code, and capture-avoiding substitution computes the
output code by beta reduction without executing either term.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Uniform indices from a fixed template
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Use the closed term
    $$V:=\LambdaSubstCode\,\ChurchNumeral{\LambdaSyntaxCode{M}}\,\ChurchNumeral{i}.$$
    The substitution theorem gives $V\ChurchNumeral{u}\to_\beta^*\ChurchNumeral{t(u)}$ for every natural number $u$.
    It constructs the substituted syntax without executing the term decoded from the input. Substitution respects
    alpha-equivalence, so decoding the output gives the asserted alpha-class. If the only possible free variable of
    $M$ is $x_i$ and the inserted term is closed, the free-variable formula for substitution makes the result closed.
    The representative of the fixed template is chosen once; the input syntax is supplied by its numerical code.
-/
theorem uniform_template_indices (M : AlphaTerm) (x : ℕ) :
    ∃ G g, NumericalComputes G g ∧ ∀ u,
      mk (Term.decode (g u)) = M.subst x (mk (Term.decode u)) := by
  obtain ⟨T,hT⟩ := Quotient.exists_rep M
  have ht : mk T = M := hT
  refine ⟨app (app substitutionTerm (numeral T.code)) (numeral x),
    fun u => (T.subst x (Term.decode u)).code,⟨?_,?_⟩,?_⟩
  · exact closed_app (closed_app substitutionTerm_closed (numeral_closed T.code))
      (numeral_closed x)
  · intro u
    simpa only [Term.decode_code] using substitutionTerm_apply T.code x u
  · intro u
    rw [Term.decode_code, ← subst_mk, ht]

theorem uniform_closed_template_indices (M : AlphaTerm) (x : ℕ)
    (hM : ∀ P : AlphaTerm, P.Closed → (M.subst x P).Closed) :
    ∃ G g, NumericalComputes G g ∧ ∀ u, (Term.decode u).fv = ∅ →
      (Term.decode (g u)).fv = ∅ ∧
      Term.closedProgram (g u) = M.subst x (Term.closedProgram u) := by
  obtain ⟨G,g,hG,hg⟩ := uniform_template_indices M x
  refine ⟨G,g,hG,fun u hu => ?_⟩
  have hc : (Term.decode (g u)).fv = ∅ := by
    have h := hM (mk (Term.decode u)) hu
    rw [← hg u] at h
    exact h
  refine ⟨hc,?_⟩
  simp only [Term.closedProgram, hu, hc, ite_true]
  exact hg u

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Uniform indices from a fixed template
-/
theorem uniform_one_variable_template_indices (M : AlphaTerm) (x : ℕ)
    (hM : M.fv ⊆ {x}) :
    ∃ G g, NumericalComputes G g ∧ ∀ u, (Term.decode u).fv = ∅ →
      (Term.decode (g u)).fv = ∅ ∧
      Term.closedProgram (g u) = M.subst x (Term.closedProgram u) := by
  apply uniform_closed_template_indices M x
  intro P hP
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have h := fv_subst_subset M P x hy
  rcases Finset.mem_union.mp h with h | h
  · have he := Finset.mem_erase.mp h
    exact he.1 (Finset.mem_singleton.mp (hM he.2))
  · have hp : P.fv = ∅ := hP
    rw [hp] at h
    exact Finset.notMem_empty y h

/-- Fix the middle argument of the ternary syntax-substitution program. -/
def substitutionAtVariable (x : ℕ) : AlphaTerm :=
  lam 90 (app (app substitutionTerm (var 90)) (numeral x))

theorem substitutionAtVariable_closed (x : ℕ) : (substitutionAtVariable x).Closed := by
  unfold substitutionAtVariable Closed
  simp only [fv_lam, fv_app, fv_var,
    (show substitutionTerm.fv = ∅ from substitutionTerm_closed),
    (show (numeral x).fv = ∅ from numeral_closed x)]
  simp

theorem substitutionAtVariable_apply (x e d : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (substitutionAtVariable x) (numeral e)) (numeral d))
      (numeral ((Term.decode e).subst x (Term.decode d)).code) := by
  have hb : Beta (app (substitutionAtVariable x) (numeral e))
      (app (app substitutionTerm (numeral e)) (numeral x)) := by
    simpa only [substitutionAtVariable, subst_app, subst_var, ite_true,
      subst_closed _ _ _ substitutionTerm_closed, subst_closed _ _ _ (numeral_closed x)] using
      Beta.contract 90 (app (app substitutionTerm (var 90)) (numeral x)) (numeral e)
  exact (Relation.ReflTransGen.single (.app_left _ hb)).trans (substitutionTerm_apply e x d)

/-- The second substitution uses the first computed code as its source code. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The same construction accepts two input codes. Fix a named term $M$ and variable indices $i,j$, and put
    $$M_u:=\SubstLambda{M}{x_i}{\LambdaSyntaxDecode{u}},\qquad
     t(u,v):=\LambdaSyntaxCode{\SubstLambda{M_u}{x_j}{\LambdaSyntaxDecode{v}}}.$$
    The first substitution computes the code of $M_u$ from $u$. Use that computed code as the source argument of
    $\LambdaSubstCode$, with variable index $j$ and replacement code $v$. Numerical projections and composition
    therefore give a single closed term computing $t(u,v)$ on input $\NatPair{u}{v}$. Both substitutions terminate
    for every pair of input codes and execute neither decoded term. Decoding the result gives the two successive
    capture-avoiding substitutions on alpha-classes.
-/
theorem uniform_binary_template_indices (M : AlphaTerm) (x y : ℕ) :
    ∃ G g, NumericalComputes G g ∧ ∀ u v,
      mk (Term.decode (g (Nat.pair u v))) =
        (M.subst x (mk (Term.decode u))).subst y (mk (Term.decode v)) := by
  obtain ⟨U,u,hU,hu⟩ := uniform_template_indices M x
  have h := (hU.comp (projection_computes true)).combine (projection_computes false)
    (substitutionAtVariable_closed y) _ (substitutionAtVariable_apply y)
  refine ⟨_,_,h,fun a b => ?_⟩
  simp only [ite_true, Bool.false_eq_true, ite_false, Nat.unpair_pair, Term.decode_code]
  rw [← subst_mk, hu a]

/-- Reuse the computed intermediate code for a third substitution. -/
theorem uniform_ternary_template_indices (M : AlphaTerm) (x y z : ℕ) :
    ∃ G g, NumericalComputes G g ∧ ∀ u v w,
      mk (Term.decode (g (Nat.pair (Nat.pair u v) w))) =
        ((M.subst x (mk (Term.decode u))).subst y (mk (Term.decode v))).subst z
          (mk (Term.decode w)) := by
  obtain ⟨F,f,hF,hf⟩ := uniform_binary_template_indices M x y
  have h := (hF.comp (projection_computes true)).combine (projection_computes false)
    (substitutionAtVariable_closed z) _ (substitutionAtVariable_apply z)
  refine ⟨_,_,h,fun u v w => ?_⟩
  simp only [ite_true, Bool.false_eq_true, ite_false, Nat.unpair_pair, Term.decode_code]
  rw [← subst_mk, hf u v]

end PolishSpaceBook.NamedLambda.AlphaTerm
