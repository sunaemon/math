module

public import PolishSpaceBook.LambdaRelativePredicates
public import PolishSpaceBook.LambdaProgramSpecialization

@[expose] public section

/-! # Specializing a relative predicate family on numerical syntax codes

The code transformation is itself computed by a closed numerical lambda
term. It inserts a Church numeral in a fixed named template and preserves
the original input parameter.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def specializePairProgram (P : AlphaTerm) (i : ℕ) : AlphaTerm :=
  lam 1 (lam 2 (app (app P (var 1)) (app (app numericalPairTerm (numeral i)) (var 2))))

theorem specializePairProgram_closed {P : AlphaTerm} (hP : P.Closed) (i : ℕ) :
    (specializePairProgram P i).Closed := by
  unfold specializePairProgram Closed
  simp only [fv_lam,fv_app,fv_var,(show P.fv = ∅ from hP),
    (show numericalPairTerm.fv = ∅ from numericalPairTerm_closed),
    (show (numeral i).fv = ∅ from numeral_closed i)]
  decide

theorem specializePairProgram_start {P : AlphaTerm} (hP : P.Closed)
    (ε : ℕ → ℕ) (i n : ℕ) :
    Relation.ReflTransGen (OracleStep ε)
      (app (app (specializePairProgram P i) (var 0)) (numeral n))
      (app (app P (var 0)) (numeral (Nat.pair i n))) := by
  have h₁ : Beta (app (specializePairProgram P i) (var 0))
      (lam 2 (app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (var 2)))) := by
    have he : (lam 2 (app (app P (var 1)) (app (app numericalPairTerm (numeral i)) (var 2)))).subst 1 (var 0) =
        lam 2 (app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (var 2))) := by
      rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
      simp [subst_app,subst_var,subst_closed _ _ _ hP,
        subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed i)]
    rw [← he]
    exact Beta.contract 1 _ _
  have h₂ : Beta
      (app (lam 2 (app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (var 2)))) (numeral n))
      (app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (numeral n))) := by
    have he : (app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (var 2))).subst 2 (numeral n) =
        app (app P (var 0)) (app (app numericalPairTerm (numeral i)) (numeral n)) := by
      simp [subst_app,subst_var,subst_closed _ _ _ hP,
        subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed i)]
    rw [← he]
    exact Beta.contract 2 _ _
  exact (Relation.ReflTransGen.tail (.single (.beta (.app_left _ h₁))) (.beta h₂)).trans
    (oracle_steps_app_right _ (beta_steps_oracle (numericalPairTerm_apply i n)))

theorem specializePairProgram_runs {P : AlphaTerm} (hP : P.Closed)
    {ε : ℕ → ℕ} {i n m : ℕ} (h : OracleRuns ε P (Nat.pair i n) m) :
    OracleRuns ε (specializePairProgram P i) n m :=
  (specializePairProgram_start hP ε i n).trans h

/-- Specialization preserves divergence as well as every numerical output. -/
theorem specializePairProgram_runs_iff {P : AlphaTerm} (hP : P.Closed)
    (ε : ℕ → ℕ) (i n m : ℕ) :
    OracleRuns ε (specializePairProgram P i) n m ↔ OracleRuns ε P (Nat.pair i n) m :=
  ⟨oracle_numeral_after_reduction (specializePairProgram_start hP ε i n),
    specializePairProgram_runs hP⟩

/-- Application and abstraction constructors applied to two computed syntax codes. -/
def codeTagProgram (t : ℕ) (F G : AlphaTerm) : AlphaTerm := numericalCombine (taggedPairCodeTerm t) F G

theorem codeTagProgram_computes {F G : AlphaTerm} {f g : ℕ → ℕ}
    (hF : NumericalComputes F f) (hG : NumericalComputes G g) (t : ℕ) :
    NumericalComputes (codeTagProgram t F G) (fun n => 3 * Nat.pair (f n) (g n) + t) :=
  hF.combine hG (taggedPairCodeTerm_closed t) _ (taggedPairCodeTerm_apply t)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For specialization, choose fixed named representatives of a closed family decider $P$ and the numerical-pairing
    term, with syntax codes $u,\beta$. Use binder names $x_1,x_2$, whose variable codes are $3,6$. With the application
    and abstraction code constructors
    $$\operatorname{app}(a,c)=3\NatPair{a}{c}+1,\qquad
    \operatorname{lam}(k,a)=3\NatPair{k}{a}+2,$$
    the specialized program has code
    $$\begin{aligned}
    f(i)=\operatorname{lam}\bigl(1,\operatorname{lam}\bigl(2,
     &\operatorname{app}\bigl(\operatorname{app}(u,3),\\
     &\operatorname{app}(\operatorname{app}(\beta,\LambdaSyntaxCode{\ChurchNumeral{i}}),6)\bigr)\bigr)\bigr).
    \end{aligned}$$
    This is exactly the code of $\lambdaab{o}{\lambdaab{z}{Po(\LambdaNumericPair\,\ChurchNumeral{i}\,z)}}$ with
    $o=x_1$ and $z=x_2$.
-/
def pairSpecializationCode (u b i : ℕ) : ℕ :=
  3 * Nat.pair 1 (3 * Nat.pair 2
    (3 * Nat.pair (3 * Nat.pair u 3 + 1)
      (3 * Nat.pair (3 * Nat.pair b (Term.churchNumeral i).code + 1) 6 + 1) + 1) + 2) + 2

def pairSpecializationCodeProgram (u b : ℕ) : AlphaTerm :=
  codeTagProgram 2 (numericalConstant 1) (codeTagProgram 2 (numericalConstant 2)
    (codeTagProgram 1 (codeTagProgram 1 (numericalConstant u) (numericalConstant 3))
      (codeTagProgram 1 (codeTagProgram 1 (numericalConstant b) numeralCodeTerm) (numericalConstant 6))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Computed specialization of relative predicates
-/
theorem pairSpecializationCode_computes (u b : ℕ) :
    NumericalComputes (pairSpecializationCodeProgram u b) (pairSpecializationCode u b) := by
  have hn : NumericalComputes numeralCodeTerm (fun i => (Term.churchNumeral i).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  exact codeTagProgram_computes (numericalConstant_computes 1)
    (codeTagProgram_computes (numericalConstant_computes 2)
      (codeTagProgram_computes
        (codeTagProgram_computes (numericalConstant_computes u) (numericalConstant_computes 3) 1)
        (codeTagProgram_computes
          (codeTagProgram_computes (numericalConstant_computes b) hn 1) (numericalConstant_computes 6) 1) 1) 2) 2

end PolishSpaceBook.NamedLambda.AlphaTerm
namespace PolishSpaceBook.NamedLambda.Term
open AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To recover the original parameter bits, use the closed terms
    $$\begin{aligned}
    Q&:=\lambdaab{o}{\lambdaab{z}{o(p_1(p_1z))}},\qquad P:=\LambdaRelativeSearch{Q},\\
    S_n&:=\lambdaab{o}{\lambdaab{t}{Po(\LambdaNumericPair\,\ChurchNumeral{n}\,t)}}.
    \end{aligned}$$
    On input $\NatPair{\NatPair{n}{t}}{k}$, the trial $Q$ returns $\varepsilon(n)$ independently of $t,k$.
    Apply the syntax-code construction in §{sec:lambda-pair-tree-programs} to this fixed $P$: it gives
    an index $f(n)$ for $S_n$ and a closed numerical lambda term $F$ computing $f$.
    The same code construction applies to a partial program; totality was needed for the decision conclusion,
    not for constructing the specialized syntax. Both $F$ and $f$ are independent of $\varepsilon$.
-/
def specializePairSyntax (P B : Term) (i : ℕ) : Term :=
  .lam 1 (.lam 2 (.app (.app P (.var 1)) (.app (.app B (churchNumeral i)) (.var 2))))

theorem specializePairSyntax_code (P B : Term) (i : ℕ) :
    (specializePairSyntax P B i).code = pairSpecializationCode P.code B.code i := rfl

theorem mk_specializePairSyntax (P B : Term) (hB : mk B = numericalPairTerm) (i : ℕ) :
    mk (specializePairSyntax P B i) = specializePairProgram (mk P) i := by
  change AlphaTerm.lam 1 (AlphaTerm.lam 2 (AlphaTerm.app (AlphaTerm.app (mk P) (AlphaTerm.var 1))
    (AlphaTerm.app (AlphaTerm.app (mk B) (mk (churchNumeral i))) (AlphaTerm.var 2)))) = _
  rw [hB,mk_churchNumeral]
  rfl

theorem closedProgram_pairSpecializationCode (P B : Term) (hP : (mk P).Closed)
    (hB : mk B = numericalPairTerm) (i : ℕ) :
    closedProgram (pairSpecializationCode P.code B.code i) = specializePairProgram (mk P) i := by
  have hm := mk_specializePairSyntax P B hB i
  have hc : (specializePairSyntax P B i).fv = ∅ := by
    change (mk (specializePairSyntax P B i)).fv = ∅
    rw [hm]
    exact specializePairProgram_closed hP i
  rw [← specializePairSyntax_code]
  simp only [closedProgram,decode_code,hc,ite_true,hm]
end PolishSpaceBook.NamedLambda.Term

namespace PolishSpaceBook.LambdaRelative
open NamedLambda NamedLambda.AlphaTerm
universe u
set_option maxRecDepth 4096

/-- Both the old program code and the specialized argument may vary. -/
def pairCodeProgram (b : ℕ) : AlphaTerm :=
  codeTagProgram 2 (numericalConstant 1) (codeTagProgram 2 (numericalConstant 2)
    (codeTagProgram 1 (codeTagProgram 1 (numericalProjectionTerm true) (numericalConstant 3))
      (codeTagProgram 1 (codeTagProgram 1 (numericalConstant b)
        (numericalCompose numeralCodeTerm (numericalProjectionTerm false))) (numericalConstant 6))))

theorem pairCodeProgram_computes (b : ℕ) : NumericalComputes (pairCodeProgram b)
    (fun z => pairSpecializationCode z.unpair.1 b z.unpair.2) := by
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have h := codeTagProgram_computes (numericalConstant_computes 1)
      (codeTagProgram_computes (numericalConstant_computes 2)
        (codeTagProgram_computes
          (codeTagProgram_computes (projection_computes true) (numericalConstant_computes 3) 1)
          (codeTagProgram_computes
            (codeTagProgram_computes (numericalConstant_computes b)
              (hn.comp (projection_computes false)) 1) (numericalConstant_computes 6) 1) 1) 2) 2

  refine ⟨h.1,fun z => ?_⟩
  simpa only [pairCodeProgram,pairSpecializationCode,ite_true,Bool.false_eq_true,ite_false] using h.2 z


/-- The program code and the inserted numerical parameter are both inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The source program code may also be supplied as an input. Keep only the representative of numerical pairing
    fixed. In the preceding code recipe, replace the constant source code by the first input projection and compute
    the inserted numeral code from the second projection. This gives a total numerical map $\Pair{u}{a}\mapsto \kappa(u,a)$.
    Whenever $u$ decodes to a closed term, its output is the syntax code of a closed term satisfying
    $$P_{\kappa(u,a)}=\lambdaab{o}{\lambdaab{z}{P_uo(\LambdaNumericPair\,\ChurchNumeral{a}\,z)}}.$$
    Here $o=x_1$ and $z=x_2$. This identity does not require the source program to terminate. The index computation
    constructs syntax and is total on every pair of natural-number inputs.
-/
theorem uniform_pair_specialization_indices :
    ∃ F f, NumericalComputes F f ∧ ∀ u a, (Term.decode u).fv = ∅ →
      (Term.decode (f (Nat.pair u a))).fv = ∅ ∧
      Term.closedProgram (f (Nat.pair u a)) = specializePairProgram (Term.closedProgram u) a := by
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  have hb : mk B = numericalPairTerm := hB
  refine ⟨_,_,pairCodeProgram_computes B.code,fun u a hu => ?_⟩
  simp only [Nat.unpair_pair]
  have hd : Term.decode (pairSpecializationCode u B.code a) =
      Term.specializePairSyntax (Term.decode u) B a := by
    simpa only [Term.specializePairSyntax_code, Term.code_decode] using
      Term.decode_code (Term.specializePairSyntax (Term.decode u) B a)
  have hm := Term.mk_specializePairSyntax (Term.decode u) B hb a
  have hc : (Term.decode (pairSpecializationCode u B.code a)).fv = ∅ := by
    rw [hd]
    have h := specializePairProgram_closed (P := mk (Term.decode u)) hu a
    rw [← hm] at h
    exact h
  refine ⟨hc,?_⟩
  have hp : Term.closedProgram u = mk (Term.decode u) := ite_eq_left hu
  simpa only [Term.code_decode, hp] using
    Term.closedProgram_pairSpecializationCode (Term.decode u) B hu hb a

theorem Decides.specializePair {α : Type u} [Encodable α] {ε : ℕ → ℕ} {P : AlphaTerm}
    {R : ℕ → α → Prop} (hP : Decides ε P (fun z : ℕ × α => R z.1 z.2)) (i : ℕ) :
    Decides ε (specializePairProgram P i) (R i) := by
  refine ⟨specializePairProgram_closed hP.1 i,fun a => ⟨?_,?_⟩⟩
  · intro h
    exact specializePairProgram_runs hP.1 ((hP.2 (i,a)).1 h)
  · intro h
    exact specializePairProgram_runs hP.1 ((hP.2 (i,a)).2 h)

/-- Specialization of a jointly decidable family is a computed map of indices. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Fix a closed family decider $P$. Insert the numeral for $i$ into the template
    $$\lambdaab{o}{\lambdaab{z}{Po(\LambdaNumericPair\,\ChurchNumeral{i}\,z)}}.$$
    Two outer beta steps and numerical pairing reduce this program to the family decision on the pair of $i$ and
    the node code. The syntax-code constructors and numeral-code program compute the code of this template from
    $i$, without querying $\varepsilon$. This is the required function $f$. The preceding theorem gives the body
    identity. The concrete code recipe and the finite-test program are detailed in §{sec:lambda-pair-tree-programs}.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Compute the numeral code with $\LambdaNumeralCodeProgram$, the four application codes with
    $\LambdaTaggedCode{1}$, and the two abstraction codes with $\LambdaTaggedCode{2}$. Pointwise composition of these
    closed numerical programs gives a closed term computing $f$. The coding inverses recover the stated template;
    its only added variables are bound, so its code denotes the intended closed program. On a valid input code,
    two beta contractions expose the family decider applied to a numerically paired input. Pairing supplies the
    exact family code and the original decider supplies its answer. The parameter remains unchanged throughout.
-/
theorem DecidablePredicate.specialized_indices {α : Type u} [Encodable α]
    {ε : ℕ → ℕ} {R : ℕ → α → Prop}
    (hR : DecidablePredicate ε (fun z : ℕ × α => R z.1 z.2)) :
    ∃ f : ℕ → ℕ, (∃ F, NumericalComputes F f) ∧
      ∀ i, Decides ε (Term.closedProgram (f i)) (R i) := by
  obtain ⟨P,hP⟩ := hR
  obtain ⟨U,hU⟩ := Quotient.exists_rep P
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  have hu : mk U = P := hU
  have hb : mk B = numericalPairTerm := hB
  refine ⟨pairSpecializationCode U.code B.code,⟨_,pairSpecializationCode_computes _ _⟩,fun i => ?_⟩
  rw [Term.closedProgram_pairSpecializationCode U B (hu.symm ▸ hP.1) hb i,hu]
  exact hP.specializePair i
end PolishSpaceBook.LambdaRelative
