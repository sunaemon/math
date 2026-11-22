module

public import PolishSpaceBook.FirstOrderEffectiveSyntax
public import PolishSpaceBook.LambdaBoundedProducts

@[expose] public section

/-! # A concrete finite bound for general quantifier witnesses

A nonvacuous replacement contributes its free names and its entire syntax
size to the substituted formula. Its canonical term encoding uses only zero
for bound names in closed symbol tags. These facts give a numerical search
bound even when the observed target uses arbitrary alpha-renamed binders.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding (LTerm tag)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace QuantifierBounds

/-- Every variable name, whether bound or free, is at most the bound. -/
def NamesLe (k : ℕ) : LTerm → Prop
  | .var x => x ≤ k
  | .app a b => NamesLe k a ∧ NamesLe k b
  | .lam x a => x ≤ k ∧ NamesLe k a

theorem tag_namesLe (k n : ℕ) : NamesLe k (tag n) := by
  induction n with
  | zero => simp [FirstOrderLambdaEncoding.tag, NamesLe]
  | succ n ih => exact ⟨Nat.zero_le _, ih⟩

theorem vector_namesLe {n : ℕ} (ts : Fin n → LTerm) (k : ℕ)
    (h : ∀ i, NamesLe k (ts i)) : NamesLe k (encodeVector ts) := by
  induction n with
  | zero => exact tag_namesLe k 9
  | succ n ih => exact ⟨h 0, ih _ (fun i => h i.succ)⟩

theorem encodeTerm_namesLe (t : L.Term ℕ) (k : ℕ)
    (h : ∀ x ∈ t.varFinset, x ≤ k) : NamesLe k (S.encodeTerm t) := by
  induction t with
  | var x => exact h x (by simp)
  | func f ts ih =>
    refine ⟨tag_namesLe k 8, tag_namesLe _ _, vector_namesLe _ k ?_⟩
    intro i
    exact ih i (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Here are explicit finite bounds for the witnesses that the input does not supply. For a raw syntax code $a$, the
    decoded term has at most $2a+1$ nodes, and every free variable index is at most $a$.
-/
theorem free_name_le_code (A : LTerm) (x : ℕ) (hx : x ∈ A.fv) : x ≤ A.code := by
  induction A with
  | var y =>
    have hxy : x = y := by simpa [Term.fv] using hx
    subst x
    simp only [Term.code]
    omega
  | app A B ihA ihB =>
    simp only [Term.fv, Finset.mem_union] at hx
    rcases hx with ha | hb
    · exact (ihA ha).trans (by have := Nat.left_le_pair A.code B.code; simp only [Term.code]; omega)
    · exact (ihB hb).trans (by have := Nat.right_le_pair A.code B.code; simp only [Term.code]; omega)
  | lam y A ih =>
    have ha := (Finset.mem_erase.mp hx).2
    exact (ih ha).trans (by have := Nat.right_le_pair y A.code; simp only [Term.code]; omega)

theorem nodes_le_code (A : LTerm) : A.nodes ≤ 2 * A.code + 1 := by
  induction A with
  | var x => simp [Term.nodes, Term.code]
  | app A B ihA ihB =>
    have := Nat.add_le_pair A.code B.code
    simp only [Term.nodes, Term.code]
    omega
  | lam x A ih =>
    have := Nat.right_le_pair x A.code
    simp only [Term.nodes, Term.code]
    omega

/-- Capture avoidance may rename binders, but it cannot discard a replacement
inserted at a free occurrence. -/
theorem replacement_nodes_le (A N : LTerm) (x : ℕ) (hx : x ∈ A.fv) :
    N.nodes ≤ (A.subst x N).nodes := by
  have bounded : ∀ k (A N : LTerm) x, A.nodes ≤ k → x ∈ A.fv →
      N.nodes ≤ (A.subst x N).nodes := by
    intro k
    induction k with
    | zero => intro A N x hk; have := A.nodes_pos; omega
    | succ k ih =>
      intro A N x hk hx
      cases A with
      | var y =>
        have hy : y = x := (by simpa [Term.fv] using hx : x = y).symm
        simp only [Term.subst_var, hy, ite_true]
        exact le_rfl
      | app A B =>
        simp only [Term.nodes] at hk
        simp only [Term.fv, Finset.mem_union] at hx
        rw [Term.subst_app]
        simp only [Term.nodes]
        rcases hx with ha | hb
        · have := ih A N x (by omega) ha; omega
        · have := ih B N x (by omega) hb; omega
      | lam y A =>
        have hx' := Finset.mem_erase.mp hx
        have hA : A.nodes ≤ k := by simpa only [Term.nodes, Nat.add_le_add_iff_right] using hk
        rw [Term.subst_lam, ite_eq_right (Ne.symm hx'.1)]
        by_cases hy : y ∉ N.fv
        · rw [ite_eq_left hy]
          have := ih A N x hA hx'.2
          simp only [Term.nodes]; omega
        · rw [ite_eq_right hy]
          let z := Term.fresh (A.fv ∪ N.fv ∪ {x})
          have hz : x ∈ (A.subst y (.var z)).fv :=
            (Term.mem_fv_subst _ _ _ _).mpr (Or.inl ⟨hx'.2, hx'.1⟩)
          have hh := ih (A.subst y (.var z)) N x (by simpa only [Term.nodes_subst_var] using hA) hz
          change N.nodes ≤ ((A.subst y (.var z)).subst x N).nodes + 1
          omega
  exact bounded A.nodes A N x le_rfl hx

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Define
    \begin{mathmeta}
      \define{LambdaSyntaxSizeBound}
    \end{mathmeta}
    $$
    \LambdaSyntaxSizeBound{k}{0}=3k+3,\qquad
    \LambdaSyntaxSizeBound{k}{m+1}=3\bigl(\LambdaSyntaxSizeBound{k}{m}+1\bigr)^2+3.
    $$
-/
/-- A deliberately generous primitive-recursive bound on raw syntax codes. -/
def codeBound (k : ℕ) : ℕ → ℕ
  | 0 => 3 * k + 3
  | n + 1 => 3 * (codeBound k n + 1) ^ 2 + 3

theorem codeBound_step (k n : ℕ) : codeBound k n ≤ codeBound k (n + 1) := by
  simp only [codeBound]
  nlinarith

theorem codeBound_mono (k : ℕ) : Monotone (codeBound k) := by
  intro m n h
  induction h with
  | refl => rfl
  | @step n _ ih => exact ih.trans (codeBound_step k n)

theorem name_le_codeBound (k n : ℕ) : k ≤ codeBound k n := by
  have hh := codeBound_mono k (Nat.zero_le n)
  simp only [codeBound] at hh
  omega

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Induction on the syntax shows that a term with at most $m$ nodes and with every variable and binder index at most
    $k$ has code at most $\LambdaSyntaxSizeBound{k}{m}$. The variable case follows from its code being three times its
    index. The application and abstraction cases use the fact that pairing two numbers at most $d$ gives a number
    less than $(d+1)^2$.
-/
theorem code_le_bound (A : LTerm) (k n : ℕ) (hn : A.nodes ≤ n) (hk : NamesLe k A) :
    A.code ≤ codeBound k n := by
  induction n generalizing A with
  | zero => have := A.nodes_pos; omega
  | succ n ih =>
    have hkB := name_le_codeBound k n
    cases A with
    | var x =>
      change x ≤ k at hk
      simp only [Term.code, codeBound]
      nlinarith
    | app A B =>
      have ha := ih A (by simp only [Term.nodes] at hn; omega) hk.1
      have hb := ih B (by simp only [Term.nodes] at hn; omega) hk.2
      have hp := Nat.pair_lt_max_add_one_sq A.code B.code
      have hm : max A.code B.code ≤ codeBound k n := max_le ha hb
      have hs := Nat.mul_self_le_mul_self (Nat.add_le_add_right hm 1)
      simp only [← pow_two] at hs
      simp only [Term.code, codeBound]
      omega
    | lam x A =>
      have ha := ih A (by simp only [Term.nodes] at hn; omega) hk.2
      have hx : x ≤ codeBound k n := hk.1.trans hkB
      have hp := Nat.pair_lt_max_add_one_sq x A.code
      have hm : max x A.code ≤ codeBound k n := max_le hx ha
      have hs := Nat.mul_self_le_mul_self (Nat.add_le_add_right hm 1)
      simp only [← pow_two] at hs
      simp only [Term.code, codeBound]
      omega

def witnessBound (targetCode : ℕ) : ℕ := codeBound targetCode (2 * targetCode + 1)

/-- The target is arbitrary raw lambda syntax. Only its alpha equivalence to
the substituted source formula is required. -/
theorem witness_code_le (φ : Formula L) (x : ℕ) (r : L.Term ℕ) (B : LTerm)
    (hx : x ∈ φ.fv) (hB : B.Alpha (S.encodeFormula (φ.subst x r))) :
    (S.encodeTerm r).code ≤ witnessBound B.code := by
  have he := (S.encodeFormula_subst_alpha φ x r).trans hB.symm
  have hfree : x ∈ (S.encodeFormula φ).fv := by simpa only [S.encodeFormula_fv] using hx
  have hn := replacement_nodes_le (S.encodeFormula φ) (S.encodeTerm r) x hfree
  rw [he.nodes_eq] at hn
  apply code_le_bound _ B.code (2 * B.code + 1) (hn.trans (nodes_le_code B))
  apply encodeTerm_namesLe S r B.code
  intro y hy
  have hy' : y ∈ (S.encodeTerm r).fv := by simpa only [S.encodeTerm_fv] using hy
  have ho := (Term.mem_fv_subst (S.encodeFormula φ) x (S.encodeTerm r) y).mpr (Or.inr ⟨hfree, hy'⟩)
  rw [he.fv_eq] at ho
  exact free_name_le_code B y ho

open NamedLambda.AlphaTerm LambdaIndexPCA
open FirstOrderLambdaEncoding.Grammar (Program)

namespace Program

def add (p q : Program) : Program :=
  ⟨addNumerical p.term q.term, fun n => p.value n + q.value n, p.computes.add q.computes⟩
def call (p q : Program) : Program :=
  ⟨numericalCompose p.term q.term, fun n => p.value (q.value n), p.computes.comp q.computes⟩

end Program

open FirstOrderLambdaEncoding.Grammar.Program

def boundBase : Program := Program.add ((const 3).mul ident) (const 3)
def boundStep : Program :=
  let v := Program.add ident.second.second (const 1)
  Program.add ((const 3).mul (v.mul v)) (const 3)

theorem primitiveRec_bound (k n : ℕ) :
    primitiveRec (boundBase.value k)
      (fun j r => boundStep.value (Nat.pair k (Nat.pair j r))) n = codeBound k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [primitiveRec, ih]
    simp [boundStep, Program.add, mul, second, ident, const, codeBound, pow_two]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The displayed recurrence is implemented by the numerical lambda recursor.
-/
/-- Runtime input is the pair `(name bound, node bound)`. -/
def codeBoundProgram : Program :=
  ⟨numericalRecursion boundBase.term boundStep.term,
    fun z => codeBound z.unpair.1 z.unpair.2, by
      simpa only [primitiveRec_bound] using numericalRecursion_computes boundBase.computes boundStep.computes⟩

theorem codeBoundProgram_apply (k n : ℕ) : Relation.ReflTransGen Beta
    (app codeBoundProgram.term (numeral (Nat.pair k n))) (numeral (codeBound k n)) := by
  simpa only [codeBoundProgram, Nat.unpair_pair] using codeBoundProgram.computes.2 (Nat.pair k n)

/-- The size/name bound uses the observed raw target code as runtime input. -/
def witnessBoundProgram : Program :=
  Program.call codeBoundProgram (ident.pair (Program.add ((const 2).mul ident) (const 1)))

theorem witnessBoundProgram_value (n : ℕ) : witnessBoundProgram.value n = witnessBound n := by
  simp [witnessBoundProgram, Program.call, codeBoundProgram, Program.add, ident, pair, mul, const, witnessBound]

theorem witnessBoundProgram_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app witnessBoundProgram.term (numeral n)) (numeral (witnessBound n)) := by
  simpa only [witnessBoundProgram_value] using witnessBoundProgram.computes.2 n

end QuantifierBounds
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
