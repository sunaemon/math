module

public import PolishSpaceBook.FirstOrderEqualityTemplatePrograms

@[expose] public section

/-! # Total lambda matching of equality elimination without an annotated template

Two finite subset enumerations implement the template test. The second selects
all distinguished leaves, because its target has no distinguished free name.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false

namespace EqualityMatcher
open TemplatePrograms

def candidateCodes (n t z : ℕ) : List ℕ := (variants t z (Term.decode n)).map Term.code

@[simp] theorem candidateCodes_tree (A : BindingTree) (t z : ℕ) :
    candidateCodes A.code t z = (BindingTree.templates t z A).map BindingTree.code := by
  simp only [candidateCodes, BindingTree.code, Term.decode_code, variants_dataTerm, List.map_map]
  rfl

def candidateProgram : Grammar.Program :=
  ⟨uncurryNumerical candidatesTerm,
    fun n => NatListCode.encode (candidateCodes n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2),
    uncurryNumerical_computes candidatesTerm_closed
      (fun n p => NatListCode.encode (candidateCodes n p.unpair.1 p.unpair.2)) (fun n p => by
      simpa only [Nat.pair_unpair, candidateCodes] using candidatesTerm_apply n p.unpair.1 p.unpair.2)⟩

/-- Parameter is `(target,(distinguished,replacement))`. -/
def hit (p c : ℕ) : Bool := decide (p.unpair.1 ∈ candidateCodes c p.unpair.2.unpair.1 p.unpair.2.unpair.2)

def hitProgram : Grammar.Program :=
  let p := Grammar.Program.ident.first
  let c := Grammar.Program.ident.second
  let candidates : Grammar.Program :=
    ⟨numericalCompose candidateProgram.term (c.pair p.second).term,
      fun n => NatListCode.encode (candidateCodes (c.value n) (p.value n).unpair.2.unpair.1
        (p.value n).unpair.2.unpair.2), by
        convert candidateProgram.computes.comp (c.pair p.second).computes using 1
        funext n
        simp only [candidateProgram, Grammar.Program.pair, Grammar.Program.second, Nat.unpair_pair]⟩
  ⟨(Program.binary listMemberTerm
      (fun a e => if a ∈ NatListCode.decode e then 1 else 0)
      listMemberTerm_closed listMemberTerm_apply p.first candidates).term,
    fun n => if hit n.unpair.1 n.unpair.2 then 1 else 0, by
      have h := (Program.binary listMemberTerm
        (fun a e => if a ∈ NatListCode.decode e then 1 else 0)
        listMemberTerm_closed listMemberTerm_apply p.first candidates).computes
      convert h using 1
      funext n
      simp only [hit, p, c, candidates, Program.binary, Grammar.Program.first,
        Grammar.Program.second, Grammar.Program.ident, id_eq, NatListCode.decode_encode,
        decide_eq_true_eq]⟩

def anyHitTerm : AlphaTerm := ContextPrograms.anyWithParameter hitProgram.term

theorem anyHitTerm_closed : anyHitTerm.Closed := ContextPrograms.anyWithParameter_closed hitProgram.computes.1

theorem anyHitTerm_apply (p e : ℕ) : Relation.ReflTransGen Beta
    (app (app anyHitTerm (numeral p)) (numeral e))
    (numeral (if (NatListCode.decode e).any (hit p) then 1 else 0)) :=
  ContextPrograms.anyWithParameter_apply hitProgram.computes p e

/-- Inputs are `(source,(target,(left,(right,distinguished))))`. -/
def input (a b t r z : ℕ) := Nat.pair a (Nat.pair b (Nat.pair t (Nat.pair r z)))

def check (a b t r z : ℕ) : Bool :=
  (candidateCodes a t z).any (hit (Nat.pair b (Nat.pair z r)))

def checkProgram : Grammar.Program :=
  let a := Grammar.Program.ident.first
  let b := Grammar.Program.ident.second.first
  let t := Grammar.Program.ident.second.second.first
  let r := Grammar.Program.ident.second.second.second.first
  let z := Grammar.Program.ident.second.second.second.second
  let candidates : Grammar.Program :=
    ⟨numericalCompose candidateProgram.term (a.pair (t.pair z)).term,
      fun n => NatListCode.encode (candidateCodes (a.value n) (t.value n) (z.value n)), by
        convert candidateProgram.computes.comp (a.pair (t.pair z)).computes using 1
        funext n
        simp only [candidateProgram, Grammar.Program.pair, Nat.unpair_pair]⟩
  Program.binary anyHitTerm (fun p e => if (NatListCode.decode e).any (hit p) then 1 else 0)
    anyHitTerm_closed anyHitTerm_apply (b.pair (z.pair r)) candidates

theorem checkProgram_apply (a b t r z : ℕ) : Relation.ReflTransGen Beta
    (app checkProgram.term (numeral (input a b t r z)))
    (numeral (if check a b t r z then 1 else 0)) := by
  have h := checkProgram.computes.2 (input a b t r z)
  convert h using 1
  simp only [checkProgram, Program.binary, Grammar.Program.pair, Grammar.Program.first,
    Grammar.Program.second, Grammar.Program.ident, id_eq, Nat.unpair_pair,
    NatListCode.decode_encode, input, check]
  rfl

/-- On binding-tree codes, the numeric search is exactly the two finite lists. -/
theorem check_tree_iff (A B : BindingTree) (t r z : ℕ) :
    check A.code B.code t r z = true ↔
      ∃ C ∈ BindingTree.templates t z A, B ∈ BindingTree.templates z r C := by
  simp only [check, candidateCodes_tree, List.any_eq_true, List.mem_map, hit,
    Nat.unpair_pair, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, hB⟩
    rw [candidateCodes_tree] at hB
    obtain ⟨D, hD, he⟩ := List.mem_map.mp hB
    exact ⟨C, hC, BindingTree.code_injective he ▸ hD⟩
  · rintro ⟨C, hC, hB⟩
    refine ⟨C.code, ⟨C, hC, rfl⟩, ?_⟩
    rw [candidateCodes_tree]
    exact List.mem_map.mpr ⟨B, hB, rfl⟩

/-- The template predicate has no existentially supplied annotation: the program
searches the two explicit finite lists from the source and target themselves. -/
theorem check_formula_iff (A B : FOL) (t r z : ℕ)
    (hzA : z ∉ names A) (hzB : z ∉ B.fv) :
    check (encode A).bindingTree.code (encode B).bindingTree.code t r z = true ↔
      ∃ (φ : FOL) (x : ℕ), (φ.subst x (.var t)).Alpha A ∧ (φ.subst x (.var r)).Alpha B := by
  rw [check_tree_iff, ← equality_templates_iff A B t r z hzA]
  constructor
  · rintro ⟨C, hC, hB⟩
    refine ⟨C, hC, (BindingTree.template_eq_subst_of_not_mem hB ?_).symm⟩
    simpa only [Term.bindingTree_fv, encode_fv] using hzB
  · rintro ⟨C, hC, hB⟩
    exact ⟨C, hC, hB ▸ BindingTree.subst_mem_templates C z r⟩


/-- A finite upper bound for every name, including shadowed and bound names. -/
def syntaxNames : LTerm → Finset ℕ
  | .var x => {x}
  | .app M N => syntaxNames M ∪ syntaxNames N
  | .lam x M => insert x (syntaxNames M)

theorem syntaxName_le_code (M : LTerm) {x : ℕ} (hx : x ∈ syntaxNames M) : x ≤ M.code := by
  induction M with
  | var y => simp only [syntaxNames, Finset.mem_singleton] at hx; subst x; simp [Term.code]; omega
  | app M N ihM ihN =>
    simp only [syntaxNames, Finset.mem_union] at hx
    have hm := Nat.left_le_pair M.code N.code
    have hn := Nat.right_le_pair M.code N.code
    rcases hx with hx | hx
    · have := ihM hx; simp only [Term.code]; omega
    · have := ihN hx; simp only [Term.code]; omega
  | lam y M ih =>
    simp only [syntaxNames, Finset.mem_insert] at hx
    have hy := Nat.left_le_pair y M.code
    have hm := Nat.right_le_pair y M.code
    rcases hx with rfl | hx
    · simp only [Term.code]; omega
    · have := ih hx; simp only [Term.code]; omega

theorem names_subset_syntaxNames (φ : FOL) : names φ ⊆ syntaxNames (encode φ) := by
  induction φ with
  | falsum => simp [names]
  | equal s t => simp [names, encode, node, syntaxNames]
  | rel r ts => cases r; simp [names, encode, node, syntaxNames]
  | binary c φ ψ ihφ ihψ =>
    simp only [names, encode, node, syntaxNames]
    exact Finset.Subset.trans (Finset.union_subset_union ihφ ihψ) Finset.subset_union_right
  | quant q x φ ih =>
    simp only [names, encode, node, syntaxNames]
    exact Finset.Subset.trans (Finset.insert_subset_insert x ih) Finset.subset_union_right

def freshName (a b : ℕ) := a + b + 1

theorem freshName_source (A B : FOL) : freshName (encode A).code (encode B).code ∉ names A := by
  intro h
  have := syntaxName_le_code (encode A) (names_subset_syntaxNames A h)
  simp only [freshName] at this
  omega

theorem freshName_target (A B : FOL) : freshName (encode A).code (encode B).code ∉ B.fv := by
  intro h
  have := syntaxName_le_code (encode B) (names_subset_syntaxNames B (fv_subset_names B h))
  simp only [freshName] at this
  omega

def rawInput (a b t r : ℕ) := Nat.pair a (Nat.pair b (Nat.pair t r))
def rawCheck (a b t r : ℕ) : Bool :=
  check (Term.decode a).bindingTree.code (Term.decode b).bindingTree.code t r (freshName a b)

def bindingProgram (a : Grammar.Program) : Grammar.Program :=
  ⟨numericalCompose bindingTreeTerm a.term, fun n => (Term.decode (a.value n)).bindingTree.code,
    (show NumericalComputes bindingTreeTerm (fun n => (Term.decode n).bindingTree.code) from
      ⟨bindingTreeTerm_closed, bindingTreeTerm_apply⟩).comp a.computes⟩

def rawProgram : Grammar.Program :=
  let a := Grammar.Program.ident.first
  let b := Grammar.Program.ident.second.first
  let t := Grammar.Program.ident.second.second.first
  let r := Grammar.Program.ident.second.second.second
  let fresh : Grammar.Program :=
    ⟨numericalCompose successorTerm (addNumerical a.term b.term),
      fun n => freshName (a.value n) (b.value n), successor_computes.comp (a.computes.add b.computes)⟩
  let packed := (bindingProgram a).pair ((bindingProgram b).pair (t.pair (r.pair fresh)))
  ⟨numericalCompose checkProgram.term packed.term,
    fun n => checkProgram.value (packed.value n), checkProgram.computes.comp packed.computes⟩

/-- This closed program computes its own fresh name and binding-tree codes from
arbitrary numerical source and target codes. -/
theorem rawProgram_apply (a b t r : ℕ) : Relation.ReflTransGen Beta
    (app rawProgram.term (numeral (rawInput a b t r)))
    (numeral (if rawCheck a b t r then 1 else 0)) := by
  have h := rawProgram.computes.2 (rawInput a b t r)
  convert h using 1
  simp only [rawProgram, bindingProgram, checkProgram, Program.binary,
    Grammar.Program.pair, Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident,
    id_eq, rawInput, rawCheck, check, Nat.unpair_pair, NatListCode.decode_encode]
  rfl

/-- Exact equality-elimination template matching with no witness supplied to the program. -/
theorem rawCheck_formula_iff (A B : FOL) (t r : ℕ) :
    rawCheck (encode A).code (encode B).code t r = true ↔
      ∃ (φ : FOL) (x : ℕ), (φ.subst x (.var t)).Alpha A ∧ (φ.subst x (.var r)).Alpha B := by
  simpa only [rawCheck, Term.decode_code] using check_formula_iff A B t r
    (freshName (encode A).code (encode B).code) (freshName_source A B) (freshName_target A B)

end EqualityMatcher
end PolishSpaceBook.FirstOrderLambdaEncoding
