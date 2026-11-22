module

public import PolishSpaceBook.FirstOrderLocalRulePrograms

@[expose] public section

/-! # A total lambda fold over unannotated numerical proof trees

A node is tagged syntax carrying its numerical sequent and a structural list of
children. Its data contain no rule annotation. The fold checks the seventeen
concrete local clauses and all descendants, so recursion is always on proper
syntax subtrees even for malformed numerical inputs.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency.types false

namespace ProofTreeProgram
abbrev P := Grammar.Program

/-- State: raw code, tree bit, root sequent, list bit, list of roots,
node-payload bit, node-payload root. -/
def pack (c t r l rs p pr : ℕ) :=
  Nat.pair c (Nat.pair t (Nat.pair r (Nat.pair l (Nat.pair rs (Nat.pair p pr)))))
def treeBit (s : ℕ) := s.unpair.2.unpair.1

namespace Program

def code (p : P) := p.first
def tree (p : P) := p.second.first
def root (p : P) := p.second.second.first
def listBit (p : P) := p.second.second.second.first
def roots (p : P) := p.second.second.second.second.first
def payloadBit (p : P) := p.second.second.second.second.second.first
def payloadRoot (p : P) := p.second.second.second.second.second.second

def pack (c t r l rs p pr : P) : P :=
  c.pair (t.pair (r.pair (l.pair (rs.pair (p.pair pr)))))

def ruleCheck (p : P) : P := LocalRulePrograms.Program.call LocalRulePrograms.checker.term
  LocalRulePrograms.checker.value LocalRulePrograms.checker.computes p

end Program

def variableHandler : P := Program.pack Grammar.Program.ident.varCode
  (Grammar.Program.const 0) (Grammar.Program.const 0)
  (Grammar.Program.ident.equal (Grammar.Program.const 0))
  (Grammar.Program.const 0) (Grammar.Program.const 0) (Grammar.Program.const 0)

def applicationHandler : P :=
  let a := Grammar.Program.ident.first
  let b := Grammar.Program.ident.second
  let seq := LocalRulePrograms.Program.payload (Program.code a)
  let nodePayload := LocalRulePrograms.Program.all
    [(Program.code a).syntaxTag.equal (Grammar.Program.const 0), Program.listBit b,
      LocalRulePrograms.Program.validSequent seq,
      Program.ruleCheck (seq.pair (Program.roots b))]
  Program.pack ((Program.code a).application (Program.code b))
    (((Program.code a).alpha (Grammar.Program.const (tag 8).code)).mul (Program.payloadBit b))
    (Program.payloadRoot b)
    ((Program.tree a).mul (Program.listBit b))
    (TemplatePrograms.Program.cons (Program.root a) (Program.roots b))
    nodePayload seq

def abstractionHandler : P := Program.pack
  (Grammar.Program.ident.first.abstraction (Program.code Grammar.Program.ident.second))
  (Grammar.Program.const 0) (Grammar.Program.const 0) (Grammar.Program.const 0)
  (Grammar.Program.const 0) (Grammar.Program.const 0) (Grammar.Program.const 0)

/-- The host recurrence is exactly the explicit numerical handler table. -/
def state : LTerm → ℕ
  | .var x => variableHandler.value x
  | .app A B => applicationHandler.value (Nat.pair (state A) (state B))
  | .lam x A => abstractionHandler.value (Nat.pair x (state A))

def stateTerm : AlphaTerm := syntaxFold variableHandler.term
  (curryNumerical applicationHandler.term) (curryNumerical abstractionHandler.term)

theorem stateTerm_closed : stateTerm.Closed := syntaxFold_closed variableHandler.computes.1
  (curryNumerical_closed applicationHandler.computes.1) (curryNumerical_closed abstractionHandler.computes.1)

theorem stateTerm_code (M : LTerm) : Relation.ReflTransGen Beta
    (app stateTerm (numeral M.code)) (numeral (state M)) := by
  apply syntaxFold_apply variableHandler.computes.1
    (curryNumerical_closed applicationHandler.computes.1)
    (curryNumerical_closed abstractionHandler.computes.1) (fun M => numeral (state M))
  · intro x; exact variableHandler.computes.2 x
  · intro A B
    exact (curryNumerical_apply applicationHandler.computes.1 _ _).trans
      (applicationHandler.computes.2 (Nat.pair (state A) (state B)))
  · intro x A
    exact (curryNumerical_apply abstractionHandler.computes.1 _ _).trans
      (abstractionHandler.computes.2 (Nat.pair x (state A)))

theorem stateTerm_computes : NumericalComputes stateTerm (fun n => state (Term.decode n)) :=
  ⟨stateTerm_closed, fun n => by simpa only [Term.code_decode] using stateTerm_code (Term.decode n)⟩

def flagProgram : P :=
  ⟨numericalCompose (Program.tree Grammar.Program.ident).term stateTerm,
    fun n => treeBit (state (Term.decode n)),
    (Program.tree Grammar.Program.ident).computes.comp stateTerm_computes⟩

def checker : P := LocalRulePrograms.Program.normalize flagProgram

def accepts (n : ℕ) : Prop := treeBit (state (Term.decode n)) ≠ 0
instance acceptsDecidable (n : ℕ) : Decidable (accepts n) := inferInstanceAs (Decidable (_ ≠ 0))

/-- Every numeral input halts with exactly the acceptance bit. -/
theorem checker_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app checker.term (numeral n)) (numeral (if accepts n then 1 else 0)) := by
  have h := checker.computes.2 n
  convert h using 1
  apply congrArg numeral
  change (if accepts n then 1 else 0 : ℕ) = if treeBit (state (Term.decode n)) = 0 then 0 else 1
  by_cases h : treeBit (state (Term.decode n)) = 0 <;> simp [accepts, h]

theorem checker_closed : checker.term.Closed := checker.computes.1

/-- The candidate data contain sequents and ordered child trees only. A sequent
number pairs a context list code with a conclusion formula code. -/
inductive Data where
  | node (sequent : ℕ) (children : List Data) : Data

namespace Data

def root : Data → ℕ
  | .node s _ => s

def encode : Data → LTerm
  | .node s cs => FirstOrderLambdaEncoding.node 8 (.app (.var s) ((cs.map encode).foldr Term.app (.var 0)))

end Data
end ProofTreeProgram
end PolishSpaceBook.FirstOrderLambdaEncoding
