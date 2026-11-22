module

public import PolishSpaceBook.FirstOrderEigenvariablePrograms
public import PolishSpaceBook.FirstOrderUnannotatedTrees
public import PolishSpaceBook.LambdaListAccess

@[expose] public section

/-! # Concrete lambda alternatives for the seventeen local inference rules

The input is a root sequent and the list of child sequents. Neither rule tags nor
substitution witnesses occur in that input. Every clause below is a composition
of the already constructed total numerical lambda programs. The separate
correspondence layer relates these numerical clauses to `LocalRule`.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 16384

namespace LocalRulePrograms
open TemplatePrograms
abbrev P := Grammar.Program

namespace Program

def call (F : AlphaTerm) (f : ℕ → ℕ) (hF : NumericalComputes F f) (p : P) : P :=
  ⟨numericalCompose F p.term, fun n => f (p.value n), hF.comp p.computes⟩
def all (ps : List P) : P := ps.foldr Grammar.Program.mul (Grammar.Program.const 1)
def any (ps : List P) : P := ps.foldr (fun p r => p.ifZero r (Grammar.Program.const 1)) (Grammar.Program.const 0)
def normalize (p : P) : P := p.ifZero (Grammar.Program.const 0) (Grammar.Program.const 1)
def field (first : Bool) (p : P) : P := call (syntaxFieldTerm first)
  (fun n => if first then (n / 3).unpair.1 else (n / 3).unpair.2)
  ⟨syntaxFieldTerm_closed first, syntaxFieldTerm_apply first⟩ p
def payload (p : P) : P := call syntaxPayloadTerm (· / 3)
  ⟨syntaxPayloadTerm_closed, syntaxPayloadTerm_apply⟩ p

def tagIs (p : P) (k : ℕ) : P := (field true p).alpha (Grammar.Program.const (tag k).code)
def left (p : P) : P := field true (field false p)
def right (p : P) : P := field false (field false p)
def atomLeft (p : P) : P := payload (left p)
def atomRight (p : P) : P := payload (right p)
def length (p : P) : P := call listLengthTerm _ listLength_computes p
def get (p : P) (i : ℕ) : P := call listGetTerm _ listGet_computes (p.pair (Grammar.Program.const i))

def contextEqual := EigenvariablePrograms.Program.contextEqual

def conclusionEqual (s t : P) : P := s.second.alpha t.second
def sameContext (s t : P) : P := contextEqual s.first t.first

def withHyp (φ Γ : P) : P := TemplatePrograms.Program.cons φ Γ

def validSequent (s : P) : P :=
  (call ContextPrograms.grammarTerm _ ContextPrograms.grammarTerm_computes s.first).mul
    (call Grammar.formulaTerm _ Grammar.formulaTerm_computes s.second)

def instanceSearch (body binder target : P) : P :=
  call InstancePrograms.searchTerm _ InstancePrograms.searchTerm_computes
    (body.pair (binder.pair target))

def allSearch (Γ body target : P) : P :=
  call EigenvariablePrograms.allSearchTerm _ EigenvariablePrograms.allSearchTerm_computes
    (Γ.pair (body.pair target))

def exSearch (Γ Δ body target binder : P) : P :=
  call EigenvariablePrograms.exSearchTerm _ EigenvariablePrograms.exSearchTerm_computes
    (Γ.pair (Δ.pair (body.pair (target.pair binder))))

def equalitySearch (source target t r : P) : P :=
  ⟨numericalCompose EqualityMatcher.rawProgram.term (source.pair (target.pair (t.pair r))).term,
    fun n => EqualityMatcher.rawProgram.value (Nat.pair (source.value n)
      (Nat.pair (target.value n) (Nat.pair (t.value n) (r.value n)))),
    EqualityMatcher.rawProgram.computes.comp (source.pair (target.pair (t.pair r))).computes⟩

end Program

/-- Nullary schemas: assumption, reflexive equality and excluded middle. -/
def nullary (s : P) : P :=
  let a := s.second
  let assumption := TemplatePrograms.Program.binary ContextPrograms.memberTerm
    (fun a c => if ContextPrograms.member a c then 1 else 0)
    ContextPrograms.memberTerm_closed ContextPrograms.memberTerm_apply a s.first
  let reflexive := Program.all [Program.tagIs a 1, (Program.left a).alpha (Program.right a)]
  let excludedMiddle := Program.all [Program.tagIs a 4, Program.tagIs (Program.right a) 5,
    (Program.left a).alpha (Program.left (Program.right a)),
    (Program.right (Program.right a)).alpha (Grammar.Program.const (encode .falsum).code)]
  Program.any [assumption, reflexive, excludedMiddle]

/-- The nine one-premise schemas, including their context conditions. -/
def unary (s p : P) : P :=
  let a := s.second
  let b := p.second
  let same := Program.sameContext s p
  let andLeft := Program.all [same, Program.tagIs b 3, a.alpha (Program.left b)]
  let andRight := Program.all [same, Program.tagIs b 3, a.alpha (Program.right b)]
  let orLeft := Program.all [same, Program.tagIs a 4, b.alpha (Program.left a)]
  let orRight := Program.all [same, Program.tagIs a 4, b.alpha (Program.right a)]
  let impIntro := Program.all [Program.tagIs a 5, b.alpha (Program.right a),
    Program.contextEqual p.first (Program.withHyp (Program.left a) s.first)]
  let falseElim := Program.all [same, b.alpha (Grammar.Program.const (encode .falsum).code)]
  let allIntro := Program.all [same, Program.allSearch s.first b a]
  let allElim := Program.all [same, Program.tagIs b 6,
    Program.instanceSearch (Program.right b) (Program.left b) a]
  let exIntro := Program.all [same, Program.tagIs a 7,
    Program.instanceSearch (Program.right a) (Program.left a) b]
  Program.any [andLeft, andRight, orLeft, orRight, impIntro, falseElim, allIntro, allElim, exIntro]

/-- The four two-premise schemas. -/
def binary (s p q : P) : P :=
  let a := s.second
  let b := p.second
  let c := q.second
  let same := Program.all [Program.sameContext s p, Program.sameContext s q]
  let andIntro := Program.all [same, Program.tagIs a 3, b.alpha (Program.left a), c.alpha (Program.right a)]
  let impElim := Program.all [same, Program.tagIs b 5, c.alpha (Program.left b), a.alpha (Program.right b)]
  let exElim := Program.all [Program.sameContext s p, Program.tagIs b 7, a.alpha c,
    Program.exSearch s.first q.first (Program.right b) a (Program.left b)]
  let eqElim := Program.all [same, Program.tagIs c 1,
    Program.equalitySearch b a (Program.atomLeft c) (Program.atomRight c)]
  Program.any [andIntro, impElim, exElim, eqElim]

/-- Disjunction elimination is the sole three-premise schema. -/
def ternary (s p q r : P) : P :=
  let a := p.second
  Program.all [Program.sameContext s p, Program.tagIs a 4,
    Program.conclusionEqual s q, Program.conclusionEqual s r,
    Program.contextEqual q.first (Program.withHyp (Program.left a) s.first),
    Program.contextEqual r.first (Program.withHyp (Program.right a) s.first)]

/-- All grammar checks run on the supplied labels; excess children are rejected. -/
def checker : P :=
  let s := Grammar.Program.ident.first
  let cs := Grammar.Program.ident.second
  let p := Program.get cs 0
  let q := Program.get cs 1
  let r := Program.get cs 2
  let n := Program.length cs
  let one := Program.all [Program.validSequent p, unary s p]
  let two := Program.all [Program.validSequent p, Program.validSequent q, binary s p q]
  let three := Program.all [Program.validSequent p, Program.validSequent q, Program.validSequent r, ternary s p q r]
  let choices := (n.equal (Grammar.Program.const 0)).ifZero
    ((n.equal (Grammar.Program.const 1)).ifZero
      ((n.equal (Grammar.Program.const 2)).ifZero
        ((n.equal (Grammar.Program.const 3)).ifZero (Grammar.Program.const 0) three) two) one)
    (nullary s)
  Program.normalize ((Program.validSequent s).mul choices)

/-- The implemented local checker is total on every numerical input. -/
theorem checker_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app checker.term (numeral n)) (numeral (checker.value n)) := checker.computes.2 n

theorem checker_closed : checker.term.Closed := checker.computes.1

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
