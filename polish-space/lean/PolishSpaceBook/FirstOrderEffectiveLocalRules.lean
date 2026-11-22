module

public import PolishSpaceBook.FirstOrderEffectiveContextGrammar
public import PolishSpaceBook.FirstOrderEffectiveEigenvariableWitnesses
public import PolishSpaceBook.FirstOrderEffectiveQuantifierInstances
public import PolishSpaceBook.FirstOrderEffectiveEqualityPrograms

@[expose] public section

/-! # The actual seventeen-rule lambda checker for an effective signature

Compound term witnesses are found by the constructed finite searches. Equality
elimination receives whole term codes, rather than extracting variable numbers.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm
open FirstOrderLambdaEncoding
open FirstOrderLambdaEncoding.LocalRulePrograms (P)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

def instanceSearch (body binder target : P) : P :=
  run (InstancePrograms.searchProgram S) (body.pair (binder.pair target))

def equalitySearch (source target left right : P) : P :=
  run (EqualityPrograms.searchProgram S) (source.pair (target.pair (left.pair right)))

abbrev nullary : P → P := LocalRulePrograms.nullary
abbrev ternary : P → P → P → P → P := LocalRulePrograms.ternary

def unary (s p : P) : P :=
  let a := s.second
  let b := p.second
  let same := LocalRulePrograms.Program.sameContext s p
  let andLeft := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs b 3,
    a.alpha (LocalRulePrograms.Program.left b)]
  let andRight := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs b 3,
    a.alpha (LocalRulePrograms.Program.right b)]
  let orLeft := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs a 4,
    b.alpha (LocalRulePrograms.Program.left a)]
  let orRight := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs a 4,
    b.alpha (LocalRulePrograms.Program.right a)]
  let impIntro := LocalRulePrograms.Program.all [LocalRulePrograms.Program.tagIs a 5,
    b.alpha (LocalRulePrograms.Program.right a),
    LocalRulePrograms.Program.contextEqual p.first
      (LocalRulePrograms.Program.withHyp (LocalRulePrograms.Program.left a) s.first)]
  let falseElim := LocalRulePrograms.Program.all [same,
    b.alpha (Grammar.Program.const (node 0 (tag 0)).code)]
  let allIntro := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.allSearch s.first b a]
  let allElim := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs b 6,
    instanceSearch S (LocalRulePrograms.Program.right b) (LocalRulePrograms.Program.left b) a]
  let exIntro := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs a 7,
    instanceSearch S (LocalRulePrograms.Program.right a) (LocalRulePrograms.Program.left a) b]
  LocalRulePrograms.Program.any [andLeft, andRight, orLeft, orRight, impIntro, falseElim, allIntro, allElim, exIntro]

def binary (s p q : P) : P :=
  let a := s.second
  let b := p.second
  let c := q.second
  let same := LocalRulePrograms.Program.all
    [LocalRulePrograms.Program.sameContext s p, LocalRulePrograms.Program.sameContext s q]
  let andIntro := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs a 3,
    b.alpha (LocalRulePrograms.Program.left a), c.alpha (LocalRulePrograms.Program.right a)]
  let impElim := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs b 5,
    c.alpha (LocalRulePrograms.Program.left b), a.alpha (LocalRulePrograms.Program.right b)]
  let exElim := LocalRulePrograms.Program.all [LocalRulePrograms.Program.sameContext s p,
    LocalRulePrograms.Program.tagIs b 7, a.alpha c,
    LocalRulePrograms.Program.exSearch s.first q.first (LocalRulePrograms.Program.right b) a (LocalRulePrograms.Program.left b)]
  let eqElim := LocalRulePrograms.Program.all [same, LocalRulePrograms.Program.tagIs c 1,
    equalitySearch S b a (LocalRulePrograms.Program.left c) (LocalRulePrograms.Program.right c)]
  LocalRulePrograms.Program.any [andIntro, impElim, exElim, eqElim]

def checker : P :=
  let s := Grammar.Program.ident.first
  let cs := Grammar.Program.ident.second
  let p := LocalRulePrograms.Program.get cs 0
  let q := LocalRulePrograms.Program.get cs 1
  let r := LocalRulePrograms.Program.get cs 2
  let n := LocalRulePrograms.Program.length cs
  let one := LocalRulePrograms.Program.all [validSequent S p, unary S s p]
  let two := LocalRulePrograms.Program.all [validSequent S p, validSequent S q, binary S s p q]
  let three := LocalRulePrograms.Program.all [validSequent S p, validSequent S q, validSequent S r, ternary s p q r]
  let choices := (n.equal (Grammar.Program.const 0)).ifZero
    ((n.equal (Grammar.Program.const 1)).ifZero
      ((n.equal (Grammar.Program.const 2)).ifZero
        ((n.equal (Grammar.Program.const 3)).ifZero (Grammar.Program.const 0) three) two) one)
    (nullary s)
  LocalRulePrograms.Program.normalize ((validSequent S s).mul choices)

theorem checker_apply (n : ℕ) : Relation.ReflTransGen Beta
    (app (checker S).term (numeral n)) (numeral ((checker S).value n)) := (checker S).computes.2 n

theorem checker_closed : (checker S).term.Closed := (checker S).computes.1

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature.EffectiveRulePrograms
