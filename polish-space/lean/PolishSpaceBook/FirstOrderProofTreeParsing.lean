module

public import PolishSpaceBook.FirstOrderProofTreeProgram

@[expose] public section

/-! # Total parsing of unannotated numerical tree data

A single structural pass keeps tree, child-list and node-payload views. The
payload contains a numerical sequent and a list of child trees; no rule witness
or proof annotation is decoded.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
open NamedLambda

structure Parsed where
  tree : Option Data
  children : Option (List Data)
  payload : Option (ℕ × List Data)

/-- Each recursive call is on one of the two immediate syntax children. -/
def parse : LTerm → Parsed
  | .var x => ⟨none, if x = 0 then some [] else none, none⟩
  | .lam _ _ => ⟨none, none, none⟩
  | .app A B =>
    let a := parse A
    let b := parse B
    ⟨if A.Alpha (tag 8) then b.payload.map (fun p => Data.node p.1 p.2) else none,
      do return (← a.tree) :: (← b.children),
      match A with
      | .var s => b.children.map (fun cs => (s, cs))
      | _ => none⟩

def parseCode (n : ℕ) : Option Data := (parse (Term.decode n)).tree

private theorem parse_children_fold (cs : List Data)
    (h : ∀ c ∈ cs, (parse c.encode).tree = some c) :
    (parse ((cs.map Data.encode).foldr Term.app (.var 0))).children = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldr_cons, parse]
    rw [h c (by simp), ih (fun d hd => h d (by simp [hd]))]
    rfl

@[simp] theorem parse_encode (T : Data) : (parse T.encode).tree = some T := by
  cases T with
  | node s cs =>
    have hcs := parse_children_fold cs (fun c hc => parse_encode c)
    simp only [Data.encode, FirstOrderLambdaEncoding.node, parse, Term.Alpha.refl, ↓reduceIte]
    rw [hcs]
    rfl
termination_by sizeOf T
decreasing_by
  have h := List.sizeOf_lt_of_mem hc
  simp only [Data.node.sizeOf_spec]
  omega

@[simp] theorem parseCode_encode (T : Data) : parseCode T.encode.code = some T := by
  simp only [parseCode, Term.decode_code, parse_encode]

/-- Parsing never adds or reads annotations: the root number is the one stored
in the variable payload, and the ordered child list is reconstructed structurally. -/
theorem parse_app_tree (A B : LTerm) (T : Data) :
    (parse (.app A B)).tree = some T ↔
      A.Alpha (tag 8) ∧ ∃ s cs, (parse B).payload = some (s, cs) ∧ T = .node s cs := by
  simp only [parse]
  by_cases h : A.Alpha (tag 8)
  · simp only [h, ↓reduceIte, Option.map_eq_some_iff, true_and]
    constructor
    · rintro ⟨⟨s, cs⟩, hp, he⟩; exact ⟨s, cs, hp, he.symm⟩
    · rintro ⟨s, cs, hp, rfl⟩; exact ⟨(s, cs), hp, rfl⟩
  · simp [h]

end PolishSpaceBook.FirstOrderLambdaEncoding.ProofTreeProgram
