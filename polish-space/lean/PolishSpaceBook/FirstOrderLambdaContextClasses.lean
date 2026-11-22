module

public import PolishSpaceBook.FirstOrderLambdaContextTests

@[expose] public section

/-! # Alpha-set semantics of arbitrary numerical context lists

This layer allows a substitution program to supply an alpha-equivalent raw
formula code directly to the context tests; no canonicalization oracle is used.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm NamedFirstOrder

/-- The formula encoding induces an injection on alpha classes. -/
def encodeClass : AlphaFormula ForcingFormulas.membershipLanguage → AlphaTerm :=
  Quotient.map encode (fun φ ψ h => (encode_alpha_iff φ ψ).mpr h)

@[simp] theorem encodeClass_mk (φ : FOL) : encodeClass (AlphaFormula.mk φ) = AlphaTerm.mk (encode φ) := rfl

theorem encodeClass_injective : Function.Injective encodeClass := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ φ =>
    induction b using Quotient.inductionOn with
    | _ ψ =>
      intro h
      exact (AlphaFormula.mk_eq_iff φ ψ).mpr
        ((encode_alpha_iff φ ψ).mp ((AlphaTerm.mk_eq_iff _ _).mp h))

namespace ContextPrograms
noncomputable local instance contextTermClassDecidableEq : DecidableEq AlphaTerm := Classical.decEq _
noncomputable local instance contextFormulaClassDecidableEq : DecidableEq (AlphaFormula ForcingFormulas.membershipLanguage) := Classical.decEq _

noncomputable def rawContext (e : ℕ) : Finset AlphaTerm :=
  ((NatListCode.decode e).map (fun a => AlphaTerm.mk (Term.decode a))).toFinset

theorem member_rawContext (a e : ℕ) :
    member a e = true ↔ AlphaTerm.mk (Term.decode a) ∈ rawContext e := by
  simp only [member, List.any_eq_true, decide_eq_true_eq, rawContext,
    List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, (AlphaTerm.mk_eq_iff _ _).mpr h.symm⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, (AlphaTerm.mk_eq_iff _ _).mp h.symm⟩

theorem subset_rawContext (e d : ℕ) : subset e d = true ↔ rawContext e ⊆ rawContext d := by
  simp only [subset, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_false, member_rawContext]
  constructor
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact h b hb
  · intro h a ha
    apply h
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)

def equalBit (e d : ℕ) : Bool := subset e d && subset d e

theorem equalBit_iff (e d : ℕ) : equalBit e d = true ↔ rawContext e = rawContext d := by
  simp only [equalBit, Bool.and_eq_true, subset_rawContext]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2, fun h => by simp [h]⟩

theorem rawContext_listCode (xs : List FOL) :
    rawContext (listCode xs) = (context xs).image encodeClass := by
  ext a
  simp only [rawContext, listCode, NatListCode.decode_encode, List.map_map,
    Function.comp_def, Term.decode_code, List.mem_toFinset, List.mem_map,
    Finset.mem_image, context]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨AlphaFormula.mk φ, ⟨φ, hφ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, rfl⟩

@[simp] theorem context_cons (φ : FOL) (xs : List FOL) :
    context (φ :: xs) = insert (AlphaFormula.mk φ) (context xs) := by
  simp only [context, List.map_cons, List.toFinset_cons]

 theorem equalBit_listCode (xs ys : List FOL) :
    equalBit (listCode xs) (listCode ys) = true ↔ context xs = context ys := by
  rw [equalBit_iff, rawContext_listCode, rawContext_listCode]
  exact ⟨fun h => Finset.image_injective encodeClass_injective h, congrArg (Finset.image encodeClass)⟩

theorem rawContext_cons (a e : ℕ) :
    rawContext (Nat.pair a e + 1) = insert (AlphaTerm.mk (Term.decode a)) (rawContext e) := by
  simp only [rawContext, NatListCode.decode, Nat.unpair_pair, List.map_cons, List.toFinset_cons]

/-- The concrete substitution output may be inserted directly into a context. -/
theorem rawContext_substitution (Γ : List FOL) (φ : FOL) (x y : ℕ) :
    rawContext (Nat.pair ((encode φ).subst x (.var y)).code (listCode Γ) + 1) =
      rawContext (listCode (φ.subst x (.var y) :: Γ)) := by
  rw [rawContext_cons, rawContext_listCode Γ, rawContext_listCode (_ :: _),
    context_cons, Finset.image_insert]
  simp only [Term.decode_code, encodeClass_mk]
  rw [(AlphaTerm.mk_eq_iff _ _).mpr (encode_subst_alpha φ x y)]


theorem equalBit_substitution (Γ Δ : List FOL) (φ : FOL) (x y : ℕ) :
    equalBit (listCode Δ) (Nat.pair ((encode φ).subst x (.var y)).code (listCode Γ) + 1) = true ↔
      context Δ = insert (AlphaFormula.mk (φ.subst x (.var y))) (context Γ) := by
  rw [equalBit_iff, rawContext_substitution, rawContext_listCode, rawContext_listCode]
  constructor
  · intro h
    simpa only [context_cons] using Finset.image_injective encodeClass_injective h
  · intro h
    apply congrArg (Finset.image encodeClass)
    simpa only [context_cons] using h

/-- Curried form of the actual numerical context comparator. -/
def equalTerm : AlphaTerm := curryNumerical equalProgram.term

theorem equalTerm_closed : equalTerm.Closed := curryNumerical_closed equalProgram.computes.1

theorem equalTerm_apply (e d : ℕ) : Relation.ReflTransGen Beta
    (app (app equalTerm (numeral e)) (numeral d))
    (numeral (if equalBit e d then 1 else 0)) :=
  (curryNumerical_apply equalProgram.computes.1 e d).trans (equalProgram_apply e d)

end ContextPrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
