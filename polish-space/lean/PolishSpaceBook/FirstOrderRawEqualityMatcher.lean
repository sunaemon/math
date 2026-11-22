module

public import PolishSpaceBook.FirstOrderEqualityMatcher

@[expose] public section

/-! # Equality-template matching for arbitrary parsed formula codes

The parser retains every atomic and binder name. Consequently the actual input
code bounds all names of its parsed representative, even when rigid tags use
other alpha-equivalent bound names.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedFirstOrder FirstOrder Language
open EqualityMatcher
set_option backward.isDefEq.respectTransparency.types false

 theorem parse_names_subset (M : LTerm) (φ : FOL) (hp : parse M = some φ) :
    names φ ⊆ syntaxNames M := by
  have aux : ∀ n (M : LTerm) (φ : FOL), M.nodes ≤ n → parse M = some φ →
      names φ ⊆ syntaxNames M := by
    intro n
    induction n with
    | zero => intro M φ hn; have := M.nodes_pos; omega
    | succ n ih =>
      intro M φ hn hp
      cases M with
      | var => simp [parse.eq_def] at hp
      | lam => simp [parse.eq_def] at hp
      | app k p =>
        have binary (c : Connective)
            (hb : (match p with
              | .app a b => do return Formula.binary (L := ForcingFormulas.membershipLanguage) c (← parse a) (← parse b)
              | _ => none) = some φ) : names φ ⊆ syntaxNames (.app k p) := by
          cases p with
          | var => simp at hb
          | lam => simp at hb
          | app a b =>
            change (parse a).bind (fun α => (parse b).bind (fun β => some (Formula.binary c α β))) = some φ at hb
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
            obtain ⟨α, hα, β, hβ, rfl⟩ := hb
            have ha := ih a α (by simp only [Term.nodes] at hn; omega) hα
            have hb := ih b β (by simp only [Term.nodes] at hn; omega) hβ
            exact Finset.Subset.trans (Finset.union_subset_union ha hb) Finset.subset_union_right
        have quant (q : Quantifier)
            (hb : (match p with
              | .lam x a => do return Formula.quant (L := ForcingFormulas.membershipLanguage) q x (← parse a)
              | _ => none) = some φ) : names φ ⊆ syntaxNames (.app k p) := by
          cases p with
          | var => simp at hb
          | app => simp at hb
          | lam x a =>
            change (parse a).bind (fun α => some (Formula.quant q x α)) = some φ at hb
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
            obtain ⟨α, hα, rfl⟩ := hb
            have ha := ih a α (by simp only [Term.nodes] at hn; omega) hα
            exact Finset.Subset.trans (Finset.insert_subset_insert x ha) Finset.subset_union_right
        rw [parse.eq_def] at hp
        dsimp only at hp
        split_ifs at hp with h0 hp0 h1 h2 h3 h4 h5 h6 h7
        · cases hp; simp [names]
        · cases p with
          | var => simp at hp
          | lam => simp at hp
          | app a b =>
            cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at hp
            subst φ
            simp [names, syntaxNames, termName]
        · cases p with
          | var => simp at hp
          | lam => simp at hp
          | app a b =>
            cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at hp
            subst φ
            simp [names, syntaxNames, termName]
        · apply binary .conj; cases p <;> exact hp
        · apply binary .disj; cases p <;> exact hp
        · apply binary .imp; cases p <;> exact hp
        · apply quant .all; cases p <;> exact hp
        · apply quant .ex; cases p <;> exact hp
  exact aux M.nodes M φ le_rfl hp

theorem parseCode_name_bound {a : ℕ} {A : FOL} (hA : parseCode a = some A)
    {x : ℕ} (hx : x ∈ names A) : x ≤ a := by
  have h := syntaxName_le_code (Term.decode a) (parse_names_subset _ A hA hx)
  simpa only [Term.code_decode] using h

/-- The raw-code matcher has the same full template specification for every
successful parse, with no canonical-tag assumption on its numerical inputs. -/
theorem EqualityMatcher.rawCheck_parsed_iff {a b : ℕ} {A B : FOL}
    (hA : parseCode a = some A) (hB : parseCode b = some B) (t r : ℕ) :
    rawCheck a b t r = true ↔
      ∃ (φ : FOL) (x : ℕ), (φ.subst x (.var t)).Alpha A ∧ (φ.subst x (.var r)).Alpha B := by
  have ha := (Term.alpha_iff_bindingTree _ _).mp (parse_sound (Term.decode a) A hA)
  have hb := (Term.alpha_iff_bindingTree _ _).mp (parse_sound (Term.decode b) B hB)
  rw [rawCheck, ha, hb]
  apply check_formula_iff A B t r (freshName a b)
  · intro hz
    have := parseCode_name_bound hA hz
    simp only [freshName] at this
    omega
  · intro hz
    have := parseCode_name_bound hB (fv_subset_names B hz)
    simp only [freshName] at this
    omega

end PolishSpaceBook.FirstOrderLambdaEncoding
