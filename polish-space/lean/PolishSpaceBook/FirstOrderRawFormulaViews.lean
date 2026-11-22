module

public import PolishSpaceBook.FirstOrderLocalRulePrograms

@[expose] public section

/-! # Exact constructor views of successfully parsed raw formula data

The raw closed tags may have arbitrary alpha-equivalent bound names. Parsing
retains the actual formula binders and exposes the actual syntax fields.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage MembershipSymbol)

inductive ParsedShape : LTerm → FOL → Prop where
  | falsum {k p : LTerm} (hk : k.Alpha (tag 0)) (hp : p.Alpha (tag 0)) :
      ParsedShape (.app k p) .falsum
  | equal {k : LTerm} (x y : ℕ) (hk : k.Alpha (tag 1)) :
      ParsedShape (.app k (.app (.var x) (.var y))) (.equal (.var x) (.var y))
  | mem {k : LTerm} (x y : ℕ) (hk : k.Alpha (tag 2)) :
      ParsedShape (.app k (.app (.var x) (.var y))) (.rel MembershipSymbol.mem ![.var x, .var y])
  | binary {k a b : LTerm} (c : Connective) {φ ψ : FOL}
      (hk : k.Alpha (tag (connectiveCode c))) (ha : parse a = some φ) (hb : parse b = some ψ) :
      ParsedShape (.app k (.app a b)) (.binary c φ ψ)
  | quant {k a : LTerm} (q : Quantifier) (x : ℕ) {φ : FOL}
      (hk : k.Alpha (tag (quantifierCode q))) (ha : parse a = some φ) :
      ParsedShape (.app k (.lam x a)) (.quant q x φ)

theorem parsedShape_of_parse {t : LTerm} {φ : FOL} (h : parse t = some φ) : ParsedShape t φ := by
  cases t with
  | var => simp [parse.eq_def] at h
  | lam => simp [parse.eq_def] at h
  | app k p =>
    have binary (c : Connective) (hk : k.Alpha (tag (connectiveCode c)))
        (hb : (match p with
          | .app a b => do return Formula.binary c (← parse a) (← parse b)
          | _ => none) = some φ) : ParsedShape (.app k p) φ := by
      cases p with
      | var => simp at hb
      | lam => simp at hb
      | app a b =>
        change (parse a).bind (fun α => (parse b).bind (fun β => some (Formula.binary c α β))) = some φ at hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
        obtain ⟨α, hα, β, hβ, rfl⟩ := hb
        exact .binary c hk hα hβ
    have quant (q : Quantifier) (hk : k.Alpha (tag (quantifierCode q)))
        (hb : (match p with
          | .lam x a => do return Formula.quant q x (← parse a)
          | _ => none) = some φ) : ParsedShape (.app k p) φ := by
      cases p with
      | var => simp at hb
      | app => simp at hb
      | lam x a =>
        change (parse a).bind (fun α => some (Formula.quant q x α)) = some φ at hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
        obtain ⟨α, hα, rfl⟩ := hb
        exact .quant q x hk hα
    rw [parse.eq_def] at h
    dsimp only at h
    split_ifs at h with h₀ hp₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
    · cases h
      exact .falsum h₀ hp₀
    · cases p with
      | var => simp at h
      | lam => simp at h
      | app a b =>
        cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst φ
        exact .equal _ _ h₁
    · cases p with
      | var => simp at h
      | lam => simp at h
      | app a b =>
        cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst φ
        exact .mem _ _ h₂
    · apply binary .conj h₃
      cases p <;> exact h
    · apply binary .disj h₄
      cases p <;> exact h
    · apply binary .imp h₅
      cases p <;> exact h
    · apply quant .all h₆
      cases p <;> exact h
    · apply quant .ex h₇
      cases p <;> exact h

theorem ParsedShape.parse {t : LTerm} {φ : FOL} (h : ParsedShape t φ) : parse t = some φ := by
  cases h with
  | falsum hk hp => exact parse_tagged_falsum hk hp
  | equal x y hk => exact parse_tagged_equal hk x y
  | mem x y hk => exact parse_tagged_mem hk x y
  | binary c hk ha hb => exact parse_tagged_binary c hk ha hb
  | quant q x hk ha => exact parse_tagged_quant q x hk ha

theorem parse_iff_parsedShape (t : LTerm) (φ : FOL) : parse t = some φ ↔ ParsedShape t φ :=
  ⟨parsedShape_of_parse, ParsedShape.parse⟩

theorem parseCode_binary_iff (a : ℕ) (c : Connective) (φ ψ : FOL) :
    parseCode a = some (.binary c φ ψ) ↔ ∃ k M N : LTerm,
      Term.decode a = .app k (.app M N) ∧ k.Alpha (tag (connectiveCode c)) ∧
      parse M = some φ ∧ parse N = some ψ := by
  constructor
  · intro h
    change parse (Term.decode a) = _ at h
    generalize ht : Term.decode a = raw at h ⊢
    cases parsedShape_of_parse h with
    | binary c hk hM hN => exact ⟨_, _, _, rfl, hk, hM, hN⟩
  · rintro ⟨k, M, N, he, hk, hM, hN⟩
    change parse (Term.decode a) = _
    rw [he]
    exact parse_tagged_binary c hk hM hN

theorem parseCode_quant_iff (a : ℕ) (q : Quantifier) (x : ℕ) (φ : FOL) :
    parseCode a = some (.quant q x φ) ↔ ∃ k M : LTerm,
      Term.decode a = .app k (.lam x M) ∧ k.Alpha (tag (quantifierCode q)) ∧ parse M = some φ := by
  constructor
  · intro h
    change parse (Term.decode a) = _ at h
    generalize ht : Term.decode a = raw at h ⊢
    cases parsedShape_of_parse h with
    | quant q x hk hM => exact ⟨_, _, rfl, hk, hM⟩
  · rintro ⟨k, M, he, hk, hM⟩
    change parse (Term.decode a) = _
    rw [he]
    exact parse_tagged_quant q x hk hM

theorem parseCode_equal_iff (a : ℕ) (s t : membershipLanguage.Term ℕ) :
    parseCode a = some (.equal s t) ↔ ∃ k : LTerm,
      Term.decode a = .app k (.app (.var (termName s)) (.var (termName t))) ∧ k.Alpha (tag 1) := by
  constructor
  · intro h
    change parse (Term.decode a) = _ at h
    generalize ht : Term.decode a = raw at h ⊢
    cases parsedShape_of_parse h with
    | equal x y hk => exact ⟨_, rfl, hk⟩
  · rintro ⟨k, he, hk⟩
    change parse (Term.decode a) = _
    rw [he]
    simpa only [term_var_name] using parse_tagged_equal hk (termName s) (termName t)

theorem parseCode_mem_iff (a : ℕ) (ts : Fin 2 → membershipLanguage.Term ℕ) :
    parseCode a = some (.rel MembershipSymbol.mem ts) ↔ ∃ k : LTerm,
      Term.decode a = .app k (.app (.var (termName (ts 0))) (.var (termName (ts 1)))) ∧ k.Alpha (tag 2) := by
  constructor
  · intro h
    change parse (Term.decode a) = _ at h
    generalize ht : Term.decode a = raw at h ⊢
    cases parsedShape_of_parse h with
    | mem x y hk => exact ⟨_, rfl, hk⟩
  · rintro ⟨k, he, hk⟩
    have ht : ![FirstOrder.Language.Term.var (termName (ts 0)), FirstOrder.Language.Term.var (termName (ts 1))] = ts := by
      funext i
      fin_cases i <;> simp
    change parse (Term.decode a) = _
    rw [he]
    simpa only [ht] using parse_tagged_mem hk (termName (ts 0)) (termName (ts 1))

end PolishSpaceBook.FirstOrderLambdaEncoding
