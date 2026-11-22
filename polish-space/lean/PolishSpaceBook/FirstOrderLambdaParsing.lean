module

public import PolishSpaceBook.FirstOrderLambdaTests

@[expose] public section

/-! # Parsing membership-formula lambda data

Parsing descends through finite syntax and compares rigid tags by the implemented
alpha test. Atomic fields must be variables, binary fields must have two children,
and quantifier fields must be abstractions. Thus arbitrary numerical codes have
a total parser, without assuming that they encode well-formed formulas.
-/

namespace PolishSpaceBook.FirstOrderLambdaEncoding
open FirstOrder Language NamedFirstOrder NamedLambda
open ForcingFormulas (membershipLanguage MembershipSymbol)

@[simp] theorem tag_alpha_iff (n m : ℕ) : (tag n).Alpha (tag m) ↔ n = m := by
  rw [Term.alpha_iff_renameEq, Term.renameEq_iff_nameRel, tag_nameRel_iff]

/-- Recognize the grammar, retaining raw binder names and allowing alpha-renamed
closed tags. Every recursive argument is a proper syntax subtree. -/
def parse : LTerm → Option FOL
  | .app k p =>
    if k.Alpha (tag 0) then
      if p.Alpha (tag 0) then some .falsum else none
    else if k.Alpha (tag 1) then
      match p with
      | .app (.var x) (.var y) => some (.equal (.var x) (.var y))
      | _ => none
    else if k.Alpha (tag 2) then
      match p with
      | .app (.var x) (.var y) => some (.rel MembershipSymbol.mem ![.var x, .var y])
      | _ => none
    else if k.Alpha (tag 3) then
      match p with
      | .app a b => do return .binary .conj (← parse a) (← parse b)
      | _ => none
    else if k.Alpha (tag 4) then
      match p with
      | .app a b => do return .binary .disj (← parse a) (← parse b)
      | _ => none
    else if k.Alpha (tag 5) then
      match p with
      | .app a b => do return .binary .imp (← parse a) (← parse b)
      | _ => none
    else if k.Alpha (tag 6) then
      match p with
      | .lam x a => return .quant .all x (← parse a)
      | _ => none
    else if k.Alpha (tag 7) then
      match p with
      | .lam x a => return .quant .ex x (← parse a)
      | _ => none
    else none
  | _ => none
termination_by t => t.nodes
decreasing_by all_goals simp only [Term.nodes]; omega

/-- Every encoded formula parses back to the original named formula. -/
@[simp] theorem parse_encode (φ : FOL) : parse (encode φ) = some φ := by
  induction φ with
  | falsum => simp [encode, node, parse.eq_def]
  | equal s t => simp [encode, node, parse.eq_def]
  | rel r ts =>
    cases r
    have ht : ![ts 0, ts 1] = ts := by funext i; fin_cases i <;> rfl
    simpa [encode, node, parse.eq_def] using congrArg (fun us => some (Formula.rel
      (L := membershipLanguage) MembershipSymbol.mem us)) ht
  | binary c φ ψ ihφ ihψ =>
    cases c <;> rw [encode, node, parse.eq_def] <;> simp [connectiveCode, ihφ, ihψ]
  | quant q x φ ih =>
    cases q <;> rw [encode, node, parse.eq_def] <;> simp [quantifierCode, ih]

/-- Successful parsing certifies the actual formula grammar, up to changes of
bound names inside the rigid closed tags. -/
theorem parse_sound (t : LTerm) (φ : FOL) (h : parse t = some φ) : t.Alpha (encode φ) := by
  have aux : ∀ n (t : LTerm) (φ : FOL), t.nodes ≤ n → parse t = some φ → t.Alpha (encode φ) := by
    intro n
    induction n with
    | zero => intro t φ hn; have := t.nodes_pos; omega
    | succ n ih =>
      intro t φ hn h
      cases t with
      | var => simp [parse.eq_def] at h
      | lam => simp [parse.eq_def] at h
      | app k p =>
        have binary (c : Connective) (ht : k.Alpha (tag (connectiveCode c)))
            (hb : (match p with
              | .app a b => do return Formula.binary c (← parse a) (← parse b)
              | _ => none) = some φ) : (Term.app k p).Alpha (encode φ) := by
          cases p with
          | var => simp at hb
          | lam => simp at hb
          | app a b =>
            change (parse a).bind (fun α => (parse b).bind (fun β => some (Formula.binary c α β))) = some φ at hb
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
            obtain ⟨α, hα, β, hβ, rfl⟩ := hb
            exact ht.app ((ih a α (by simp only [Term.nodes] at hn; omega) hα).app
              (ih b β (by simp only [Term.nodes] at hn; omega) hβ))
        have quant (q : Quantifier) (ht : k.Alpha (tag (quantifierCode q)))
            (hb : (match p with
              | .lam x a => do return Formula.quant q x (← parse a)
              | _ => none) = some φ) : (Term.app k p).Alpha (encode φ) := by
          cases p with
          | var => simp at hb
          | app => simp at hb
          | lam x a =>
            change (parse a).bind (fun α => some (Formula.quant q x α)) = some φ at hb
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
            obtain ⟨α, hα, rfl⟩ := hb
            exact ht.app ((ih a α (by simp only [Term.nodes] at hn; omega) hα).lam x)
        rw [parse.eq_def] at h
        dsimp only at h
        split_ifs at h with h₀ hp₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
        · cases h
          exact h₀.app hp₀
        · cases p with
          | var => simp at h
          | lam => simp at h
          | app a b =>
            cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at h
            subst φ
            exact h₁.app ((Term.Alpha.refl _).app (.refl _))
        · cases p with
          | var => simp at h
          | lam => simp at h
          | app a b =>
            cases a <;> cases b <;> simp only [Option.some.injEq, reduceCtorEq] at h
            subst φ
            exact h₂.app ((Term.Alpha.refl _).app (.refl _))
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
  exact aux t.nodes t φ le_rfl h

theorem alpha_tag_index_iff {t : LTerm} {n : ℕ} (h : t.Alpha (tag n)) (m : ℕ) :
    t.Alpha (tag m) ↔ n = m := by
  constructor
  · intro hm
    exact (tag_alpha_iff _ _).mp (h.symm.trans hm)
  · rintro rfl
    exact h

theorem source_tag_alpha {R : ℕ → ℕ → Prop} {t : LTerm} {n : ℕ}
    (h : Term.NameRel R t (tag n)) : t.Alpha (tag n) := by
  apply (Term.alpha_iff_renameEq _ _).mpr
  apply Term.NameRel.eq_renameEq
  exact h.congr (by simp)

theorem parse_tagged_falsum {k p : LTerm} (hk : k.Alpha (tag 0)) (hp : p.Alpha (tag 0)) :
    parse (.app k p) = some (.falsum : FOL) := by
  rw [parse.eq_def]
  simp [hk, hp]

theorem parse_tagged_equal {k : LTerm} (hk : k.Alpha (tag 1)) (x y : ℕ) :
    parse (.app k (.app (.var x) (.var y))) = some (.equal (.var x) (.var y) : FOL) := by
  rw [parse.eq_def]
  simp [alpha_tag_index_iff hk]

theorem parse_tagged_mem {k : LTerm} (hk : k.Alpha (tag 2)) (x y : ℕ) :
    parse (.app k (.app (.var x) (.var y))) =
      some (.rel MembershipSymbol.mem ![.var x, .var y] : FOL) := by
  rw [parse.eq_def]
  simp [alpha_tag_index_iff hk]

theorem parse_tagged_binary {k a b : LTerm} (c : Connective)
    (hk : k.Alpha (tag (connectiveCode c))) {φ ψ : FOL}
    (ha : parse a = some φ) (hb : parse b = some ψ) :
    parse (.app k (.app a b)) = some (.binary c φ ψ) := by
  cases c <;> rw [parse.eq_def] <;> simp [alpha_tag_index_iff hk, connectiveCode, ha, hb]

theorem parse_tagged_quant {k a : LTerm} (q : Quantifier) (x : ℕ)
    (hk : k.Alpha (tag (quantifierCode q))) {φ : FOL} (ha : parse a = some φ) :
    parse (.app k (.lam x a)) = some (.quant q x φ) := by
  cases q <;> rw [parse.eq_def] <;> simp [alpha_tag_index_iff hk, quantifierCode, ha]

/-- Every syntax term comparing with an encoded formula parses, and the output
retains the same correspondence of free and bound names. -/
theorem parse_complete_nameRel (φ : FOL) : ∀ (R : ℕ → ℕ → Prop) (t : LTerm),
    Term.NameRel R t (encode φ) →
      ∃ ψ : FOL, parse t = some ψ ∧ Formula.NameRel R ψ φ := by
  induction φ with
  | falsum =>
    intro R t h
    cases h with
    | app hk hp => exact ⟨.falsum, parse_tagged_falsum (source_tag_alpha hk)
        (source_tag_alpha hp), .falsum _⟩
  | equal s r =>
    intro R t h
    cases h with
    | app hk hp =>
      cases hp with
      | app hs hr =>
        cases hs with
        | @var _ x _ hx =>
          cases hr with
          | @var _ y _ hy =>
            refine ⟨.equal (.var x) (.var y), parse_tagged_equal (source_tag_alpha hk) x y, ?_⟩
            exact .equal ((termRel_iff _ _ _).mpr hx) ((termRel_iff _ _ _).mpr hy)
  | rel r ts =>
    cases r
    intro R t h
    cases h with
    | app hk hp =>
      cases hp with
      | app hs hr =>
        cases hs with
        | @var _ x _ hx =>
          cases hr with
          | @var _ y _ hy =>
            refine ⟨.rel MembershipSymbol.mem ![.var x, .var y],
              parse_tagged_mem (source_tag_alpha hk) x y, ?_⟩
            apply Formula.NameRel.rel (L := membershipLanguage) MembershipSymbol.mem
            intro i
            fin_cases i
            · exact (termRel_iff _ _ _).mpr hx
            · exact (termRel_iff _ _ _).mpr hy
  | binary c φ ψ ihφ ihψ =>
    intro R t h
    cases h with
    | app hk hp =>
      cases hp with
      | app hφ hψ =>
        obtain ⟨φ', hpφ, hrφ⟩ := ihφ R _ hφ
        obtain ⟨ψ', hpψ, hrψ⟩ := ihψ R _ hψ
        exact ⟨.binary c φ' ψ', parse_tagged_binary c (source_tag_alpha hk) hpφ hpψ,
          .binary c hrφ hrψ⟩
  | quant q x φ ih =>
    intro R t h
    cases h with
    | app hk hp =>
      cases hp with
      | @lam _ y _ _ _ hφ =>
        obtain ⟨φ', hpφ, hrφ⟩ := ih _ _ hφ
        exact ⟨.quant q y φ', parse_tagged_quant q y (source_tag_alpha hk) hpφ, .quant q hrφ⟩

theorem parse_complete {t : LTerm} {φ : FOL} (h : t.Alpha (encode φ)) :
    ∃ ψ : FOL, parse t = some ψ ∧ ψ.Alpha φ := by
  obtain ⟨ψ, hp, hr⟩ := parse_complete_nameRel φ Eq t
    ((Term.renameEq_iff_nameRel _ _).mp ((Term.alpha_iff_renameEq _ _).mp h))
  exact ⟨ψ, hp, (Formula.alpha_iff_nameRel _ _).mpr hr⟩

/-- Total parsing on every natural input, including malformed formula data. -/
def parseCode (n : ℕ) : Option FOL := parse (Term.decode n)

@[simp] theorem parseCode_encode (φ : FOL) : parseCode (encode φ).code = some φ := by
  simp [parseCode]

/-- Rejection means exactly that the arbitrary numerical input is not a formula
encoding, even allowing alpha-renamed tags and binders. -/
theorem parseCode_none_iff (n : ℕ) :
    parseCode n = none ↔ ¬∃ φ : FOL, (Term.decode n).Alpha (encode φ) := by
  constructor
  · intro hn ⟨φ, hφ⟩
    obtain ⟨ψ, hp, _⟩ := parse_complete hφ
    simp [parseCode, hp] at hn
  · intro hn
    cases hp : parse (Term.decode n) with
    | none => exact hp
    | some φ => exact (hn ⟨φ, parse_sound _ _ hp⟩).elim

end PolishSpaceBook.FirstOrderLambdaEncoding
