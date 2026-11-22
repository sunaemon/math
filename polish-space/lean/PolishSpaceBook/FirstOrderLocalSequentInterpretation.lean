module

public import PolishSpaceBook.FirstOrderLocalRulePrograms

@[expose] public section

/-! # Decoding arbitrary numerical sequent labels

The parser retains raw bound names and accepts the actual grammar, including
alpha-renamed closed tags. Context interpretation forgets order and repetition.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedFirstOrder
open ForcingFormulas (membershipLanguage)

namespace LocalRulePrograms
noncomputable local instance rawAlphaTermDecidableEq : DecidableEq AlphaTerm := Classical.decEq _

def parseFormulaList : List ℕ → Option (List FOL)
  | [] => some []
  | a :: as => do return (← parseCode a) :: (← parseFormulaList as)

def parseContext (e : ℕ) : Option (List FOL) := parseFormulaList (NatListCode.decode e)

noncomputable def parseSequent (n : ℕ) : Option (Sequent membershipLanguage) := do
  let Γ ← parseContext n.unpair.1
  let φ ← parseCode n.unpair.2
  return (ContextPrograms.context Γ, AlphaFormula.mk φ)

theorem parseFormulaList_some_iff (xs : List ℕ) (φs : List FOL) :
    parseFormulaList xs = some φs ↔ List.Forall₂ (fun a φ => parseCode a = some φ) xs φs := by
  induction xs generalizing φs with
  | nil => cases φs <;> simp [parseFormulaList]
  | cons a as ih =>
    cases φs <;> simp [parseFormulaList, Option.bind_eq_some_iff, ih]

theorem parseFormulaList_exists (xs : List ℕ) :
    (∃ φs, parseFormulaList xs = some φs) ↔ ∀ a ∈ xs, ∃ φ, parseCode a = some φ := by
  induction xs with
  | nil => simp [parseFormulaList]
  | cons a as ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    cases ha : parseCode a <;> cases hs : parseFormulaList as <;>
      simp [parseFormulaList, ha, hs]

theorem wellFormed_iff_parseContext (e : ℕ) :
    ContextPrograms.wellFormed e = true ↔ ∃ Γ, parseContext e = some Γ := by
  rw [parseContext, parseFormulaList_exists, ContextPrograms.wellFormed_iff]
  constructor
  · intro h a ha
    obtain ⟨φ, hφ⟩ := h a ha
    obtain ⟨ψ, hψ, _⟩ := parse_complete hφ
    exact ⟨ψ, hψ⟩
  · intro h a ha
    obtain ⟨φ, hφ⟩ := h a ha
    exact ⟨φ, parse_sound _ _ hφ⟩

@[simp] theorem parseFormulaList_encode (Γ : List FOL) :
    parseFormulaList (Γ.map (fun φ => (encode φ).code)) = some Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [parseFormulaList, ih]

@[simp] theorem parseContext_listCode (Γ : List FOL) :
    parseContext (ContextPrograms.listCode Γ) = some Γ := by
  simp [parseContext, ContextPrograms.listCode]

@[simp] theorem parseSequent_encode (Γ : List FOL) (φ : FOL) :
    parseSequent (Nat.pair (ContextPrograms.listCode Γ) (encode φ).code) =
      some (ContextPrograms.context Γ, AlphaFormula.mk φ) := by
  simp [parseSequent]

theorem parseSequent_some_iff (n : ℕ) (s : Sequent membershipLanguage) :
    parseSequent n = some s ↔ ∃ Γ φ, parseContext n.unpair.1 = some Γ ∧
      parseCode n.unpair.2 = some φ ∧ s = (ContextPrograms.context Γ, AlphaFormula.mk φ) := by
  cases hΓ : parseContext n.unpair.1 <;> cases hφ : parseCode n.unpair.2 <;>
    simp [parseSequent, hΓ, hφ, eq_comm]

theorem parseCode_alpha_iff {a b : ℕ} {φ ψ : FOL}
    (ha : parseCode a = some φ) (hb : parseCode b = some ψ) :
    (Term.decode a).Alpha (Term.decode b) ↔ AlphaFormula.mk φ = AlphaFormula.mk ψ := by
  have hφ := parse_sound _ _ ha
  have hψ := parse_sound _ _ hb
  rw [AlphaFormula.mk_eq_iff, ← encode_alpha_iff]
  exact ⟨fun h => hφ.symm.trans (h.trans hψ), fun h => hφ.trans (h.trans hψ.symm)⟩

theorem parseCode_fv {a : ℕ} {φ : FOL} (ha : parseCode a = some φ) :
    (Term.decode a).fv = φ.fv := by
  simpa only [encode_fv] using (parse_sound _ _ ha).fv_eq

theorem parseContext_raw {e : ℕ} {Γ : List FOL} (h : parseContext e = some Γ) :
    ContextPrograms.rawContext e = (ContextPrograms.context Γ).image encodeClass := by
  classical
  have hr := (parseFormulaList_some_iff _ _).mp h
  clear h
  change ((NatListCode.decode e).map (fun a => AlphaTerm.mk (Term.decode a))).toFinset = _
  generalize NatListCode.decode e = xs at hr ⊢
  induction hr with
  | nil => simp [ContextPrograms.context]
  | @cons a φ as Γ hφ _ ih =>
    have he : AlphaTerm.mk (Term.decode a) = encodeClass (AlphaFormula.mk φ) :=
      (AlphaTerm.mk_eq_iff _ _).mpr (parse_sound _ _ hφ)
    simpa only [List.map_cons, List.toFinset_cons, ContextPrograms.context_cons,
      Finset.image_insert, he] using congrArg (insert (encodeClass (AlphaFormula.mk φ))) ih

theorem parseContext_equal {e d : ℕ} {Γ Δ : List FOL}
    (he : parseContext e = some Γ) (hd : parseContext d = some Δ) :
    ContextPrograms.equalBit e d = true ↔ ContextPrograms.context Γ = ContextPrograms.context Δ := by
  classical
  rw [ContextPrograms.equalBit_iff, parseContext_raw he, parseContext_raw hd]
  exact ⟨fun h => Finset.image_injective encodeClass_injective h, congrArg (Finset.image encodeClass)⟩

theorem parseContext_member {a e : ℕ} {φ : FOL} {Γ : List FOL}
    (ha : parseCode a = some φ) (he : parseContext e = some Γ) :
    ContextPrograms.member a e = true ↔ AlphaFormula.mk φ ∈ ContextPrograms.context Γ := by
  classical
  rw [ContextPrograms.member_rawContext, parseContext_raw he]
  have hφ : AlphaTerm.mk (Term.decode a) = encodeClass (AlphaFormula.mk φ) :=
    (AlphaTerm.mk_eq_iff _ _).mpr (parse_sound _ _ ha)
  rw [hφ, Finset.mem_image]
  exact ⟨fun ⟨ψ, hψ, he⟩ => encodeClass_injective he ▸ hψ, fun h => ⟨_, h, rfl⟩⟩

theorem parseContext_free {e : ℕ} {Γ : List FOL} (h : parseContext e = some Γ) (x : ℕ) :
    ContextPrograms.hasFree x e = true ↔ x ∈ (ContextPrograms.context Γ).fv := by
  classical
  have hr := (parseFormulaList_some_iff _ _).mp h
  clear h
  have he : (NatListCode.decode e).any (fun a => decide (x ∈ (Term.decode a).fv)) =
      Γ.any (fun φ => decide (x ∈ φ.fv)) := by
    generalize NatListCode.decode e = xs at hr ⊢
    induction hr with
    | nil => rfl
    | cons hφ _ ih => simp only [List.any_cons, parseCode_fv hφ, ih]
  rw [ContextPrograms.hasFree, he, ContextPrograms.mem_context_fv]
  simp

@[simp] theorem parseContext_cons (a e : ℕ) :
    parseContext (Nat.pair a e + 1) = do return (← parseCode a) :: (← parseContext e) := by
  simp only [parseContext, NatListCode.decode, Nat.unpair_pair, parseFormulaList]

theorem validSequent_ne_zero (s : P) (n : ℕ) :
    (Program.validSequent s).value n ≠ 0 ↔ ∃ q, parseSequent (s.value n) = some q := by
  change (if ContextPrograms.wellFormed (s.value n).unpair.1 then 1 else 0) *
    (if (parseCode (s.value n).unpair.2).isSome then 1 else 0) ≠ (0 : ℕ) ↔ _
  rw [Nat.mul_ne_zero_iff]
  have bit (b : Bool) : (if b then 1 else 0 : ℕ) ≠ 0 ↔ b = true := by cases b <;> decide
  rw [bit, bit, wellFormed_iff_parseContext]
  cases hΓ : parseContext (s.value n).unpair.1 <;> cases hφ : parseCode (s.value n).unpair.2 <;>
    simp [parseSequent, hΓ, hφ]

end LocalRulePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
