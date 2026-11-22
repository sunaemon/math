module

public import PolishSpaceBook.FirstOrderDeductionSemantics

@[expose] public section

/-!
# Simultaneous permutation of first-order variable names

Both free and bound names are permuted. Substitution commutes with this operation
on alpha-classes, even though the prescribed least fresh name need not commute
with a permutation on raw syntax.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v
variable {L : Language.{u,v}}

namespace TermRel

theorem relabel {R S : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r)
    (e f : ℕ → ℕ) (hs : ∀ a b, R a b → S (e a) (f b)) :
    TermRel S (t.relabel e) (r.relabel f) := by
  induction h with
  | var h => exact .var (hs _ _ h)
  | func g h ih => exact .func g ih

theorem graph (e : ℕ → ℕ) (t : L.Term ℕ) : TermRel (fun a b => b = e a) t (t.relabel e) := by
  simpa only [Term.relabel_id] using (refl t).relabel id e (by intro a b h; subst b; rfl)

end TermRel
namespace Formula

def permute (e : Equiv.Perm ℕ) : Formula L → Formula L
  | .falsum => .falsum
  | .equal t r => .equal (t.relabel e) (r.relabel e)
  | .rel r ts => .rel r (fun i => (ts i).relabel e)
  | .binary c φ ψ => .binary c (permute e φ) (permute e ψ)
  | .quant q x φ => .quant q (e x) (permute e φ)

theorem NameRel.permute {R S : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ)
    (e f : Equiv.Perm ℕ) (hs : ∀ a b, R a b → S (e a) (f b)) :
    NameRel S (φ.permute e) (ψ.permute f) := by
  induction h generalizing S with
  | falsum => exact .falsum _
  | equal ht hr => exact .equal (ht.relabel e f hs) (hr.relabel e f hs)
  | rel r ht => exact .rel r (fun i => (ht i).relabel e f hs)
  | binary c hφ hψ ihφ ihψ => exact .binary c (ihφ hs) (ihψ hs)
  | @quant q R x y φ ψ h ih =>
    apply NameRel.quant q
    apply ih
    intro a b hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨fun he => ha (e.injective he), fun he => hb (f.injective he), hs a b hab⟩

@[simp] theorem permute_id (φ : Formula L) : φ.permute (Equiv.refl ℕ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t r => simp [permute, Term.relabel_id]
  | rel r ts => simp [permute, Term.relabel_id]
  | binary c φ ψ ihφ ihψ => simp [permute, ihφ, ihψ]
  | quant q x φ ih => simp [permute, ih]

@[simp] theorem permute_comp (φ : Formula L) (e f : Equiv.Perm ℕ) :
    (φ.permute e).permute f = φ.permute (e.trans f) := by
  induction φ with
  | falsum => rfl
  | equal t r => simp [permute]
  | rel r ts => simp [permute]
  | binary c φ ψ ihφ ihψ => simp [permute, ihφ, ihψ]
  | quant q x φ ih => simp [permute, ih]

theorem nameRel_permute (φ : Formula L) (e : Equiv.Perm ℕ) :
    NameRel (fun a b => b = e a) φ (φ.permute e) := by
  simpa only [permute_id, Equiv.refl_apply] using
    (NameRel.refl φ).permute (Equiv.refl ℕ) e (by intro a b h; subst b; rfl)

theorem Alpha.permute {φ ψ : Formula L} (h : Alpha φ ψ) (e : Equiv.Perm ℕ) :
    Alpha (φ.permute e) (ψ.permute e) :=
  (h.nameRel.permute e e (by intro a b h; rw [h])).eq_alpha

theorem permute_fixed (φ : Formula L) (e : Equiv.Perm ℕ) (h : ∀ x ∈ φ.fv, e x = x) :
    Alpha (φ.permute e) φ := by
  apply Alpha.symm
  apply NameRel.eq_alpha
  apply (nameRel_permute φ e).congr
  intro a ha b _ hab
  exact (hab.trans (h a ha)).symm

theorem fv_permute (φ : Formula L) (e : Equiv.Perm ℕ) :
    (φ.permute e).fv = φ.fv.image e := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := (nameRel_permute φ e).symm.fv_left hb
    exact Finset.mem_image.mpr ⟨a, ha, hab.symm⟩
  · rintro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨b, hb, rfl⟩ := (nameRel_permute φ e).fv_left ha
    exact hb

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: prose
  excerpt: |
    For a permutation $e$ of the variable set, extend $e$ to terms and formulas by changing every variable name,
    including bound names, and leaving function symbols, relation symbols, and logical operations unchanged.
    For a finite context, put $e(\Gamma):=\{e(\psi):\psi\in\Gamma\}$.
    This operation respects $\alpha$-equivalence. Moreover,
    $$\begin{aligned}
    \FreeVars{e(\varphi)}&=e[\FreeVars{\varphi}],\\
    e(\varphi\subst{x}{t})&=e(\varphi)\subst{e(x)}{e(t)}.
    \end{aligned}$$
    These are identities of $\alpha$-classes. To verify them, compare each free name $a$ with $e(a)$ using
    \termuse{comparison of named first-order formulas}. At a binder, injectivity preserves the distinction between
    its bound name and the other names. The free-variable identity follows in both directions from this comparison;
    the substitution identity follows from the substitution compatibility lemma. In particular, if $e$ fixes all
    free variables of a formula, it fixes its $\alpha$-class. No equivariance of the least-fresh-name choice is required.
-/
theorem permute_subst (φ : Formula L) (e : Equiv.Perm ℕ) (x : ℕ) (t : L.Term ℕ) :
    Alpha ((φ.subst x t).permute e) ((φ.permute e).subst (e x) (t.relabel e)) := by
  have hs := (nameRel_permute φ e).subst x (e x) (TermRel.graph e t)
    (by intro a b h; subst b; exact e.injective.eq_iff.symm)
    (by intro a b h _; exact h)
  exact ((nameRel_permute (φ.subst x t) e).symm.trans hs
    (by intro a b c h₁ h₂; exact h₁.trans h₂.symm)).eq_alpha

end Formula
namespace AlphaFormula

def permute (e : Equiv.Perm ℕ) : AlphaFormula L → AlphaFormula L :=
  Quotient.map (Formula.permute e) (by intro a b h; exact h.permute e)

@[simp] theorem permute_mk (e : Equiv.Perm ℕ) (φ : Formula L) :
    (mk φ).permute e = mk (φ.permute e) := rfl

@[simp] theorem permute_id (φ : AlphaFormula L) : φ.permute (Equiv.refl ℕ) = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.permute_id φ)

@[simp] theorem permute_comp (φ : AlphaFormula L) (e f : Equiv.Perm ℕ) :
    (φ.permute e).permute f = φ.permute (e.trans f) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.permute_comp φ e f)

@[simp] theorem permute_falsum (e : Equiv.Perm ℕ) : (falsum : AlphaFormula L).permute e = falsum := rfl

@[simp] theorem permute_equal (e : Equiv.Perm ℕ) (t r : L.Term ℕ) :
    (equal t r).permute e = equal (t.relabel e) (r.relabel e) := rfl

@[simp] theorem permute_binary (e : Equiv.Perm ℕ) (c : Connective) (φ ψ : AlphaFormula L) :
    (binary c φ ψ).permute e = binary c (φ.permute e) (ψ.permute e) := by
  induction φ using Quotient.inductionOn with
  | _ φ => induction ψ using Quotient.inductionOn with
    | _ ψ => rfl

@[simp] theorem permute_quant (e : Equiv.Perm ℕ) (q : Quantifier) (x : ℕ) (φ : AlphaFormula L) :
    (quant q x φ).permute e = quant q (e x) (φ.permute e) := by
  induction φ using Quotient.inductionOn with
  | _ φ => rfl

@[simp] theorem permute_subst (e : Equiv.Perm ℕ) (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).permute e = (φ.permute e).subst (e x) (t.relabel e) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Quotient.sound (Formula.permute_subst φ e x t)

theorem permute_fixed (φ : AlphaFormula L) (e : Equiv.Perm ℕ) (h : ∀ x ∈ φ.fv, e x = x) :
    φ.permute e = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Quotient.sound (Formula.permute_fixed φ e h)

@[simp] theorem fv_permute (φ : AlphaFormula L) (e : Equiv.Perm ℕ) :
    (φ.permute e).fv = φ.fv.image e := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.fv_permute φ e

theorem permute_swap_fixed (φ : AlphaFormula L) (x z : ℕ) (hx : x ∉ φ.fv) (hz : z ∉ φ.fv) :
    φ.permute (Equiv.swap x z) = φ := by
  apply φ.permute_fixed
  intro a ha
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hz (h ▸ ha))

@[simp] theorem mem_fv_permute (φ : AlphaFormula L) (e : Equiv.Perm ℕ) (x : ℕ) :
    e x ∈ (φ.permute e).fv ↔ x ∈ φ.fv := by
  simp

end AlphaFormula

noncomputable section
namespace Context
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

def permute (e : Equiv.Perm ℕ) (Γ : Context L) : Context L := Γ.image (AlphaFormula.permute e)

@[simp] theorem permute_insert (e : Equiv.Perm ℕ) (Γ : Context L) (φ : AlphaFormula L) :
    (insert φ Γ).permute e = insert (φ.permute e) (Γ.permute e) := by
  simp [permute]

@[simp] theorem permute_id (Γ : Context L) : Γ.permute (Equiv.refl ℕ) = Γ := by
  change Γ.image (AlphaFormula.permute (Equiv.refl ℕ)) = Γ
  rw [show AlphaFormula.permute (L := L) (Equiv.refl ℕ) = id from
    funext AlphaFormula.permute_id, Finset.image_id]

theorem mem_fv_of_mem {Γ : Context L} {φ : AlphaFormula L} (hφ : φ ∈ Γ) {x : ℕ}
    (hx : x ∈ φ.fv) : x ∈ Γ.fv := Finset.mem_biUnion.mpr ⟨φ, hφ, hx⟩

theorem fv_mono {Γ Δ : Context L} (h : Γ ⊆ Δ) : Γ.fv ⊆ Δ.fv := by
  intro x hx
  obtain ⟨φ, hφ, hx⟩ := Finset.mem_biUnion.mp hx
  exact mem_fv_of_mem (h hφ) hx

@[simp] theorem fv_permute (Γ : Context L) (e : Equiv.Perm ℕ) :
    (Γ.permute e).fv = Γ.fv.image e := by
  ext x
  constructor
  · intro hx
    obtain ⟨ψ, hψ, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
    rw [AlphaFormula.fv_permute] at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨a, mem_fv_of_mem hφ ha, rfl⟩
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨φ, hφ, ha⟩ := Finset.mem_biUnion.mp ha
    exact mem_fv_of_mem (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩)
      ((AlphaFormula.mem_fv_permute φ e a).mpr ha)

@[simp] theorem mem_fv_permute (Γ : Context L) (e : Equiv.Perm ℕ) (x : ℕ) :
    e x ∈ (Γ.permute e).fv ↔ x ∈ Γ.fv := by
  simp

end Context
end
end PolishSpaceBook.NamedFirstOrder
