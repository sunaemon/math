module

public import PolishSpaceBook.FirstOrderNamedAlpha
public import PolishSpaceBook.LambdaNameCorrespondence

@[expose] public section

/-!
# First-order terms under corresponding variable names

Function symbols and argument positions are unchanged; only variable names are
compared by the supplied relation. These terms are mathlib's standard syntax.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To prove that substitution respects $\alpha$-equivalence, compare expressions under a relation $R$ between variable
    names. Write $\FirstOrderNameCorrespondence{R}{t}{t'}$ when corresponding variables satisfy $R$ and function
    symbols and argument positions agree. For formulas, write $\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ when
    the outer constructors agree and their components compare. At an atomic formula, require the same relation symbol
    or equality sign and compare corresponding terms. At a binary connective, compare its two pairs of subformulas.
    The formula $\bot$ compares with itself.
    At quantifiers of the same kind with binders $x,y$, compare their bodies under the relation defined by
    $$\begin{aligned}
    \FirstOrderBoundNames{R}{x}{y}(a,b)\quad\Longleftrightarrow\quad
    &(a=x\land b=y)\\
    &{}\lor(a\ne x\land b\ne y\land R(a,b)).
    \end{aligned}$$
    Thus the new binders replace any earlier correspondence involving either bound name.
-/
inductive TermRel : (ℕ → ℕ → Prop) → L.Term ℕ → L.Term ℕ → Prop where
  | var {R : ℕ → ℕ → Prop} {a b : ℕ} : R a b → TermRel R (.var a) (.var b)
  | func {R : ℕ → ℕ → Prop} {n : ℕ} (f : L.Functions n)
      {ts us : Fin n → L.Term ℕ} :
      (∀ i, TermRel R (ts i) (us i)) → TermRel R (.func f ts) (.func f us)

namespace TermRel

theorem congr {R S : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r)
    (hs : ∀ a ∈ t.varFinset, ∀ b ∈ r.varFinset, R a b → S a b) : TermRel S t r := by
  induction h with
  | @var a b hab => exact .var (hs a (by simp) b (by simp) hab)
  | @func n f ts us h ih =>
    apply TermRel.func f
    intro i
    apply ih i
    intro a ha b hb hab
    exact hs a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
      b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩) hab

theorem mono {R S : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r)
    (hs : ∀ a b, R a b → S a b) : TermRel S t r :=
  h.congr (fun a _ b _ => hs a b)

theorem refl (t : L.Term ℕ) : TermRel Eq t t := by
  induction t with
  | var a => exact .var rfl
  | func f ts ih => exact .func f ih

theorem eq_eq {t r : L.Term ℕ} (h : TermRel Eq t r) : t = r := by
  induction h with
  | var h => rw [h]
  | func f h ih => congr 1; funext i; exact ih i

theorem symm {R : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r) :
    TermRel (fun b a => R a b) r t := by
  induction h with
  | var h => exact .var h
  | func f h ih => exact .func f ih

theorem fv_left {R : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r)
    {a : ℕ} (ha : a ∈ t.varFinset) : ∃ b ∈ r.varFinset, R a b := by
  induction h with
  | @var a' b hab =>
    have he : a = a' := by simpa using ha
    subst a'
    exact ⟨b, by simp, hab⟩
  | @func n f ts us h ih =>
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, hab⟩ := ih i hi
    exact ⟨b, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩, hab⟩

theorem trans {R S T : ℕ → ℕ → Prop} {t r a : L.Term ℕ}
    (h : TermRel R t r) (h' : TermRel S r a)
    (ht : ∀ x y z, R x y → S y z → T x z) : TermRel T t a := by
  induction h generalizing a with
  | var h => cases h' with | var h' => exact .var (ht _ _ _ h h')
  | func f h ih =>
    cases h' with
    | func _ h' => exact .func f (fun i => ih i (h' i))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The key renaming fact is that $\FirstOrderNameCorrespondence{R}{\varphi}{\psi}$ implies
    $\FirstOrderNameCorrespondence{S}{\varphi\subst{x}{z}}{\psi}$ whenever, for corresponding free names $a,b$,
    $$\begin{aligned}
    R(a,b)\land a=x&\ \Longrightarrow\ S(z,b),\\
    R(a,b)\land a\ne x&\ \Longrightarrow\ S(a,b).
    \end{aligned}$$
    Prove this by strong induction on the number of formula constructors, allowing both relations to vary.
    Terms follow by structural induction; atomic formulas and binary connectives follow componentwise.
    At a binder for $x$, substitution stops and the binder correspondence masks that name.
    At any other binder different from $z$, apply the induction hypothesis to the body.
    If the binder is $z$, the substitution rule first renames it to a fresh name.
    Apply the induction hypothesis to this renaming and then to the remaining substitution.
    Both calls concern bodies of the original body's size. Freshness ensures that only the intended correspondence changes.
    The same assertion holds on the right by symmetry.
-/
theorem rename_left {R S : ℕ → ℕ → Prop} {t r : L.Term ℕ} (h : TermRel R t r)
    (x z : ℕ)
    (hs : ∀ a ∈ t.varFinset, ∀ b ∈ r.varFinset, R a b → S (if a = x then z else a) b) :
    TermRel S (termSubst t x (.var z)) r := by
  induction h with
  | @var a b hab =>
    have hh := hs a (by simp) b (by simp) hab
    by_cases ha : a = x
    · simpa only [termSubst, Term.subst, ite_eq_left ha] using TermRel.var
        (by simpa only [ite_eq_left ha] using hh)
    · simpa only [termSubst, Term.subst, ite_eq_right ha] using TermRel.var
        (by simpa only [ite_eq_right ha] using hh)
  | @func n f ts us h ih =>
    apply TermRel.func f
    intro i
    apply ih i
    intro a ha b hb hab
    exact hs a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
      b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩) hab

theorem subst {R S : ℕ → ℕ → Prop} {t r a b : L.Term ℕ}
    (h : TermRel R t r) (x y : ℕ) (hab : TermRel S a b)
    (hkeys : ∀ v w, R v w → (v = x ↔ w = y))
    (hkeep : ∀ v w, R v w → v ≠ x → S v w) :
    TermRel S (termSubst t x a) (termSubst r y b) := by
  induction h with
  | @var v w hvw =>
    by_cases hv : v = x
    · simpa only [termSubst, Term.subst, ite_eq_left hv, ite_eq_left ((hkeys v w hvw).mp hv)]
        using hab
    · have hw : w ≠ y := fun he => hv ((hkeys v w hvw).mpr he)
      simpa only [termSubst, Term.subst, ite_eq_right hv, ite_eq_right hw] using
        TermRel.var (hkeep v w hvw hv)
  | func f h ih => exact .func f ih

end TermRel
end PolishSpaceBook.NamedFirstOrder
