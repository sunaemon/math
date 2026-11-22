module

public import PolishSpaceBook.SetTheoryMostowski
public import PolishSpaceBook.SetTheoryModelClosure
public import PolishSpaceBook.FirstOrderLowenheimSkolem

@[expose] public section

/-! # Countable transitive models and fixed parameters

Apply the book's Skolem-stage construction, then its explicit Mostowski collapse.
A transitive seed is fixed pointwise by membership induction; mere inclusion of a
parameter in the elementary substructure does not suffice to fix that parameter.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

local instance membershipSymbols_countable : Countable membershipLanguage.Symbols := by
  unfold Language.Symbols
  infer_instance

/-- Membership on an elementary substructure inherits ambient well-foundedness. -/
def submodelMembership {V : ZFSet.{u}} (N : membershipLanguage.ElementarySubstructure V)
    (a b : N) : Prop := a.val.val ∈ b.val.val

lemma submodelMembership_wf {V : ZFSet.{u}} (N : membershipLanguage.ElementarySubstructure V) :
    WellFounded (submodelMembership N) :=
  InvImage.wf (fun a : N => a.val.val) ZFSet.mem_wf

lemma submodelMembership_extensional {V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : membershipLanguage.ElementarySubstructure V) :
    Function.Injective (fun a => {b | submodelMembership N b a}) := by
  have hN : N ⊨ extensionalitySentence := (N.realize_sentence _).mpr (models_extensionality hV)
  intro a b hab
  apply (AbstractMembership.models_extensionality_iff N).mp hN a b
  intro z
  exact Set.ext_iff.mp hab z

/-- The relational collapse is an isomorphism of the actual membership-language structures. -/
def submodelCollapseEquiv {V : ZFSet.{u}} (hV : V.IsTransitive)
    (N : membershipLanguage.ElementarySubstructure V) :
    N ≃[membershipLanguage] mostowskiImage (submodelMembership N) (submodelMembership_wf N) where
  toEquiv := (mostowskiIso (submodelMembership N) (submodelMembership_wf N)
    (submodelMembership_extensional hV N)).toEquiv
  map_fun' := by intro n f; exact Empty.elim f
  map_rel' := by
    intro n r xs
    cases r
    exact (mostowskiIso (submodelMembership N) (submodelMembership_wf N)
      (submodelMembership_extensional hV N)).map_rel_iff

/-- If all members of a transitive seed are in N, its collapse fixes them individually. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    For $a\in T$, membership induction proves $\pi(a)=a$. Transitivity of $T$ ensures that every $b\in a$
    belongs to $T$ and hence to $N$. The induction hypothesis therefore gives
    $$\pi(a)=\{\pi(b):b\in a\cap N\}=\{b:b\in a\}=a.$$
    Thus every $a\in T$ belongs to $M$, as required.
    \end{proof}
-/
theorem submodelCollapse_fixes_transitive {V T : ZFSet.{u}}
    (N : membershipLanguage.ElementarySubstructure V) (hT : T.IsTransitive)
    (hTN : ∀ x ∈ T, ∃ a : N, a.val.val = x) :
    ∀ a : N, a.val.val ∈ T →
      mostowskiCollapse (submodelMembership N) (submodelMembership_wf N) a = a.val.val := by
  have h : ∀ x : ZFSet.{u}, x ∈ T → ∀ a : N, a.val.val = x →
      mostowskiCollapse (submodelMembership N) (submodelMembership_wf N) a = x := by
    intro x
    induction x using ZFSet.inductionOn with
    | h x ih =>
      intro hx a ha
      apply ZFSet.ext
      intro z
      rw [mem_mostowskiCollapse]
      constructor
      · rintro ⟨b, hb, he⟩
        have hbx : b.val.val ∈ x := ha ▸ hb
        have hfix := ih b.val.val hbx (hT.mem_trans hbx hx) b rfl
        exact (hfix.symm.trans he) ▸ hbx
      · intro hz
        obtain ⟨b, hb⟩ := hTN z (hT.mem_trans hz hx)
        exact ⟨b, by change b.val.val ∈ a.val.val; rwa [hb, ha], ih z hz (hT.mem_trans hz hx) b hb⟩
  intro a ha
  exact h a.val.val ha a rfl

/-- A countable transitive seed survives the countable elementary-submodel collapse unchanged. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Countable transitive reduction
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    By downward Löwenheim--Skolem from §{sec:appendix-logic}, choose a countable elementary submodel
    $N\prec M_0$ containing every element of $T$. Its membership relation is well-founded by ambient
    Foundation. Transitivity makes $M_0$ satisfy Extensionality, so elementarity makes $(N,\in)$ extensional.
    The Mostowski collapse gives an isomorphism $\pi:N\to M$ onto a transitive set $M$.
    Surjectivity makes $M$ countable. Isomorphisms preserve satisfaction, and $N\prec M_0$, so $M$ and $M_0$
    satisfy exactly the same sentences.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is the theorem behind the common forcing convention "work in a sufficiently large finite fragment of ZFC."
    Reflection supplies transitive sets $V_\alpha$ satisfying any prescribed finite fragment; compactness, downward
    Löwenheim--Skolem, and Mostowski collapse then explain the countable-transitive-model reduction used in
    §{sec:internal-model-closure}.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The countable-transitive convention is reached by starting from the reflected transitive set $V_\alpha$, then applying
    downward Löwenheim--Skolem from §{sec:appendix-logic} and the Mostowski collapse below. Parameters are handled with
    care: the collapse preserves actual parameters only when enough of their transitive closures is included in the
    elementary submodel; in general it carries them to their collapsed images.
-/
theorem exists_countable_transitive_model {V T : ZFSet.{u}} [Nonempty V] [Countable T]
    (hV : V.IsTransitive) (hT : T.IsTransitive) (hTV : T ⊆ V) :
    ∃ M : ZFSet.{u}, M.IsTransitive ∧ Countable M ∧ T ⊆ M ∧
      ∀ φ : membershipLanguage.Sentence, M ⊨ φ ↔ V ⊨ φ := by
  classical
  let X : Set V := {a | a.val ∈ T}
  have hX : X.Countable := by
    let f : X → T := fun a => ⟨a.val.val, a.property⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : T => z.val) hab
    let : Countable X := Function.Injective.countable hf
    exact Set.to_countable X
  obtain ⟨N, hXN, hN⟩ := NamedFirstOrder.exists_countable_elementarySubstructure (L := membershipLanguage) hX
  let : Countable N := hN.to_subtype
  let M := mostowskiImage (submodelMembership N) (submodelMembership_wf N)
  let e := submodelCollapseEquiv hV N
  have hcount : Countable M := Function.Injective.countable e.symm.injective
  have hTN : ∀ x ∈ T, ∃ a : N, a.val.val = x := by
    intro x hx
    exact ⟨⟨⟨x, hTV hx⟩, hXN hx⟩, rfl⟩
  refine ⟨M, mostowskiImage_transitive _ _, hcount, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha⟩ := hTN x hx
    have he := submodelCollapse_fixes_transitive N hT hTN a (ha ▸ hx)
    exact (he.trans ha) ▸ ZFSet.mem_range_self a
  · intro φ
    exact (StrongHomClass.realize_sentence e φ).symm.trans (N.realize_sentence φ)

end PolishSpaceBook.SetTheoryModels
