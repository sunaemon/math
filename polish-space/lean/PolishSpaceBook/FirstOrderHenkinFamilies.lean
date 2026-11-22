module

public import PolishSpaceBook.FirstOrderHenkinWitness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Adjoining a family of fresh Henkin witnesses

One selected constant is moved to a further fresh slot, leaving the old language
and all other witness axioms unchanged. This applies the single-witness lemma
inductively inside a fixed ambient language. Finite proof support then handles
an arbitrary set of witness axioms from one language stage.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w
variable {L : Language.{u,v}} {A : Type w}
local instance : DecidableEq A := Classical.decEq _

/-- Move just the selected constant to a fresh outer slot. -/
def singleOutConstant (a : A) : L[[A]] →ᴸ L[[A]][[Unit]] := by
  classical
  exact {
  onFunction {n} f := match n with
    | 0 => match f with
      | .inl g => .inl (.inl g)
      | .inr b => if b = a then .inr () else .inl (.inr b)
    | _ + 1 => .inl f
  onRelation {_} R := Sum.inl R }

theorem singleOutConstant_comp (a : A) :
    (singleOutConstant (L := L) a).comp (L.lhomWithConstants A) =
      (L[[A]].lhomWithConstants Unit).comp (L.lhomWithConstants A) := by
  apply LHom.funext
  · funext n f
    cases n <;> rfl
  · rfl

theorem mapLanguage_singleOut_old (a : A) (φ : AlphaFormula L) :
    (φ.mapLanguage (L.lhomWithConstants A)).mapLanguage (singleOutConstant a) =
      (φ.mapLanguage (L.lhomWithConstants A)).mapLanguage (L[[A]].lhomWithConstants Unit) := by
  simp only [mapLanguage_comp, singleOutConstant_comp]

theorem singleOutConstant_selected (a : A) :
    (singleOutConstant (L := L) a).onTerm ((L.con a).term : L[[A]].Term ℕ) = (L[[A]].con ()).term := by
  simp [Constants.term, Language.con, LHom.onTerm, singleOutConstant]
  exact Subsingleton.elim _ _

theorem singleOutConstant_other (a b : A) (hba : b ≠ a) :
    (singleOutConstant (L := L) a).onTerm ((L.con b).term : L[[A]].Term ℕ) =
      (L[[A]].lhomWithConstants Unit).onTerm (L.con b).term := by
  simp [Constants.term, Language.con, LHom.onTerm, singleOutConstant, lhomWithConstants, LHom.sumInl]
  exact ⟨hba, Subsingleton.elim _ _⟩

theorem mapLanguage_henkin_selected (a : A) (x : ℕ) (φ : AlphaFormula L) :
    (henkinAxiom a x φ).mapLanguage (singleOutConstant a) =
      henkinAxiom () x (φ.mapLanguage (L.lhomWithConstants A)) := by
  simp only [henkinAxiom, mapLanguage_binary, mapLanguage_quant, mapLanguage_subst,
    mapLanguage_singleOut_old, singleOutConstant_selected]

theorem mapLanguage_henkin_other (a b : A) (hba : b ≠ a) (x : ℕ) (φ : AlphaFormula L) :
    (henkinAxiom b x φ).mapLanguage (singleOutConstant a) =
      (henkinAxiom b x φ).mapLanguage (L[[A]].lhomWithConstants Unit) := by
  simp only [henkinAxiom, mapLanguage_binary, mapLanguage_quant, mapLanguage_subst,
    mapLanguage_singleOut_old, singleOutConstant_other a b hba]

/-- The old axioms and the witness axioms whose labels belong to the chosen set. -/
def henkinTheory (T : Set (AlphaFormula L)) (x : A → ℕ) (φ : A → AlphaFormula L) (S : Set A) :
    Set (AlphaFormula L[[A]]) :=
  AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T ∪ (fun a => henkinAxiom a (x a) (φ a)) '' S

theorem henkinTheory_insert (T : Set (AlphaFormula L)) (x : A → ℕ) (φ : A → AlphaFormula L)
    (a : A) (S : Set A) :
    henkinTheory T x φ (insert a S) = insert (henkinAxiom a (x a) (φ a)) (henkinTheory T x φ S) := by
  simp only [henkinTheory, Set.image_insert_eq, Set.union_insert]

theorem henkinTheory_mono (T : Set (AlphaFormula L)) (x : A → ℕ) (φ : A → AlphaFormula L)
    {S U : Set A} (h : S ⊆ U) : henkinTheory T x φ S ⊆ henkinTheory T x φ U :=
  Set.union_subset_union_right _ (Set.image_mono h)

theorem henkinTheory_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (x : A → ℕ) (φ : A → AlphaFormula L) (hφ : ∀ a, (φ a).fv ⊆ {x a}) (S : Set A) :
    henkinTheory T x φ S ⊆ Sentences L[[A]] := by
  intro ψ hψ
  rcases hψ with ⟨θ, hθ, rfl⟩ | ⟨a, _, rfl⟩
  · simpa [Sentences] using hT hθ
  · exact henkinAxiom_sentence a (x a) (φ a) (hφ a)

theorem mapLanguage_singleOut_prior {T : Set (AlphaFormula L)} {x : A → ℕ} {φ : A → AlphaFormula L}
    {S : Set A} (a : A) (ha : a ∉ S) {ψ : AlphaFormula L[[A]]} (hψ : ψ ∈ henkinTheory T x φ S) :
    ψ.mapLanguage (singleOutConstant a) = ψ.mapLanguage (L[[A]].lhomWithConstants Unit) := by
  rcases hψ with ⟨θ, _, rfl⟩ | ⟨b, hb, rfl⟩
  · exact mapLanguage_singleOut_old a θ
  · exact mapLanguage_henkin_other a b (fun h => ha (h ▸ hb)) (x b) (φ b)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Work in the fixed language $K$, which contains all the new constants from the start.
    For a finite set $F\IncludedIn I$, put $T_F:=T\cup\{H_b:b\in F\}$.
    We prove its consistency by induction on the size of $F$. For the empty set, use the
    \termuse{constant extension lemma}.
    
    Suppose $T_F$ is consistent and $a\in\SetDifference{I}{F}$. Adjoin a further new constant $d$ to $K$.
    The \termuse{single Henkin witness lemma} makes the following theory consistent:
    $$T_F\cup\{(\existsbind{x_a}{\psi_a})\to\psi_a\subst{x_a}{d}\}.$$
    Map symbols from $K$ into this further language by sending $c_a$ to $d$ and keeping every other symbol fixed.
    The rule-by-rule proof of the \termuse{language inclusion lemma} applies to this map as well:
    arities and variable names are unchanged, and the map commutes with substitution.
    It fixes every axiom of $T_F$, since each witness formula belongs to the old language and each witness
    axiom uses only its own new constant. It sends $H_a$ to the newly adjoined axiom.
    Thus a derivation of falsity from $T_{F\cup\{a\}}$ would give one from the displayed consistent theory,
    a contradiction. This completes the induction.
-/
theorem Consistent.adjoin_henkinFinset {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (x : A → ℕ) (φ : A → AlphaFormula L)
    (hφ : ∀ a, (φ a).fv ⊆ {x a}) (S : Finset A) : Consistent (henkinTheory T x φ S) := by
  induction S using Finset.induction_on with
  | empty => simpa [henkinTheory] using hT.withConstants (A := A)
  | @insert a S ha ih =>
    rw [Finset.coe_insert, henkinTheory_insert]
    intro hbad
    have hc := ih.adjoin_henkinAxiom (henkinTheory_sentences hclosed x φ hφ S) () (x a)
      ((φ a).mapLanguage (L.lhomWithConstants A)) (by simpa using hφ a)
    apply hc
    have hm := hbad.mapLanguage (singleOutConstant a)
    apply ProvesFrom.mono (by simpa only [mapLanguage_falsum] using hm)
    rintro ψ ⟨θ, hθ, heq⟩
    rw [← heq]
    rcases hθ with rfl | hθ
    · exact Or.inl (mapLanguage_henkin_selected a (x a) (φ a))
    · exact Set.mem_insert_of_mem _ ⟨θ, hθ, (mapLanguage_singleOut_prior a ha hθ).symm⟩

/-- The finitely many assumptions in a derivation use finitely many witness labels. -/
theorem henkinTheory_finite_support (T : Set (AlphaFormula L)) (x : A → ℕ) (φ : A → AlphaFormula L)
    (S : Set A) (Γ : Context L[[A]]) (hΓ : ∀ ψ ∈ Γ, ψ ∈ henkinTheory T x φ S) :
    ∃ F : Finset A, ∀ ψ ∈ Γ, ψ ∈ henkinTheory T x φ F := by
  classical
  induction Γ using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert ψ Γ hψ ih =>
    obtain ⟨F, hF⟩ := ih (fun θ hθ => hΓ θ (Finset.mem_insert_of_mem hθ))
    rcases hΓ ψ (Finset.mem_insert_self _ _) with hold | ⟨a, _, rfl⟩
    · refine ⟨F, ?_⟩
      intro θ hθ
      rcases Finset.mem_insert.mp hθ with rfl | hθ
      · exact Or.inl hold
      · exact hF θ hθ
    · refine ⟨insert a F, ?_⟩
      intro θ hθ
      rcases Finset.mem_insert.mp hθ with rfl | hθ
      · exact Or.inr ⟨a, Finset.mem_insert_self _ _, rfl⟩
      · exact henkinTheory_mono T x φ (by intro b hb; exact Finset.mem_insert_of_mem hb) (hF θ hθ)

/-- All fresh witnesses from a fixed language stage may be adjoined at once. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: A family of Henkin witnesses
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    A derivation from the whole family uses only finitely many axioms, hence only finitely many witness labels.
    It is therefore already a derivation from some $T_F$ in the same language $K$.
    The consistency just proved rules out a derivation of falsity.
    \end{proof}
-/
theorem Consistent.adjoin_henkinFamily {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (x : A → ℕ) (φ : A → AlphaFormula L)
    (hφ : ∀ a, (φ a).fv ⊆ {x a}) (S : Set A) : Consistent (henkinTheory T x φ S) := by
  rintro ⟨Γ, hΓ, hd⟩
  obtain ⟨F, hF⟩ := henkinTheory_finite_support T x φ S Γ hΓ
  exact hT.adjoin_henkinFinset hclosed x φ hφ F ⟨Γ, hF, hd⟩

end PolishSpaceBook.NamedFirstOrder
