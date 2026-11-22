module

public import PolishSpaceBook.FirstOrderTermCorrespondence

@[expose] public section

/-!
# Comparing named first-order formulas

The comparison follows the same constructors and records corresponding bound
names. Equality correspondence is characterized by the book's finite sequences
of fresh binder renamings, not by semantic equivalence.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v
variable {L : Language.{u,v}}
namespace Formula

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
inductive NameRel : (ℕ → ℕ → Prop) → Formula L → Formula L → Prop where
  | falsum (R : ℕ → ℕ → Prop) : NameRel R .falsum .falsum
  | equal {R : ℕ → ℕ → Prop} {t t' r r' : L.Term ℕ} :
      TermRel R t t' → TermRel R r r' → NameRel R (.equal t r) (.equal t' r')
  | rel {R : ℕ → ℕ → Prop} {n : ℕ} (r : L.Relations n) {ts us : Fin n → L.Term ℕ} :
      (∀ i, TermRel R (ts i) (us i)) → NameRel R (.rel r ts) (.rel r us)
  | binary (c : Connective) {R : ℕ → ℕ → Prop} {φ φ' ψ ψ' : Formula L} :
      NameRel R φ φ' → NameRel R ψ ψ' → NameRel R (.binary c φ ψ) (.binary c φ' ψ')
  | quant (q : Quantifier) {R : ℕ → ℕ → Prop} {x y : ℕ} {φ ψ : Formula L} :
      NameRel (bindNames R x y) φ ψ → NameRel R (.quant q x φ) (.quant q y ψ)

namespace NameRel

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Structural induction shows that a comparison depends only on the relation on the two free-variable sets,
-/
theorem congr {R : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ)
    {S : ℕ → ℕ → Prop}
    (hs : ∀ a ∈ φ.fv, ∀ b ∈ ψ.fv, R a b → S a b) : NameRel S φ ψ := by
  induction h generalizing S with
  | falsum => exact .falsum _
  | equal ht hr =>
    apply NameRel.equal
    · apply ht.congr
      intro a ha b hb hab
      exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
    · apply hr.congr
      intro a ha b hb hab
      exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
  | rel r ht =>
    apply NameRel.rel r
    intro i
    apply (ht i).congr
    intro a ha b hb hab
    exact hs a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
      b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩) hab
  | binary c hφ hψ ihφ ihψ =>
    apply NameRel.binary c
    · apply ihφ; intro a ha b hb hab
      exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
    · apply ihψ; intro a ha b hb hab
      exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
  | @quant q R x y φ ψ h ih =>
    apply NameRel.quant q
    apply ih
    intro a ha b hb hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hax, hby, hs a (Finset.mem_erase.mpr ⟨hax, ha⟩)
        b (Finset.mem_erase.mpr ⟨hby, hb⟩) hab⟩

theorem mono {R S : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ)
    (hs : ∀ a b, R a b → S a b) : NameRel S φ ψ :=
  h.congr (fun a _ b _ => hs a b)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Comparison with equality is reflexive and symmetric.
-/
theorem refl (φ : Formula L) : NameRel Eq φ φ := by
  induction φ with
  | falsum => exact .falsum _
  | equal t r => exact .equal (.refl t) (.refl r)
  | rel r ts => exact .rel r (fun i => .refl (ts i))
  | binary c φ ψ ihφ ihψ => exact .binary c ihφ ihψ
  | quant q x φ ih =>
    apply NameRel.quant q
    apply ih.mono
    intro a b hab
    subst b
    by_cases ha : a = x
    · exact Or.inl ⟨ha, ha⟩
    · exact Or.inr ⟨ha, ha, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Comparison with equality is reflexive and symmetric.
-/
theorem symm {R : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ) :
    NameRel (fun b a => R a b) ψ φ := by
  induction h with
  | falsum => exact .falsum _
  | equal ht hr => exact .equal ht.symm hr.symm
  | rel r ht => exact .rel r (fun i => (ht i).symm)
  | binary c hφ hψ ihφ ihψ => exact .binary c ihφ ihψ
  | @quant q R x y φ ψ h ih =>
    apply NameRel.quant q
    apply ih.mono
    intro b a hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha, hab⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    and that each free name on either side has a corresponding free name on the other.
-/
theorem fv_left {R : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ)
    {a : ℕ} (ha : a ∈ φ.fv) : ∃ b ∈ ψ.fv, R a b := by
  induction h with
  | falsum => simp [fv] at ha
  | equal ht hr =>
    rcases Finset.mem_union.mp ha with ht' | hr'
    · obtain ⟨b, hb, hab⟩ := ht.fv_left ht'
      exact ⟨b, Finset.mem_union_left _ hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := hr.fv_left hr'
      exact ⟨b, Finset.mem_union_right _ hb, hab⟩
  | rel r ht =>
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, hab⟩ := (ht i).fv_left hi
    exact ⟨b, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩, hab⟩
  | binary c hφ hψ ihφ ihψ =>
    rcases Finset.mem_union.mp ha with hm | hp
    · obtain ⟨b, hb, hab⟩ := ihφ hm
      exact ⟨b, Finset.mem_union_left _ hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := ihψ hp
      exact ⟨b, Finset.mem_union_right _ hb, hab⟩
  | @quant q R x y φ ψ h ih =>
    obtain ⟨hax, ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨b, hb, hab⟩ := ih ha
    rcases hab with ⟨he, _⟩ | ⟨_, hby, hab⟩
    · exact (hax he).elim
    · exact ⟨b, Finset.mem_erase.mpr ⟨hby, hb⟩, hab⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Comparisons compose by induction on constructors:
    under two quantifiers, the intermediate name is either bound in both comparisons or free in both.
    In particular, comparison with equality is transitive.
-/
theorem trans {R : ℕ → ℕ → Prop} {φ ψ : Formula L} (h : NameRel R φ ψ)
    {S T : ℕ → ℕ → Prop} {χ : Formula L} (h' : NameRel S ψ χ)
    (ht : ∀ a b c, R a b → S b c → T a c) : NameRel T φ χ := by
  induction h generalizing S T χ with
  | falsum => cases h'; exact .falsum _
  | equal ht₁ ht₂ => cases h' with | equal hu₁ hu₂ =>
      exact .equal (ht₁.trans hu₁ ht) (ht₂.trans hu₂ ht)
  | rel r hts => cases h' with | rel _ hus =>
      exact .rel r (fun i => (hts i).trans (hus i) ht)
  | binary c hφ hψ ihφ ihψ =>
    cases h' with | binary _ hχ hθ => exact .binary c (ihφ hχ ht) (ihψ hθ ht)
  | @quant q R x y φ ψ h ih =>
    cases h' with
    | @quant _ _ _ z _ χ hp =>
      apply NameRel.quant q
      apply ih hp
      intro a b c hab hbc
      rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
      · rcases hbc with ⟨_, rfl⟩ | ⟨hby, _⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact (hby rfl).elim
      · rcases hbc with ⟨he, _⟩ | ⟨_, hcz, hbc⟩
        · exact (hby he).elim
        · exact Or.inr ⟨hax, hcz, ht a b c hab hbc⟩

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
theorem rename_left {R S : ℕ → ℕ → Prop} {M N : Formula L} (h : NameRel R M N)
    (x z : ℕ)
    (hs : ∀ a ∈ M.fv, ∀ b ∈ N.fv, R a b → S (if a = x then z else a) b) :
    NameRel S (M.subst x (.var z)) N := by
  have bounded : ∀ k (M N : Formula L) (R S : ℕ → ℕ → Prop) x z,
      M.nodes ≤ k → NameRel R M N →
      (∀ a ∈ M.fv, ∀ b ∈ N.fv, R a b → S (if a = x then z else a) b) →
      NameRel S (M.subst x (.var z)) N := by
    intro k
    induction k with
    | zero => intro M N R S x z hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N R S x z hk h hs
      cases h with
      | falsum => exact .falsum _
      | equal ht hr =>
        rw [subst_equal]
        apply NameRel.equal
        · apply ht.rename_left x z
          intro a ha b hb hab
          exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
        · apply hr.rename_left x z
          intro a ha b hb hab
          exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
      | rel r ht =>
        rw [subst_rel]
        apply NameRel.rel r
        intro i
        apply (ht i).rename_left x z
        intro a ha b hb hab
        exact hs a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
          b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩) hab
      | @binary c R A B C D hA hC =>
        have ha : A.nodes ≤ k := by simp only [nodes] at hk; omega
        have hc : C.nodes ≤ k := by simp only [nodes] at hk; omega
        rw [subst_binary]
        apply NameRel.binary c
        · apply ih A B R S x z ha hA
          intro a ha b hb hab
          exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
        · apply ih C D R S x z hc hC
          intro a ha b hb hab
          exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
      | @quant q R u v A B hab =>
        have hm : A.nodes ≤ k := by simp only [nodes] at hk; omega
        rw [subst_quant]
        by_cases hux : u = x
        · rw [ite_eq_left hux]
          apply NameRel.quant q
          apply hab.congr
          intro a ha b hb hr
          rcases hr with ⟨rfl, rfl⟩ | ⟨hau, hbv, hr⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · have hax : a ≠ x := by simpa only [← hux] using hau
            exact Or.inr ⟨hau, hbv, by
              simpa only [ite_eq_right hax] using hs a (Finset.mem_erase.mpr ⟨hau, ha⟩)
                b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hr⟩
        · rw [ite_eq_right hux]
          by_cases huz : u ≠ z
          · rw [ite_eq_left (by simpa only [Term.varFinset, Finset.mem_singleton] using huz)]
            apply NameRel.quant q
            apply ih A B (bindNames R u v) (bindNames S u v) x z hm hab
            intro a ha b hb hr
            rcases hr with ⟨rfl, rfl⟩ | ⟨hau, hbv, hr⟩
            · simp only [ite_eq_right hux]; exact Or.inl ⟨rfl, rfl⟩
            · have hsab := hs a (Finset.mem_erase.mpr ⟨hau, ha⟩)
                b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hr
              refine Or.inr ⟨?_, hbv, hsab⟩
              split_ifs with hax
              · exact huz.symm
              · exact hau
          · have huz : u = z := not_ne_iff.mp huz
            subst u
            rw [ite_eq_right (by simp [Term.varFinset])]
            let w := NamedLambda.Term.fresh (A.fv ∪ (Term.var z : L.Term ℕ).varFinset ∪ {x})
            have hw : w ∉ A.fv ∧ w ≠ z ∧ w ≠ x := by
              simpa only [w, Term.varFinset, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
                using NamedLambda.Term.fresh_not_mem (A.fv ∪ (Term.var z : L.Term ℕ).varFinset ∪ {x})
            change NameRel S (.quant q w ((A.subst z (.var w)).subst x (.var z))) (.quant q v B)
            apply NameRel.quant q
            have hr : NameRel (bindNames R w v) (A.subst z (.var w)) B := by
              apply ih A B (bindNames R z v) (bindNames R w v) z w hm hab
              intro a ha b hb hr
              rcases hr with ⟨rfl, rfl⟩ | ⟨haz, hbv, hr⟩
              · simp only [ite_true]; exact Or.inl ⟨rfl, rfl⟩
              · rw [ite_eq_right haz]
                have haw : a ≠ w := by intro he; subst a; exact hw.1 ha
                exact Or.inr ⟨haw, hbv, hr⟩
            apply ih (A.subst z (.var w)) B (bindNames R w v) (bindNames S w v) x z
              (by simpa only [nodes_subst] using hm) hr
            intro a ha b hb hr
            rcases hr with ⟨rfl, rfl⟩ | ⟨haw, hbv, hr⟩
            · simp only [ite_eq_right hw.2.2]; exact Or.inl ⟨rfl, rfl⟩
            · have ha' : a ∈ A.fv ∧ a ≠ z := by
                rcases (mem_fv_subst A z (.var w) a).mp ha with h | ⟨_, h⟩
                · exact h
                · exact (haw (by simpa only [Term.varFinset, Finset.mem_singleton] using h)).elim
              have hsab := hs a (Finset.mem_erase.mpr ⟨ha'.2, ha'.1⟩)
                b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hr
              refine Or.inr ⟨?_, hbv, hsab⟩
              split_ifs with hax
              · exact hw.2.1.symm
              · exact haw
  exact bounded M.nodes M N R S x z le_rfl h hs

theorem rebind_left {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Formula L}
    (h : NameRel (bindNames R x y) M N) (z : ℕ) (hz : z ∉ M.fv) :
    NameRel (bindNames R z y) (M.subst x (.var z)) N := by
  apply h.rename_left x z
  intro a ha b hb hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
  · simp only [ite_true]; exact Or.inl ⟨rfl, rfl⟩
  · rw [ite_eq_right hax]
    have haz : a ≠ z := by intro he; subst a; exact hz ha
    exact Or.inr ⟨haz, hby, hab⟩

theorem rebind_right {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Formula L}
    (h : NameRel (bindNames R x y) M N) (z : ℕ) (hz : z ∉ N.fv) :
    NameRel (bindNames R x z) M (N.subst y (.var z)) := by
  have h' : NameRel (bindNames (fun b a => R a b) y x) N M := by
    apply h.symm.mono
    intro b a hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha, hab⟩
  apply (h'.rebind_left z hz).symm.mono
  intro a b hab
  rcases hab with ⟨hb, ha⟩ | ⟨hb, ha, hab⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb, hab⟩

theorem eq_symm {M N : Formula L} (h : NameRel Eq M N) : NameRel Eq N M :=
  h.symm.mono (fun _ _ h => h.symm)

theorem eq_trans {M N P : Formula L} (h : NameRel Eq M N) (h' : NameRel Eq N P) :
    NameRel Eq M P := h.trans h' (fun _ _ _ h₁ h₂ => h₁.trans h₂)

theorem eq_quant {M N : Formula L} (h : NameRel Eq M N) (q : Quantifier) (x : ℕ) :
    NameRel Eq (.quant q x M) (.quant q x N) := by
  apply NameRel.quant q
  apply h.mono
  intro a b hab
  subst b
  by_cases ha : a = x
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨ha, ha, rfl⟩

theorem eq_rename (q : Quantifier) (M : Formula L) (x z : ℕ) (hz : z ∉ M.fv) :
    NameRel Eq (.quant q x M) (.quant q z (M.subst x (.var z))) := by
  apply NameRel.eq_symm
  apply NameRel.quant q
  apply (NameRel.refl M).rename_left x z
  intro a ha b hb hab
  subst b
  by_cases hax : a = x
  · rw [ite_eq_left hax]; exact Or.inl ⟨rfl, hax⟩
  · rw [ite_eq_right hax]
    have haz : a ≠ z := by intro he; subst a; exact hz ha
    exact Or.inr ⟨haz, hax, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Comparison of named formulas
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    It follows that renaming a binder and updating its recorded name preserve comparison.
    Every generating $\alpha$-renaming therefore preserves comparison with equality, and the equivalence and
    congruence rules preserve it as well. Conversely, induct on the number of formula constructors.
    Atomic formulas that compare with equality are identical, and binary connectives reduce to their components.
    For quantifiers, rename both binders to one name fresh for both bodies.
    The renaming fact makes the two renamed bodies compare with equality, so induction gives their $\alpha$-equivalence.
    Restore the common quantifier and undo the two renamings to obtain the original formulas' $\alpha$-equivalence.
-/
theorem eq_alpha {M N : Formula L} (h : NameRel Eq M N) : Alpha M N := by
  have bounded : ∀ k (M N : Formula L), M.nodes ≤ k → NameRel Eq M N → Alpha M N := by
    intro k
    induction k with
    | zero => intro M N hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N hk h
      cases h with
      | falsum => exact .refl _
      | equal ht hr => rw [ht.eq_eq, hr.eq_eq]; exact .refl _
      | @rel _ _ r ts us ht =>
        have he : ts = us := funext (fun i => (ht i).eq_eq)
        subst us
        exact .refl _
      | @binary c _ A B C D hab hcd =>
        apply Alpha.binary c
        · apply ih A B (by simp only [nodes] at hk; omega) hab
        · apply ih C D (by simp only [nodes] at hk; omega) hcd
      | @quant q _ x y A B hab =>
        let z := NamedLambda.Term.fresh (A.fv ∪ B.fv)
        have hz : z ∉ A.fv ∧ z ∉ B.fv := by
          simpa only [z, Finset.mem_union, not_or] using NamedLambda.Term.fresh_not_mem (A.fv ∪ B.fv)
        have hbody : NameRel Eq (A.subst x (.var z)) (B.subst y (.var z)) := by
          apply ((hab.rebind_left z hz.1).rebind_right z hz.2).mono
          intro a b hr
          rcases hr with ⟨rfl, rfl⟩ | ⟨_, _, hr⟩
          · rfl
          · exact hr
        have hm : (A.subst x (.var z)).nodes ≤ k := by
          rw [nodes_subst]; simp only [nodes] at hk; omega
        exact (Alpha.rename q A x z hz.1).trans
          ((Alpha.quant q z (ih _ _ hm hbody)).trans (Alpha.rename q B y z hz.2).symm)
  exact bounded M.nodes M N le_rfl h

end NameRel

theorem Alpha.nameRel {M N : Formula L} (h : Alpha M N) : NameRel Eq M N := by
  induction h with
  | refl M => exact NameRel.refl M
  | symm _ ih => exact ih.eq_symm
  | trans _ _ ih₁ ih₂ => exact ih₁.eq_trans ih₂
  | binary c _ _ ih₁ ih₂ => exact .binary c ih₁ ih₂
  | quant q x _ ih => exact ih.eq_quant q x
  | rename q M x z hz => exact NameRel.eq_rename q M x z hz

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Comparison of named formulas
-/
theorem alpha_iff_nameRel (M N : Formula L) : Alpha M N ↔ NameRel Eq M N :=
  ⟨Alpha.nameRel, NameRel.eq_alpha⟩

end Formula
end PolishSpaceBook.NamedFirstOrder
