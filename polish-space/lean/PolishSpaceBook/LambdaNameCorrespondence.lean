module

public import PolishSpaceBook.LambdaNamedAlpha

@[expose] public section

/-! # Comparing named terms under corresponding variable names

This judgment relates the original named terms directly. Under two abstractions,
the bound names correspond to each other and shadow any previous correspondence.
No second term syntax or unnamed representation is used.
-/
namespace PolishSpaceBook.NamedLambda.Term

/-- Extend a correspondence by a pair of bound names, masking both names. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compare named terms, keep a relation $R$ between the variable names on the two sides. Upon entering abstractions with
    binders $x,y$, replace it by the relation
    $$\begin{aligned}
    \LambdaBoundNames{R}{x}{y}(a,b)
    &\Longleftrightarrow (a=x\ \land\ b=y)\\
    &\qquad\lor\bigl(a\ne x\ \land\ b\ne y\ \land\ R(a,b)\bigr).
    \end{aligned}$$
    The two bound names now correspond to each other; their previous correspondences are hidden by these binders.
-/
def bindNames (R : ℕ → ℕ → Prop) (x y a b : ℕ) : Prop :=
  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ R a b)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $\LambdaNameCorrespondence{R}{M}{N}$ for the comparison defined recursively on the original named terms by
    $$\begin{aligned}
    \LambdaNameCorrespondence{R}{a}{b}&\Longleftrightarrow R(a,b),\\
    \LambdaNameCorrespondence{R}{MP}{NQ}&\Longleftrightarrow
     \LambdaNameCorrespondence{R}{M}{N}\ \land\ \LambdaNameCorrespondence{R}{P}{Q},\\
    \LambdaNameCorrespondence{R}{\lambdaab{x}{M}}{\lambdaab{y}{N}}
     &\Longleftrightarrow\LambdaNameCorrespondence{\LambdaBoundNames{R}{x}{y}}{M}{N}.
    \end{aligned}$$
    Terms with different outer constructors do not correspond. In particular, the equality relation on names compares free
    names literally while allowing corresponding bound names to differ.
-/
inductive NameRel : (ℕ → ℕ → Prop) → Term → Term → Prop where
  | var {R : ℕ → ℕ → Prop} {a b : ℕ} : R a b → NameRel R (.var a) (.var b)
  | app {R : ℕ → ℕ → Prop} {M N P Q : Term} : NameRel R M N → NameRel R P Q → NameRel R (.app M P) (.app N Q)
  | lam {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Term} : NameRel (bindNames R x y) M N → NameRel R (.lam x M) (.lam y N)

namespace NameRel

/-- Only the correspondence on the free variables of the terms matters. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First observe by induction that a comparison uses the relation only on the free-variable sets of its two terms. Every free name on either side has a corresponding free name on the other. The comparison with equality is reflexive and symmetric. Composition of comparisons follows by induction: beneath abstractions, the intermediate name is either bound on both sides or free on both sides. These cases give the extended composite relation. In particular, comparison with equality is transitive.
-/
theorem congr {R : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N)
    {S : ℕ → ℕ → Prop}
    (hs : ∀ a ∈ M.fv, ∀ b ∈ N.fv, R a b → S a b) : NameRel S M N := by
  induction h generalizing S with
  | @var R a b hab => exact .var (hs a (by simp [fv]) b (by simp [fv]) hab)
  | @app R M N P Q hM hP ihM ihP =>
    apply NameRel.app
    · apply ihM; intro a ha b hb hab
      exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
    · apply ihP; intro a ha b hb hab
      exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
  | @lam R x y M N h ih =>
    apply NameRel.lam
    apply ih
    intro a ha b hb hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hax, hby, hs a (Finset.mem_erase.mpr ⟨hax, ha⟩)
        b (Finset.mem_erase.mpr ⟨hby, hb⟩) hab⟩

theorem mono {R S : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N)
    (hs : ∀ a b, R a b → S a b) : NameRel S M N :=
  h.congr (fun a _ b _ => hs a b)

theorem refl (M : Term) : NameRel Eq M M := by
  induction M with
  | var a => exact .var rfl
  | app M N ihM ihN => exact .app ihM ihN
  | lam x M ih =>
    apply NameRel.lam
    apply ih.mono
    intro a b hab
    subst b
    by_cases ha : a = x
    · exact Or.inl ⟨ha, ha⟩
    · exact Or.inr ⟨ha, ha, rfl⟩

theorem symm {R : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N) :
    NameRel (fun b a => R a b) N M := by
  induction h with
  | var hab => exact .var hab
  | app hM hP ihM ihP => exact .app ihM ihP
  | @lam R x y M N h ih =>
    apply NameRel.lam
    apply ih.mono
    intro b a hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha, hab⟩

/-- Every free occurrence has a corresponding free name on the other side. -/
theorem fv_left {R : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N)
    {a : ℕ} (ha : a ∈ M.fv) : ∃ b ∈ N.fv, R a b := by
  induction h with
  | @var R a' b hab =>
    have he : a = a' := by simpa only [fv, Finset.mem_singleton] using ha
    subst a'; exact ⟨b, by simp [fv], hab⟩
  | app hM hP ihM ihP =>
    rcases Finset.mem_union.mp ha with hm | hp
    · obtain ⟨b, hb, hab⟩ := ihM hm
      exact ⟨b, Finset.mem_union_left _ hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := ihP hp
      exact ⟨b, Finset.mem_union_right _ hb, hab⟩
  | @lam R x y M N h ih =>
    obtain ⟨hax, ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨b, hb, hab⟩ := ih ha
    rcases hab with ⟨he, _⟩ | ⟨_, hby, hab⟩
    · exact (hax he).elim
    · exact ⟨b, Finset.mem_erase.mpr ⟨hby, hb⟩, hab⟩

theorem trans {R : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N)
    {S T : ℕ → ℕ → Prop} {P : Term} (h' : NameRel S N P)
    (ht : ∀ a b c, R a b → S b c → T a c) : NameRel T M P := by
  induction h generalizing S T P with
  | var hab => cases h' with | var hbc => exact .var (ht _ _ _ hab hbc)
  | app hM hN ihM ihN =>
    cases h' with
    | app hP hQ => exact .app (ihM hP ht) (ihN hQ ht)
  | @lam R x y M N h ih =>
    cases h' with
    | @lam _ _ z _ P hp =>
      apply NameRel.lam
      apply ih hp
      intro a b c hab hbc
      rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
      · rcases hbc with ⟨_, rfl⟩ | ⟨hby, _⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact (hby rfl).elim
      · rcases hbc with ⟨he, _⟩ | ⟨_, hcz, hbc⟩
        · exact (hby he).elim
        · exact Or.inr ⟨hax, hcz, ht a b c hab hbc⟩

/-- Capture-avoiding replacement of one free name transports its correspondence. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    The key renaming step is the following. Suppose $\LambdaNameCorrespondence{R}{M}{N}$ and, for free names $a$ of $M$ and $b$ of $N$, the implication
    $$\begin{aligned}
    R(a,b)\ \land\ a=x&\ \Longrightarrow\ S(z,b),\\
    R(a,b)\ \land\ a\ne x&\ \Longrightarrow\ S(a,b)
    \end{aligned}$$
    holds. Then $\LambdaNameCorrespondence{S}{\SubstLambda{M}{x}{z}}{N}$. Induct on a node-count bound for $M$, allowing both relations to vary. Variables and applications follow from the substitution clauses. Under an abstraction binding $x$, substitution stops, and the extended relation masks $x$. Under any other binder different from $z$, apply the induction hypothesis to the body. If the binder is $z$, substitution first renames it to a fresh variable. Apply the induction hypothesis to that variable renaming, then again to replacement of $x$ by $z$. Both calls concern bodies with the original body's node count. Freshness ensures that the newly chosen name has no pre-existing free occurrence, so only the intended bound-name correspondence changes. This proves the claim, and the symmetric claim applies on the right.
-/
theorem rename_left {R S : ℕ → ℕ → Prop} {M N : Term} (h : NameRel R M N)
    (x z : ℕ)
    (hs : ∀ a ∈ M.fv, ∀ b ∈ N.fv, R a b → S (if a = x then z else a) b) :
    NameRel S (M.subst x (.var z)) N := by
  have bounded : ∀ k (M N : Term) (R S : ℕ → ℕ → Prop) x z, M.nodes ≤ k → NameRel R M N →
      (∀ a ∈ M.fv, ∀ b ∈ N.fv, R a b → S (if a = x then z else a) b) →
      NameRel S (M.subst x (.var z)) N := by
    intro k
    induction k with
    | zero => intro M N R S x z hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N R S x z hk h hs
      cases h with
      | @var R a b hab =>
        have hh := hs a (by simp [fv]) b (by simp [fv]) hab
        rw [subst_var]
        by_cases ha : a = x
        · rw [ite_eq_left ha]; exact .var (by simpa only [ite_eq_left ha] using hh)
        · rw [ite_eq_right ha]; exact .var (by simpa only [ite_eq_right ha] using hh)
      | @app R A B C D hA hC =>
        have ha : A.nodes ≤ k := by simp only [nodes] at hk; omega
        have hc : C.nodes ≤ k := by simp only [nodes] at hk; omega
        rw [subst_app]
        apply NameRel.app
        · apply ih A B R S x z ha hA
          intro a ha b hb hab
          exact hs a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) hab
        · apply ih C D R S x z hc hC
          intro a ha b hb hab
          exact hs a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) hab
      | @lam R u v A B hab =>
        have hm : A.nodes ≤ k := by simp only [nodes] at hk; omega
        rw [subst_lam]
        by_cases hux : u = x
        · rw [ite_eq_left hux]
          apply NameRel.lam
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
          · rw [ite_eq_left (by simpa only [fv, Finset.mem_singleton] using huz)]
            apply NameRel.lam
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
            rw [ite_eq_right (by simp [fv])]
            let w := fresh (A.fv ∪ (Term.var z).fv ∪ {x})
            have hw : w ∉ A.fv ∧ w ≠ z ∧ w ≠ x := by
              simpa only [w, fv, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
                using fresh_not_mem (A.fv ∪ (Term.var z).fv ∪ {x})
            change NameRel S (.lam w ((A.subst z (.var w)).subst x (.var z))) (.lam v B)
            apply NameRel.lam
            have hr : NameRel (bindNames R w v) (A.subst z (.var w)) B := by
              apply ih A B (bindNames R z v) (bindNames R w v) z w hm hab
              intro a ha b hb hr
              rcases hr with ⟨rfl, rfl⟩ | ⟨haz, hbv, hr⟩
              · simp only [ite_true]; exact Or.inl ⟨rfl, rfl⟩
              · rw [ite_eq_right haz]
                have haw : a ≠ w := by intro he; subst a; exact hw.1 ha
                exact Or.inr ⟨haw, hbv, hr⟩
            apply ih (A.subst z (.var w)) B (bindNames R w v) (bindNames S w v) x z
              (by simpa only [nodes_subst_var] using hm) hr
            intro a ha b hb hr
            rcases hr with ⟨rfl, rfl⟩ | ⟨haw, hbv, hr⟩
            · simp only [ite_eq_right hw.2.2]; exact Or.inl ⟨rfl, rfl⟩
            · have ha' : a ∈ A.fv ∧ a ≠ z := by
                rcases (mem_fv_subst A z (.var w) a).mp ha with h | ⟨_, h⟩
                · exact h
                · exact (haw (by simpa only [fv, Finset.mem_singleton] using h)).elim
              have hsab := hs a (Finset.mem_erase.mpr ⟨ha'.2, ha'.1⟩)
                b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hr
              refine Or.inr ⟨?_, hbv, hsab⟩
              split_ifs with hax
              · exact hw.2.1.symm
              · exact haw
  exact bounded M.nodes M N R S x z le_rfl h hs

/-- Changing one abstraction's bound name transports the corresponding body. -/
theorem rebind_left {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Term}
    (h : NameRel (bindNames R x y) M N) (z : ℕ) (hz : z ∉ M.fv) :
    NameRel (bindNames R z y) (M.subst x (.var z)) N := by
  apply h.rename_left x z
  intro a ha b hb hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨hax, hby, hab⟩
  · simp only [ite_true]; exact Or.inl ⟨rfl, rfl⟩
  · rw [ite_eq_right hax]
    have haz : a ≠ z := by intro he; subst a; exact hz ha
    exact Or.inr ⟨haz, hby, hab⟩

theorem rebind_right {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Term}
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

theorem eq_symm {M N : Term} (h : NameRel Eq M N) : NameRel Eq N M :=
  h.symm.mono (fun _ _ h => h.symm)

theorem eq_trans {M N P : Term} (h : NameRel Eq M N) (h' : NameRel Eq N P) :
    NameRel Eq M P := h.trans h' (fun _ _ _ h₁ h₂ => h₁.trans h₂)

theorem eq_lam {M N : Term} (h : NameRel Eq M N) (x : ℕ) :
    NameRel Eq (.lam x M) (.lam x N) := by
  apply NameRel.lam
  apply h.mono
  intro a b hab
  subst b
  by_cases ha : a = x
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨ha, ha, rfl⟩

theorem eq_rename (M : Term) (x z : ℕ) (hz : z ∉ M.fv) :
    NameRel Eq (.lam x M) (.lam z (M.subst x (.var z))) := by
  apply NameRel.eq_symm
  apply NameRel.lam
  apply (NameRel.refl M).rename_left x z
  intro a ha b hb hab
  subst b
  by_cases hax : a = x
  · rw [ite_eq_left hax]; exact Or.inl ⟨rfl, hax⟩
  · rw [ite_eq_right hax]
    have haz : a ≠ z := by intro he; subst a; exact hz ha
    exact Or.inr ⟨haz, hax, rfl⟩

/-- Equality correspondence can be realized by actual fresh-name rewrites. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Comparison of named terms
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Apply this renaming step to a pair of corresponding abstraction bodies. A fresh change of one binder preserves the comparison when its recorded name is changed at the same time. Hence every generating alpha-renaming, and therefore every alpha-equivalence derivation, preserves comparison with equality. Conversely, induct on a node-count bound for two terms that compare with equality. Variables agree, and applications reduce to their component comparisons. For abstractions, choose one name fresh for both bodies and rename both binders to it. The renaming step makes the two renamed bodies compare with equality. Their node counts are unchanged, so the induction hypothesis gives alpha-equivalence of the bodies. Lift through their common abstraction and undo the two binder renamings. This proves the converse.
-/
theorem eq_renameEq {M N : Term} (h : NameRel Eq M N) : RenameEq M N := by
  have bounded : ∀ k (M N : Term), M.nodes ≤ k → NameRel Eq M N → RenameEq M N := by
    intro k
    induction k with
    | zero => intro M N hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N hk h
      cases h with
      | var hab => subst_vars; exact .refl _
      | @app _ A B C D hab hcd =>
        apply RenameEq.app
        · apply ih A B (by simp only [nodes] at hk; omega) hab
        · apply ih C D (by simp only [nodes] at hk; omega) hcd
      | @lam _ x y A B hab =>
        let z := fresh (A.fv ∪ B.fv)
        have hz : z ∉ A.fv ∧ z ∉ B.fv := by
          simpa only [z, Finset.mem_union, not_or] using fresh_not_mem (A.fv ∪ B.fv)
        have hbody : NameRel Eq (A.subst x (.var z)) (B.subst y (.var z)) := by
          apply ((hab.rebind_left z hz.1).rebind_right z hz.2).mono
          intro a b hr
          rcases hr with ⟨rfl, rfl⟩ | ⟨_, _, hr⟩
          · rfl
          · exact hr
        have hm : (A.subst x (.var z)).nodes ≤ k := by
          rw [nodes_subst_var]; simp only [nodes] at hk; omega
        exact (RenameEq.rename A x z hz.1).trans
          ((RenameEq.lam z (ih _ _ hm hbody)).trans (RenameEq.rename B y z hz.2).symm)
  exact bounded M.nodes M N le_rfl h

end NameRel

/-- Every sequence of named alpha-renamings preserves the correspondence judgment. -/
theorem RenameEq.nameRel {M N : Term} (h : RenameEq M N) : NameRel Eq M N := by
  induction h with
  | refl M => exact NameRel.refl M
  | symm _ ih => exact ih.eq_symm
  | trans _ _ ih₁ ih₂ => exact ih₁.eq_trans ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam x _ ih => exact ih.eq_lam x
  | rename M x z hz => exact NameRel.eq_rename M x z hz

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Comparison of named terms
-/
theorem renameEq_iff_nameRel (M N : Term) : RenameEq M N ↔ NameRel Eq M N :=
  ⟨RenameEq.nameRel, NameRel.eq_renameEq⟩

namespace NameRel

/-- Inspect the existing substitution clauses beneath an abstraction. -/
theorem prepare_subst_lam (M : Term) (u x : ℕ) (T : Term) (hux : u ≠ x) :
    ∃ (z : ℕ) (B : Term), (Term.lam u M).subst x T = Term.lam z (B.subst x T) ∧ B.nodes = M.nodes ∧
      z ≠ x ∧ z ∉ T.fv ∧
      ∀ (R : ℕ → ℕ → Prop) y N, NameRel (bindNames R u y) M N →
        NameRel (bindNames R z y) B N := by
  by_cases hu : u ∉ T.fv
  · refine ⟨u, M, ?_, rfl, hux, hu, ?_⟩
    · rw [subst_lam, ite_eq_right hux, ite_eq_left hu]
    · intro R y N h; exact h
  · let z := fresh (M.fv ∪ T.fv ∪ {x})
    have hz : z ∉ M.fv ∧ z ∉ T.fv ∧ z ≠ x := by
      simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
        using fresh_not_mem (M.fv ∪ T.fv ∪ {x})
    refine ⟨z, M.subst u (.var z), ?_, nodes_subst_var M u z, hz.2.2, hz.2.1, ?_⟩
    · rw [subst_lam, ite_eq_right hux, ite_eq_right hu]
    · intro R y N h; exact h.rebind_left z hz.1

theorem symm_bind {R : ℕ → ℕ → Prop} {x y : ℕ} {M N : Term}
    (h : NameRel (bindNames R x y) M N) :
    NameRel (bindNames (fun b a => R a b) y x) N M := by
  apply h.symm.mono
  intro b a hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
  · exact Or.inl ⟨hb, ha⟩
  · exact Or.inr ⟨hb, ha, hab⟩

/-- Replace a pair of corresponding free names by corresponding terms. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Substitution of related terms
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induct on a node-count bound for $M$, allowing the terms and relations to vary. If $x$ is not free in $M$, the correspondence of free names and the first hypothesis imply that $y$ is not free in $M'$. Substitution for an absent variable changes a term only by binder renaming: this follows directly from the substitution clauses by induction on node count, undoing any fresh binder renaming after applying the induction hypothesis to its body. Thus both substitutions preserve comparison, and the second hypothesis changes the comparison relation from $R$ to $S$. At variables that are replaced, use the given comparison of $N,N'$; at other variables use the second hypothesis. Applications follow from the two induction hypotheses.

    It remains to consider abstractions when the variables being replaced occur freely. Neither binder is then the variable being replaced. On each side inspect the existing substitution clause: retain the binder if it is absent from the replacement's free variables, and otherwise rename it to the fresh variable chosen by that clause. The preceding renaming step transports the body comparison to the resulting pair of binders. Both resulting binders are distinct from the variables being replaced and absent from their respective replacement terms. Hence the comparison of the replacements remains valid under the extended relation. The two hypotheses on the variable relations remain valid as well: the two bound names correspond to each other and are not replaced, while every free-name pair satisfies the original hypotheses. Apply the induction hypothesis to the two bodies and restore the abstractions. Variable renaming preserves body size, so this recursive call has a smaller bound.
    \end{proof}
-/
theorem subst {R S : ℕ → ℕ → Prop} {M N T U : Term} (h : NameRel R M N)
    (x y : ℕ) (ht : NameRel S T U)
    (hkeys : ∀ a b, R a b → (a = x ↔ b = y))
    (hkeep : ∀ a b, R a b → a ≠ x → S a b) :
    NameRel S (M.subst x T) (N.subst y U) := by
  have bounded : ∀ k (M N T U : Term) (R S : ℕ → ℕ → Prop) x y,
      M.nodes ≤ k → NameRel R M N → NameRel S T U →
      (∀ a b, R a b → (a = x ↔ b = y)) →
      (∀ a b, R a b → a ≠ x → S a b) →
      NameRel S (M.subst x T) (N.subst y U) := by
    intro k
    induction k with
    | zero => intro M N T U R S x y hk; have := M.nodes_pos; omega
    | succ k ih =>
      intro M N T U R S x y hk h ht hkeys hkeep
      by_cases hx : x ∈ M.fv
      · have hy : y ∈ N.fv := by
          obtain ⟨b, hb, hr⟩ := h.fv_left hx
          have he := (hkeys x b hr).mp rfl
          simpa only [he] using hb
        cases h with
        | @var _ a b hab =>
          rw [subst_var, subst_var]
          by_cases hax : a = x
          · rw [ite_eq_left hax, ite_eq_left ((hkeys a b hab).mp hax)]
            exact ht
          · have hby : b ≠ y := fun he => hax ((hkeys a b hab).mpr he)
            rw [ite_eq_right hax, ite_eq_right hby]
            exact .var (hkeep a b hab hax)
        | @app _ A B C D hab hcd =>
          rw [subst_app, subst_app]
          exact .app (ih A B T U R S x y (by simp only [nodes] at hk; omega) hab ht hkeys hkeep)
            (ih C D T U R S x y (by simp only [nodes] at hk; omega) hcd ht hkeys hkeep)
        | @lam _ u v A B hab =>
          have hux : u ≠ x := (Finset.mem_erase.mp hx).1.symm
          have hvy : v ≠ y := (Finset.mem_erase.mp hy).1.symm
          obtain ⟨u', A', heA, hnA, hux', huT, hA⟩ := prepare_subst_lam A u x T hux
          obtain ⟨v', B', heB, hnB, hvy', hvU, hB⟩ := prepare_subst_lam B v y U hvy
          rw [heA, heB]
          apply NameRel.lam
          have hAB : NameRel (bindNames R u' v') A' B' :=
            (hB (fun b a => R a b) u' A' ((hA R v B hab).symm_bind)).symm_bind
          have hTU : NameRel (bindNames S u' v') T U := by
            apply ht.congr
            intro a ha b hb hr
            have hau : a ≠ u' := by intro he; subst a; exact huT ha
            have hbv : b ≠ v' := by intro he; subst b; exact hvU hb
            exact Or.inr ⟨hau, hbv, hr⟩
          apply ih A' B' T U (bindNames R u' v') (bindNames S u' v') x y
            (by rw [hnA]; simp only [nodes] at hk; omega) hAB hTU
          · intro a b hr
            rcases hr with ⟨rfl, rfl⟩ | ⟨_, _, hr⟩
            · simp only [hux', hvy']
            · exact hkeys a b hr
          · intro a b hr hax
            rcases hr with ⟨rfl, rfl⟩ | ⟨hau, hbv, hr⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨hau, hbv, hkeep a b hr hax⟩
      · have hy : y ∉ N.fv := by
          intro hy
          obtain ⟨a, ha, hr⟩ := h.symm.fv_left hy
          have he := (hkeys a y hr).mpr rfl
          exact hx (by simpa only [he] using ha)
        have hMN : NameRel S M N := by
          apply h.congr
          intro a ha b hb hr
          exact hkeep a b hr (by intro he; subst a; exact hx ha)
        have hleft := (renameEq_subst_not_free M T x hx).nameRel
        have hright := (renameEq_subst_not_free N U y hy).nameRel.eq_symm
        exact (hleft.trans hMN (by intro a b c he hr; subst b; exact hr)).trans hright
          (by intro a b c hr he; subst c; exact hr)
  exact bounded M.nodes M N T U R S x y le_rfl h ht hkeys hkeep

end NameRel

/-- Substitution compatibility, proved entirely with named terms. -/
theorem RenameEq.subst_named {M M' N N' : Term} (hM : RenameEq M M')
    (hN : RenameEq N N') (x : ℕ) : RenameEq (M.subst x N) (M'.subst x N') := by
  apply NameRel.eq_renameEq
  apply hM.nameRel.subst x x hN.nameRel
  · intro a b hab; subst b; rfl
  · intro a b hab _; exact hab

/-- The result of contracting an abstraction does not depend on its named representative. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Compatibility with alpha-equivalence allows the operations and free-variable sets to descend to classes. If two named abstractions are alpha-equivalent, their bodies compare under the relation that pairs their bound names and equates all other free names. Apply \termuse{Substitution under corresponding names} to these bodies and the two alpha-equivalent arguments, with equality as the output relation. The paired bound names are exactly the names being replaced, and every other corresponding pair is equal. The conclusion states that the two contracta compare with equality, hence are alpha-equivalent. Thus contraction is independent of both the binder name and the chosen representatives.
-/
theorem RenameEq.contract_named {M M' N N' : Term} {x y : ℕ}
    (hM : RenameEq (Term.lam x M) (Term.lam y M')) (hN : RenameEq N N') :
    RenameEq (M.subst x N) (M'.subst y N') := by
  have hh := hM.nameRel
  cases hh with
  | lam hbody =>
    apply NameRel.eq_renameEq
    apply hbody.subst x y hN.nameRel
    · intro a b hr
      rcases hr with ⟨rfl, rfl⟩ | ⟨hax, hby, _⟩
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
      · simp only [hax, hby]
    · intro a b hr hax
      rcases hr with ⟨he, _⟩ | ⟨_, _, hr⟩
      · exact (hax he).elim
      · exact hr

namespace NameRel
/-- Recursive comparison of the original named terms is decidable. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: lemma
  title: Comparison of named terms
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Finally, the displayed comparison rules give a terminating decision procedure. Compare the outer constructors; at variables test the current relation, at applications compare both components, and at abstractions extend the relation and compare the bodies. Extending a decidable relation remains decidable. Every recursive call concerns a proper subterm of the first term, so its node count decreases.
    \end{proof}
-/
def decidable (R : ℕ → ℕ → Prop) (d : DecidableRel R) (M N : Term) :
    Decidable (NameRel R M N) := by
  cases M with
  | var a =>
    cases N with
    | var b =>
      cases d a b with
      | isTrue h => exact isTrue (.var h)
      | isFalse h => exact isFalse (by intro hr; cases hr with | var hab => exact h hab)
    | app A B => exact isFalse (by intro h; cases h)
    | lam y B => exact isFalse (by intro h; cases h)
  | app A B =>
    cases N with
    | var b => exact isFalse (by intro h; cases h)
    | app C D =>
      cases decidable R d A C with
      | isFalse h => exact isFalse (by intro hr; cases hr with | app h₁ h₂ => exact h h₁)
      | isTrue h₁ =>
        cases decidable R d B D with
        | isFalse h => exact isFalse (by intro hr; cases hr with | app h₁ h₂ => exact h h₂)
        | isTrue h₂ => exact isTrue (.app h₁ h₂)
    | lam y B => exact isFalse (by intro h; cases h)
  | lam x A =>
    cases N with
    | var b => exact isFalse (by intro h; cases h)
    | app A B => exact isFalse (by intro h; cases h)
    | lam y B =>
      let d' : DecidableRel (bindNames R x y) := fun a b => by
        letI : Decidable (R a b) := d a b
        unfold bindNames
        infer_instance
      cases decidable (bindNames R x y) d' A B with
      | isTrue h => exact isTrue (.lam h)
      | isFalse h => exact isFalse (by intro hr; cases hr with | lam hab => exact h hab)
termination_by M.nodes
decreasing_by all_goals simp only [nodes]; omega

end NameRel
end PolishSpaceBook.NamedLambda.Term
