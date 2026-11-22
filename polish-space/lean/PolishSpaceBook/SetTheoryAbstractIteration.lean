module

public import PolishSpaceBook.SetTheoryAbstractGraphs

@[expose] public section

/-! # Internal finite iteration without external well-foundedness -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def graphOnBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 1).imp (internalKuratowskiFormula (2 : Fin 5) 3 4).ex.ex).all ⊓
    (((internalApplicationFormula (1 : Fin 5) 2 3 ⊓ internalApplicationFormula 1 2 4).imp
      (equalAt 3 4)).all.all.all ⊓
      (((internalApplicationFormula (1 : Fin 4) 2 3).ex).iff (memberAt 2 0)).all)

theorem realize_graphOnBody (xs : Fin 2 → M) :
    graphOnBody.Realize Empty.elim xs ↔ IsGraphOn (xs 1) (xs 0) := by
  simp only [graphOnBody, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_iff,
    realize_internalKuratowskiFormula, realize_internalApplicationFormula,
    realize_memberAt, realize_equalAt]
  simp only [Fin.snoc, IsGraphOn, IsFunctionGraph]
  constructor
  · rintro ⟨hp, hf, hd⟩
    exact ⟨⟨hp, fun a b c hb hc => hf a b c ⟨hb, hc⟩⟩, hd⟩
  · rintro ⟨⟨hp, hf⟩, hd⟩
    exact ⟨hp, fun a b c h => hf a b c h.1 h.2, hd⟩

def graphAgreementBody : ForcingFormulas.Formula 3 :=
  ((internalApplicationFormula (0 : Fin 5) 2 3 ⊓ internalApplicationFormula 1 2 4).imp
    (equalAt 3 4)).all.all

theorem realize_graphAgreementBody (xs : Fin 3 → M) :
    graphAgreementBody.Realize Empty.elim xs ↔
      ∀ a b : M, GraphApplication (xs 0) (xs 2) a →
        GraphApplication (xs 1) (xs 2) b → a = b := by
  simp only [graphAgreementBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, realize_internalApplicationFormula, realize_equalAt]
  simp only [Fin.snoc, and_imp]
  rfl

/-- A sequence on the internal initial segment `n`, with fixed initial value
and a relational step. Its defining formula is supplied below. -/
def IsIteration (R : M → M → Prop) (s n f : M) : Prop :=
  IsGraphOn f n ∧
    (∀ e : M, member e n → IsEmptyObject e → GraphApplication f e s) ∧
    ∀ k l a b : M, member l n → IsSuccessorObject k l →
      GraphApplication f k a → GraphApplication f l b → R a b

def iterationZeroBody : ForcingFormulas.Formula 3 :=
  boundedAll (1 : Fin 3)
    ((reindex emptyObjectBody ![(3 : Fin 4)]).imp (internalApplicationFormula 2 3 0))

theorem realize_iterationZeroBody (xs : Fin 3 → M) :
    iterationZeroBody.Realize Empty.elim xs ↔
      ∀ e : M, member e (xs 1) → IsEmptyObject e → GraphApplication (xs 2) e (xs 0) := by
  simp only [iterationZeroBody, realize_boundedAll, BoundedFormula.realize_imp,
    realize_reindex, realize_emptyObjectBody, realize_internalApplicationFormula]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Fin.snoc]
  rfl

def iterationStepBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 2)) :
    ForcingFormulas.Formula (p + 3) :=
  let k := (Fin.last (p + 3)).castSucc.castSucc.castSucc
  let l := (Fin.last (p + 4)).castSucc.castSucc
  let a := (Fin.last (p + 5)).castSucc
  let b := Fin.last (p + 6)
  let n := (Fin.last (p + 1)).castSucc.castSucc.castSucc.castSucc.castSucc
  let f := (Fin.last (p + 2)).castSucc.castSucc.castSucc.castSucc
  ((memberAt l n ⊓ reindex successorObjectBody ![k, l] ⊓
      internalApplicationFormula f k a ⊓ internalApplicationFormula f l b).imp
    (reindex φ (Fin.snoc (Fin.snoc
      (fun i : Fin p => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      a) b))).all.all.all.all

theorem realize_iterationStepBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 2))
    (ps : Fin p → M) (s n f : M) :
    (iterationStepBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps s) n) f) ↔
      ∀ k l a b : M, member l n → IsSuccessorObject k l →
        GraphApplication f k a → GraphApplication f l b →
          φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [iterationStepBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, realize_memberAt, realize_reindex, realize_successorObjectBody,
    realize_internalApplicationFormula, Fin.comp_snoc, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last, and_imp]

def iterationBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 2)) : ForcingFormulas.Formula (p + 3) :=
  reindex graphOnBody ![(Fin.last (p + 1)).castSucc, Fin.last (p + 2)] ⊓
    (reindex iterationZeroBody ![(Fin.last p).castSucc.castSucc,
      (Fin.last (p + 1)).castSucc, Fin.last (p + 2)] ⊓
      iterationStepBody φ)

theorem realize_iterationBody {p : ℕ} (φ : ForcingFormulas.Formula (p + 2))
    (ps : Fin p → M) (s n f : M) :
    (iterationBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps s) n) f) ↔
      IsIteration (fun a b => φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) s n f := by
  simp only [iterationBody, BoundedFormula.realize_inf, realize_reindex,
    realize_graphOnBody, realize_iterationZeroBody, realize_iterationStepBody,
    IsIteration, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.snoc_castSucc, Fin.snoc_last]

/-- Agreement uses internal definable induction on the first sequence's
domain. No external well-foundedness of the membership relation is used. -/
theorem iterations_agree (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) {R : M → M → Prop}
    (hR : ∀ a b c : M, R a b → R a c → b = c)
    {s n m f g : M} (hn : member n W) (hm : member m W)
    (hf : IsIteration R s n f) (hg : IsIteration R s m g) :
    ∀ k a b : M, GraphApplication f k a → GraphApplication g k b → a = b := by
  have ht := leastInductiveObject_members_transitive hM hW
  have hw := leastInductiveObject_transitive hM hW
  have hi := fullZFC_definable_induction graphAgreementBody hM ![f, g] n (ht n hn)
    (fun k hkn ih => (realize_graphAgreementBody _).mpr (by
      intro a b hfa hgb
      have hkm := (hg.1.2 k).mp ⟨b, hgb⟩
      rcases leastInductiveObject_zero_or_successor hM hW k (hw n hn k hkn) with he | ⟨j, _, hjk⟩
      · exact (hf.1.1.2 k a s hfa (hf.2.1 k hkn he)).trans
          (hg.1.1.2 k b s hgb (hg.2.1 k hkm he)).symm
      · have hjk' := (hjk j).mpr (Or.inr rfl)
        obtain ⟨a', hfa'⟩ := (hf.1.2 j).mpr (ht n hn k hkn j hjk')
        obtain ⟨b', hgb'⟩ := (hg.1.2 j).mpr (ht m hm k hkm j hjk')
        have hab := (realize_graphAgreementBody _).mp (ih j hjk') a' b' hfa' hgb'
        subst b'
        exact hR a' a b (hf.2.2 j k a' a hkn hjk hfa' hfa)
          (hg.2.2 j k a' b hkm hjk hgb' hgb)))
  intro k a b hfa hgb
  exact (realize_graphAgreementBody _).mp (hi k ((hf.1.2 k).mp ⟨a, hfa⟩)) a b hfa hgb

theorem iteration_unique (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) {R : M → M → Prop}
    (hR : ∀ a b c : M, R a b → R a c → b = c)
    {s n f g : M} (hn : member n W) (hf : IsIteration R s n f) (hg : IsIteration R s n g) :
    f = g := by
  apply functionGraph_ext (hM.realize_of_mem _ ZFCAxiom.extensionality) hf.1.1 hg.1.1
  intro a b
  constructor
  · intro hab
    obtain ⟨c, hac⟩ := (hg.1.2 a).mpr ((hf.1.2 a).mp ⟨b, hab⟩)
    exact (iterations_agree hM hW hR hn hn hf hg a b c hab hac).symm ▸ hac
  · intro hab
    obtain ⟨c, hac⟩ := (hf.1.2 a).mpr ((hg.1.2 a).mp ⟨b, hab⟩)
    exact (iterations_agree hM hW hR hn hn hg hf a b c hab hac).symm ▸ hac

theorem iteration_empty {R : M → M → Prop} (s : M) {e : M} (he : IsEmptyObject e) :
    IsIteration R s e e :=
  ⟨isGraphOn_empty he, fun a ha => False.elim (he a ha),
    fun _ l _ _ hl => False.elim (he l hl)⟩

/-- The next finite sequence is formed by adjoining exactly one ordered pair.
Only existence and functionality of the concrete step relation are used. -/
theorem iteration_extend (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) {R : M → M → Prop}
    (hR : ∀ a : M, ∃ b : M, R a b) {s n N f : M} (hn : member n W)
    (hN : IsSuccessorObject n N) (hf : IsIteration R s n f) :
    ∃ g : M, IsIteration R s N g := by
  have hp := hM.realize_of_mem _ ZFCAxiom.pairing
  have hfoundation := hM.realize_of_mem _ ZFCAxiom.foundation
  have hext := hM.realize_of_mem _ ZFCAxiom.extensionality
  have hnn := not_member_self_of_foundation hp hfoundation n
  have htrans := leastInductiveObject_members_transitive hM hW n hn
  obtain ⟨b, hbzero, hbpred⟩ : ∃ b : M, (IsEmptyObject n → b = s) ∧
      ∀ k a : M, IsSuccessorObject k n → GraphApplication f k a → R a b := by
    rcases leastInductiveObject_zero_or_successor hM hW n hn with he | ⟨k, _, hkn⟩
    · exact ⟨s, fun _ => rfl, fun j _ hjn _ => False.elim (he j ((hjn j).mpr (Or.inr rfl)))⟩
    · obtain ⟨a, ha⟩ := (hf.1.2 k).mpr ((hkn k).mpr (Or.inr rfl))
      obtain ⟨b, hb⟩ := hR a
      refine ⟨b, fun he => False.elim (he k ((hkn k).mpr (Or.inr rfl))), ?_⟩
      intro j c hjn hc
      have hj := successorObject_injective hp hfoundation hjn hkn
      subst j
      have hc' := hf.1.1.2 k c a hc ha
      exact hc' ▸ hb
  obtain ⟨g, hg⟩ := exists_graphInsert hM f n b
  have happ := graphApplication_insert hext hp hg
  refine ⟨g, isGraphOn_insert hM hf.1 hnn hN hg, ?_, ?_⟩
  · intro e heN he
    rcases (hN e).mp heN with hen | hen
    · exact (happ e s).mpr (Or.inl (hf.2.1 e hen he))
    · subst e
      exact (happ n s).mpr (Or.inr ⟨rfl, (hbzero he).symm⟩)
  · intro k l a c hlN hkl hka hlc
    rcases (happ l c).mp hlc with hlc | ⟨hln, hcb⟩
    · have hln := (hf.1.2 l).mp ⟨c, hlc⟩
      rcases (happ k a).mp hka with hka | ⟨hkn, _⟩
      · exact hf.2.2 k l a c hln hkl hka hlc
      · subst k
        exact False.elim (hnn (htrans l hln n ((hkl n).mpr (Or.inr rfl))))
    · subst l
      subst c
      rcases (happ k a).mp hka with hka | ⟨hkn, _⟩
      · exact hbpred k a hkl hka
      · subst k
        exact False.elim (hnn ((hkl n).mpr (Or.inr rfl)))

/-- Every internal natural admits a unique finite sequence for a definable
total functional step. The assertion is proved by the model's formula
induction principle, so it covers its nonstandard naturals as well. -/
theorem finite_iteration_existsUnique (hM : M ⊨ fullZFCTheory) {W : M}
    (hW : IsLeastInductiveObject W) {p : ℕ} (φ : ForcingFormulas.Formula (p + 2))
    (ps : Fin p → M) (s : M)
    (hφ : ∀ a : M, ∃! b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b))
    (n : M) (hn : member n W) :
    ∃! f : M, (iterationBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps s) n) f) := by
  let R := fun a b : M => φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)
  have hR : ∀ a b c : M, R a b → R a c → b = c := by
    intro a b c hb hc
    obtain ⟨d, _, hd⟩ := hφ a
    exact (hd b hb).trans (hd c hc).symm
  have hi := leastInductiveObject_induction (iterationBody φ).ex
    (fullZFC_model_separation hM _) (Fin.snoc ps s) W hW
    (fun e _ he => by
      apply BoundedFormula.realize_ex.mpr
      exact ⟨e, (realize_iterationBody φ ps s e e).mpr (iteration_empty s he)⟩)
    (fun a b ha _ hab h => by
      obtain ⟨f, hf⟩ := BoundedFormula.realize_ex.mp h
      obtain ⟨g, hg⟩ := iteration_extend hM hW (fun a => (hφ a).exists) ha hab
        ((realize_iterationBody φ ps s a f).mp hf)
      exact BoundedFormula.realize_ex.mpr ⟨g, (realize_iterationBody φ ps s b g).mpr hg⟩)
  obtain ⟨f, hf⟩ := BoundedFormula.realize_ex.mp (hi n hn)
  refine ⟨f, hf, fun g hg => ?_⟩
  exact iteration_unique hM hW hR hn ((realize_iterationBody φ ps s n g).mp hg)
    ((realize_iterationBody φ ps s n f).mp hf)

end PolishSpaceBook.SetTheoryModels.AbstractMembership
