module

public import PolishSpaceBook.KleeneBrouwerOrder
public import PolishSpaceBook.LambdaRecursiveOrdinals
public import PolishSpaceBook.LambdaRecursiveTrees

@[expose] public section

/-! # Lambda comparison programs and recursive bounds for well-founded trees -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace KleeneBrouwer

instance before_decidable (s t : List ℕ) : Decidable (Before s t) := by
  cases s with
  | nil => exact isFalse (before_nil_left t)
  | cons a s =>
    cases t with
    | nil => exact isTrue trivial
    | cons b t =>
      letI := before_decidable s t
      exact inferInstanceAs (Decidable (a < b ∨ a = b ∧ Before s t))

def bit (s t : List ℕ) : ℕ := if Before s t then 1 else 0

/-- The second argument is the comparison function already built for the tail. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The comparison places the empty word last; for two nonempty words it compares their heads and, when
    they agree, their tails. In particular, a proper extension precedes its prefix. Use the list code,
    field programs, and list recursor already defined in this appendix. Put
    $$\begin{aligned}
    \LambdaTermName{kbZero}&:=\lambdaab{e}{\ChurchNumeral{0}},\\
    \LambdaTermName{kbHead}(e)&:=\LambdaListField{1}e,\qquad \LambdaTermName{kbTail}(e):=\LambdaListField{2}e,\\
    \LambdaTermName{kbTailCase}(a, \LambdaTermName{compare},e)&:= \LambdaLeCase{ \LambdaTermName{kbHead}(e)}{a}{
    \LambdaTermName{compare}( \LambdaTermName{kbTail}(e))}{ \ChurchNumeral{1}},\\
    \LambdaTermName{kbCase}(a,\LambdaTermName{compare},e)&:=\LambdaLeCase{e}{\ChurchNumeral{0}}{\ChurchNumeral{1}}{
     \LambdaLeCase{a}{ \LambdaTermName{kbHead}(e)}{ \LambdaTermName{kbTailCase}(a, \LambdaTermName{compare},e)}{
    \ChurchNumeral{0}}},\\
    \LambdaTermName{kbStep}&:= \lambdaab{a}{ \lambdaab{ \LambdaTermName{compare}}{ \lambdaab{e}{
    \LambdaTermName{kbCase}(a, \LambdaTermName{compare},e)}}}.
    \end{aligned}$$
    Expand these abbreviations with distinct fresh binders. The value passed as $\LambdaTermName{compare}$ compares
    the tail of
    the first word with its argument. The zero branch returns one without inspecting the empty second word.
-/
def body (A F E : AlphaTerm) : AlphaTerm :=
  chooseLeBody E (numeral 0) (numeral 1)
    (chooseLeBody A (app (listFieldTerm true) E)
      (chooseLeBody (app (listFieldTerm true) E) A
        (app F (app (listFieldTerm false) E)) (numeral 1)) (numeral 0))

theorem body_fv (A F E : AlphaTerm) : (body A F E).fv = A.fv ∪ F.fv ∪ E.fv := by
  simp only [body,chooseLeBody_fv,fv_app]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem body_subst (A F E W : AlphaTerm) (x : ℕ) :
    (body A F E).subst x W = body (A.subst x W) (F.subst x W) (E.subst x W) := by
  simp only [body,chooseLeBody_subst,subst_app,subst_closed _ _ _ (listFieldTerm_closed true),
    subst_closed _ _ _ (listFieldTerm_closed false),subst_closed _ _ _ (numeral_closed 0),
    subst_closed _ _ _ (numeral_closed 1)]

def handler := lam 60 (lam 61 (lam 62 (body (var 60) (var 61) (var 62))))

theorem handler_closed : handler.Closed := by
  unfold handler Closed
  simp only [fv_lam,body_fv,fv_var]
  decide

theorem handler_start {A F E : AlphaTerm} (ha : A.Closed) (hf : F.Closed) (_he : E.Closed) :
    Relation.ReflTransGen Beta (app (app (app handler A) F) E) (body A F E) := by
  have h₁ : Beta (app handler A) (lam 61 (lam 62 (body A (var 61) (var 62)))) := by
    convert Beta.contract 60 (lam 61 (lam 62 (body (var 60) (var 61) (var 62)))) A using 1 <;> try rfl
    simp [subst_lam_fresh,body_subst,subst_var,show A.fv = ∅ from ha]
  have h₂ : Beta (app (lam 61 (lam 62 (body A (var 61) (var 62)))) F)
      (lam 62 (body A F (var 62))) := by
    convert Beta.contract 61 (lam 62 (body A (var 61) (var 62))) F using 1
    simp [subst_lam_fresh,body_subst,subst_var,show F.fv = ∅ from hf,subst_closed _ _ _ ha]
  have h₃ : Beta (app (lam 62 (body A F (var 62))) E) (body A F E) := by
    convert Beta.contract 62 (body A F (var 62)) E using 1
    simp [body_subst,subst_var,subst_closed _ _ _ ha,subst_closed _ _ _ hf]
  exact (beta_steps_app_left (beta_steps_app_left (.single h₁) _) _).trans
    ((beta_steps_app_left (.single h₂) _).trans (.single h₃))

def value : List ℕ → AlphaTerm
  | [] => numericalConstant 0
  | a :: s => app (app handler (numeral a)) (value s)

theorem value_closed (s : List ℕ) : (value s).Closed := by
  induction s with
  | nil => exact (numericalConstant_computes 0).1
  | cons a s ih => exact closed_app (closed_app handler_closed (numeral_closed a)) ih

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Define closed function values $\LambdaTermName{compare}_{[]}:= \LambdaTermName{kbZero}$ and
    $\LambdaTermName{compare}_{a::s}:= \LambdaTermName{kbStep} \ChurchNumeral{a} \LambdaTermName{compare}_s$. The
    list-recursion
    formula reduces the first application to $\LambdaTermName{compare}_s$. Induct on $s$ to prove the claimed behavior of
    $\LambdaTermName{compare}_s$ on every second word. For the empty first word, $\LambdaTermName{kbZero}$ always
    returns zero. For $a::s$, three beta
    contractions expose $\LambdaTermName{kbCase}$. If the second word is empty, its code is zero and the outer test
    returns one.
    If it is $b::t$, the two field computations return $\ChurchNumeral{b}$ and $\ChurchNumeral{
    \LambdaListCode{t}}$. The two numerical
    comparisons return one when $a<b$, zero when $a>b$, and the value of $\LambdaTermName{compare}_s$ on
    $\ChurchNumeral{ \LambdaListCode{t}}$ when $a=b$.
    The induction hypothesis supplies that last value. These are exactly the defining comparison clauses.
    The recursor and handler are closed, and all reductions used here are finite beta reductions.
    \end{proof}
-/
theorem value_apply (s t : List ℕ) : Relation.ReflTransGen Beta
    (app (value s) (numeral (NatListCode.encode t))) (numeral (bit s t)) := by
  induction s generalizing t with
  | nil => simpa [value,bit] using (numericalConstant_computes 0).2 (NatListCode.encode t)
  | cons a s ih =>
    apply (handler_start (numeral_closed a) (value_closed s) (numeral_closed _)).trans
    cases t with
    | nil =>
      unfold body
      -- Zero testing does not evaluate the unused comparison branch.
      unfold chooseLeBody
      apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm
        (subtractionTerm_apply 0 0)) _) _).trans
      simpa [bit,NatListCode.encode] using branch_zero (numeral 1) _ (by rw [numeral_closed]; simp)
    | cons b t =>
      have hhead := listFieldTerm_cons true b (NatListCode.encode t)
      have htail := listFieldTerm_cons false b (NatListCode.encode t)
      simp only [ite_true] at hhead htail
      have hrec := (beta_steps_app_right (value s) htail).trans (ih t)
      have hinner := (chooseLeBody_steps hhead .refl hrec .refl).trans
        (chooseLeBody_apply b a (bit s t) 1)
      have houter := (chooseLeBody_steps .refl hhead hinner .refl).trans
        (chooseLeBody_apply a b (if b ≤ a then bit s t else 1) 0)
      have h := (chooseLeBody_steps .refl .refl .refl houter).trans
        (chooseLeBody_apply (NatListCode.encode (b :: t)) 0 1
          (if a ≤ b then if b ≤ a then bit s t else 1 else 0))
      have heq : (if NatListCode.encode (b :: t) ≤ 0 then 1 else
          if a ≤ b then if b ≤ a then bit s t else 1 else 0) = bit (a :: s) (b :: t) := by
        simp only [NatListCode.encode,Nat.add_one_le_iff,Nat.not_lt_zero,ite_false,bit,before_cons]
        by_cases hab : a = b
        · subst b; simp
        · by_cases hlt : a < b
          · simp [hlt,hab,Nat.le_of_lt hlt,Nat.not_le_of_gt hlt]
          · have hgt : b < a := by omega
            simp [hlt,hab,Nat.not_le_of_gt hgt]
      rw [heq] at h
      exact h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{LambdaKleeneBrouwer}
    \end{mathmeta}
    Define the closed binary comparison term by
    $$\LambdaKleeneBrouwer:=\LambdaListFold{\LambdaTermName{kbZero}}{\LambdaTermName{kbStep}}.$$
    A numerical-pair wrapper supplies its two arguments when a unary decision program is required.
-/
def compareTerm := listFold (numericalConstant 0) handler

theorem compareTerm_closed : compareTerm.Closed :=
  listFold_closed (numericalConstant_computes 0).1 handler_closed

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Kleene--Brouwer comparison program
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{LambdaKleeneBrouwer}
    \end{mathmeta}
    Define the closed binary comparison term by
    $$\LambdaKleeneBrouwer:=\LambdaListFold{\LambdaTermName{kbZero}}{\LambdaTermName{kbStep}}.$$
    A numerical-pair wrapper supplies its two arguments when a unary decision program is required.
-/
theorem compareTerm_apply (s t : List ℕ) : Relation.ReflTransGen Beta
    (app (app compareTerm (numeral (NatListCode.encode s))) (numeral (NatListCode.encode t)))
    (numeral (bit s t)) := by
  have h := listFold_apply (numericalConstant_computes 0).1 handler_closed value .refl
    (fun _ _ => .refl) s
  exact (beta_steps_app_left h _).trans (value_apply s t)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{LambdaKleeneBrouwer}
    \end{mathmeta}
    Define the closed binary comparison term by
    $$\LambdaKleeneBrouwer:=\LambdaListFold{\LambdaTermName{kbZero}}{\LambdaTermName{kbStep}}.$$
    A numerical-pair wrapper supplies its two arguments when a unary decision program is required.
-/
theorem compare_computes : NumericalComputes (uncurryNumerical compareTerm)
    (fun z => bit (NatListCode.decode z.unpair.1) (NatListCode.decode z.unpair.2)) := by
  apply uncurryNumerical_computes compareTerm_closed
    (fun i j => bit (NatListCode.decode i) (NatListCode.decode j))
  intro i j
  simpa only [NatListCode.encode_decode] using compareTerm_apply (NatListCode.decode i) (NatListCode.decode j)


local instance : Encodable (List ℕ) := NatListCode.encodable

/-- The list code is a bijection, so no invalid numerical codes need rejection. -/
noncomputable def presentation {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hw : WellFounded (strictTreeExtension T.tree)) : LambdaRelative.WellOrderPresentation ε where
  domain n := NatListCode.decode n ∈ T.tree
  relation i j := Before (NatListCode.decode i) (NatListCode.decode j)
  domain_decidable := T.decidable.precompNumerical (g := NatListCode.decode)
    numericalIdentity_computes (fun n => (NatListCode.encode_decode n).symm)
  relation_decidable := by
    refine ⟨_,compare_computes.uniform.1,fun z => ⟨?_,?_⟩⟩ <;> intro hz
    · simpa [Encodable.encode,Encodable.encodeSigma,bit,hz] using compare_computes.uniform.2 ε (Nat.pair z.1 z.2)
    · simpa [Encodable.encode,Encodable.encodeSigma,bit,hz] using compare_computes.uniform.2 ε (Nat.pair z.1 z.2)
  wellOrder := by
    let : IsWellOrder T.tree (fun s t => Before s.val t.val) :=
      { wf := wellFounded T.downward hw
        trichotomous := fun a b hab hba => Subtype.ext
          ((before_trichotomy a.val b.val).resolve_left hab |>.resolve_right hba) }
    let f : (fun i j : {n // NatListCode.decode n ∈ T.tree} =>
        Before (NatListCode.decode i.val) (NatListCode.decode j.val)) ↪r
        (fun s t : T.tree => Before s.val t.val) :=
      { toFun := fun i => ⟨NatListCode.decode i.val,i.property⟩
        inj' := by
          intro i j h
          apply Subtype.ext
          simpa using congrArg (fun s : T.tree => NatListCode.encode s.val) h
        map_rel_iff' := Iff.rfl }
    exact f.isWellOrder

/-- Coding the nodes preserves comparison in both directions. -/
noncomputable def presentationIso {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hw : WellFounded (strictTreeExtension T.tree)) :
    (fun s t : T.tree => Before s.val t.val) ≃r (presentation T hw).order where
  toFun s := ⟨NatListCode.encode s.val,by simpa only [presentation,NatListCode.decode_encode] using s.property⟩
  invFun i := ⟨NatListCode.decode i.val,i.property⟩
  left_inv s := Subtype.ext (NatListCode.decode_encode s.val)
  right_inv i := Subtype.ext (NatListCode.encode_decode i.val)
  map_rel_iff' := by
    intro s t
    change Before (NatListCode.decode (NatListCode.encode s.val))
      (NatListCode.decode (NatListCode.encode t.val)) ↔ Before s.val t.val
    simp

/-- The recursive order type bounds every node rank, at the original parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The comparison clauses give irreflexivity, transitivity, and trichotomy by induction on words. We prove
    well-foundedness by induction on strict extension in $T$. At a node $s$, the induction assertion is that
    every nonempty subset $A$ of its cone has a least element in the Kleene--Brouwer order. If $A$ contains
    no proper extension of $s$, its only element is $s$. Otherwise, choose the least $n$ such that the cone
    above $s\concat(n)$ meets $A$, where $s\concat(n)$ denotes appending $n$ to $s$. The child $s\concat(n)$ belongs to
    $T$ by closure under prefixes. The induction hypothesis gives a least element $m$ in that intersection.
    Every other member of $A$ is either $s$, lies above the same child, or lies above a child with larger
    index. In the first and third cases it follows after $m$; in the second it cannot precede $m$ by the
    choice of $m$. This proves the induction assertion. For a nonempty tree apply it at the empty word;
    the empty tree is immediate. The choices here prove well-foundedness and are not asserted to be
    computable from an arbitrary subset $A$.

    List encoding is a bijection with $\NN$, so the original membership program decides the domain of
    codes without any extra validity test. The comparison clauses give a total lambda program by recursion
    on the first word, as constructed in §{sec:lambda-kleene-brouwer}. This comparison makes no parameter
    queries. Consequently the coded order is a presentation at the original $\varepsilon$, and its order
    type $\alpha$ is below $\relativeChurchKleeneOrd{\varepsilon}$.

    Every strict extension precedes its prefix in this order. Induction on strict extension therefore
    bounds the rank of each node by its position in the well order: the successor of each child rank is
    at most the position of its parent, and taking their supremum preserves that inequality. Each such
    position is strictly below $\alpha$, proving the displayed bound. For a rooted tree apply it at the
    root. The constant-zero parameter gives the final assertion.
    \end{proof}
-/
theorem rank_lt_presentation {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hw : WellFounded (strictTreeExtension T.tree)) (s : T.tree) :
    (hw.apply s).rank < (presentation T hw).orderType := by
  let : WellFounded (strictTreeExtension T.tree) := hw
  let W := presentation T hw
  have hle := wellFoundedRank_le_of_relation_preserving
    (r := strictTreeExtension T.tree) (s := W.order) (presentationIso T hw)
    (fun _ _ h => (presentationIso T hw).map_rel_iff.mpr (extension_before h)) s
  rw [WellFounded.rank_eq_typein W.order] at hle
  exact hle.trans_lt (Ordinal.typein_lt_type W.order _)

theorem recursive_rank_bound {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hw : WellFounded (strictTreeExtension T.tree)) :
    (presentation T hw).orderType < LambdaRelative.recursiveOrdinalBound ε ∧
    ∀ s : T.tree, (hw.apply s).rank < (presentation T hw).orderType :=
  ⟨LambdaRelative.recursiveOrdinal_lt_bound ⟨presentation T hw,rfl⟩,rank_lt_presentation T hw⟩

theorem rank_lt_recursiveOrdinalBound {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hw : WellFounded (strictTreeExtension T.tree)) (s : T.tree) :
    (hw.apply s).rank < LambdaRelative.recursiveOrdinalBound ε :=
  (rank_lt_presentation T hw s).trans (recursive_rank_bound T hw).1


/-- Branch-based well-foundedness gives one recursive bound for all nodes. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Recursive bound for a well-founded tree
-/
theorem recursive_bound_of_no_branch {ε : ℕ → ℕ} (T : LambdaTree.PrefixTree ε)
    (hT : PrefixTreeWellFounded T.tree) :
    ∃ W : LambdaRelative.WellOrderPresentation ε,
      W.orderType < LambdaRelative.recursiveOrdinalBound ε ∧
      ∀ s : T.tree, ∃ hs : Acc (strictTreeExtension T.tree) s, hs.rank < W.orderType := by
  have hw := (prefixTreeWellFounded_iff T.tree T.downward).mp hT
  exact ⟨presentation T hw,(recursive_rank_bound T hw).1,
    fun s => ⟨hw.apply s,rank_lt_presentation T hw s⟩⟩

end KleeneBrouwer
end PolishSpaceBook
