module

public import PolishSpaceBook.WellFoundedRankBounds
public import PolishSpaceBook.BorelExpressionBoolean

@[expose] public section

/-! # Explicit Borel expressions for bounded accessible-node ranks

For a countable relation whose edges have Borel codes, recursion over a
well-founded countable bound constructs the code of each rank layer. This is
an external recursion. Its finite label interpreter is a separate computational
obligation, and no computable choice of a rank bound is asserted here.
-/
namespace PolishSpaceBook
open Set
namespace RankBound
open BorelExpression

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    To turn the recursion into an expression, use the following derived constructors:
    \begin{mathmeta}
      \define{BorelEmptyCode,BorelIntersectionCode,BorelBinaryUnionCode,RankLayerCode}
    \end{mathmeta}
    $$\begin{aligned}
    \BorelEmptyCode&:=\BorelComplementCode{\BorelLeafCode{0}},\\
    \BorelIntersectionCode{\Sequence{d_i}{i\in\omega}}&:=
     \BorelComplementCode{\BorelUnionCode{\Sequence{\BorelComplementCode{d_i}}{i\in\omega}}},\\
    \BorelBinaryUnionCode{c}{d}&:=\BorelUnionCode{\Sequence{f_i}{i\in\omega}},\qquad
     f_i:=\begin{cases}c&i=0,\\d&i>0.\end{cases}
    \end{aligned}$$
    Their values are the empty set, the countable intersection, and the binary union, respectively.
    Define $\RankLayerCode{a}{s}$ by well-founded recursion on $R$:
    $$\begin{aligned}
    d_{a,t,b}&:=\begin{cases}\RankLayerCode{b}{t}&R(b,a),\\
                             \BorelEmptyCode&\neg R(b,a),\end{cases}\\
    \RankLayerCode{a}{s}&:=\BorelIntersectionCode{
      \Sequence{\BorelBinaryUnionCode{\BorelComplementCode{e_{t,s}}}
         {\BorelUnionCode{\Sequence{d_{a,t,b}}{b\in\omega}}}}{t\in\omega}}.
    \end{aligned}$$
    Every union constructor still has children. When there is no lower bound $b$, the relevant children
    all carry the empty-set expression; they are not removed from the syntax.
-/
noncomputable def codeStep (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop)
    (a : ℕ) (rec : ∀ b, R b a → ℕ → Code) (s : ℕ) : Code := by
  classical
  exact Code.iInter (fun t => (E t s).compl.sup
    (Code.iUnion (fun b => if h : R b a then rec b h t else Code.empty)))

noncomputable def code (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R)
    (a s : ℕ) : Code := hR.fix (codeStep E R) a s

theorem code_eq (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R) (a s : ℕ) :
    code E R hR a s = codeStep E R a (fun b _ => code E R hR b) s := by
  exact congrFun (hR.fix_eq (codeStep E R) a) s

theorem value_code {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ)
    (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R) (a s : ℕ) :
    (code E R hR a s).value U =
      ⋂ t, ((E t s).value U)ᶜ ∪ ⋃ b, ⋃ (_ : R b a), (code E R hR b t).value U := by
  classical
  rw [code_eq]
  simp only [codeStep,Code.value_iInter,Code.value_sup,Code.value_compl,Code.value_iUnion]
  apply iInter_congr
  intro t
  congr 1
  apply iUnion_congr
  intro b
  by_cases h : R b a <;> simp [h,Code.value_empty U hU]

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Use well-founded induction on $a$, simultaneously for all $s$. The recursive calls are only to
    $b$ with $R(b,a)$. Their expressions are valid by induction; the other branches use the valid
    empty-set expression. The constructors therefore give a valid expression at $a,s$.
    Their interpretation equations and the induction hypothesis identify its value with the right-hand
    side of the bounded-rank recursion lemma, and hence with $\RankLayer{a}{s}$.
    Finally every valid expression has a Borel value.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The rank bound in §{sec:edst-boundedness} becomes useful only after its initial segments have explicit
    Borel expressions. We describe that construction for a countable relation. Fix a well-founded relation
    $R$ on $\NN$ and write $r(a)$ for the rank of $a$ in $R$. Let $E_x$ be a relation on $\NN$ depending on
    $x\in\BaireSpace$. For each $t,s$, suppose a valid expression $e_{t,s}$ represents
    $$E_{t,s}:=\{x:E_x(t,s)\}.$$
    The direction of both relations is downward: $R(b,a)$ says that $b$ is below $a$, and $E_x(t,s)$ says
    that $t$ is below $s$. The relations $E_x$ need not be well founded.
-/
theorem mem_value_code_iff {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ)
    (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R) (a s : ℕ) (x : X) :
    x ∈ (code E R hR a s).value U ↔ Holds R hR (fun t s => x ∈ (E t s).value U) a s := by
  classical
  induction a using hR.induction generalizing s with
  | h a ih =>
    rw [value_code U hU E R hR a s,iff_children]
    simp only [mem_iInter,mem_union,mem_compl_iff,mem_iUnion]
    constructor
    · intro h t ht
      rcases h t with hn | ⟨b,hr,hb⟩
      · exact False.elim (hn ht)
      · exact ⟨b,hr,(ih b hr t).mp hb⟩
    · intro h t
      by_cases ht : x ∈ (E t s).value U
      · obtain ⟨b,hr,hb⟩ := h t ht
        exact Or.inr ⟨b,hr,(ih b hr t).mpr hb⟩
      · exact Or.inl ht

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Borel expressions for rank layers
  excerpt: |
    Each $\RankLayerCode{a}{s}$ is valid and
    $$\BorelValue{\RankLayerCode{a}{s}}=\RankLayer{a}{s}.$$
    In particular every such rank layer is Borel.
-/
theorem code_rank_layer {X : Type*} (U : ℕ → Set X) (hU : U 0 = univ)
    (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R) (a s : ℕ) :
    (code E R hR a s).value U =
      {x | Holds R hR (fun t s => x ∈ (E t s).value U) a s} := by
  ext x
  exact mem_value_code_iff U hU E R hR a s x

theorem measurableSet_rank_layer {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (hU : U 0 = univ) (hMeas : ∀ n, MeasurableSet (U n))
    (E : ℕ → ℕ → Code) (R : ℕ → ℕ → Prop) (hR : WellFounded R) (a s : ℕ) :
    MeasurableSet {x | Holds R hR (fun t s => x ∈ (E t s).value U) a s} := by
  rw [← code_rank_layer U hU E R hR a s]
  exact (code E R hR a s).val.measurableSet_evaluate
    (code E R hR a s).property.2.2.2.2.2 U hMeas []

end RankBound
end PolishSpaceBook
