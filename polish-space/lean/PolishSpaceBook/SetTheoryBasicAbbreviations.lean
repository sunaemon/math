module

public import PolishSpaceBook.SetTheorySeparation

@[expose] public section

/-! # Basic set abbreviations in arbitrary membership structures -/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {S : Type u} [membershipLanguage.Structure S]

/-- Inclusion is a pure formula abbreviation in the membership language. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $x \IncludedIn y \;:\equiv\; \forall z\,(z \in x \to z \in y)$ — pure first-order logic on $\in$.
-/
def subsetBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 0).imp (memberAt 2 1)).all

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $x \IncludedIn y \;:\equiv\; \forall z\,(z \in x \to z \in y)$ — pure first-order logic on $\in$.
-/
lemma realize_subsetBody (x y : S) :
    subsetBody.Realize Empty.elim ![x,y] ↔ ∀ z : S, member z x → member z y := by
  simp [subsetBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt]

/-- Extensionality turns a membership characterization into a unique set. -/
theorem existsUnique_of_members (hext : S ⊨ extensionalitySentence) (P : S → Prop)
    (hex : ∃ y : S, ∀ z : S, member z y ↔ P z) :
    ∃! y : S, ∀ z : S, member z y ↔ P z := by
  obtain ⟨y, hy⟩ := hex
  refine ⟨y, hy, ?_⟩
  intro x hx
  apply (models_extensionality_iff S).mp hext x y
  exact fun z => (hx z).trans (hy z).symm

/-- Infinity gives an empty object before Separation is used. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\emptyset$ — the unique $e$ with $\forall z\,(z \notin e)$, whose existence follows directly from the
        displayed Infinity axiom, before Separation is derived.
        Afterwards, Separation with $z \ne z$ gives another construction.
-/
theorem existsUnique_empty (hext : S ⊨ extensionalitySentence) (hinf : S ⊨ infinitySentence) :
    ∃! e : S, ∀ z : S, ¬member z e := by
  obtain ⟨e, he⟩ := (models_empty_iff S).mp (models_empty_of_infinity hinf)
  have h := existsUnique_of_members hext (fun _ => False) ⟨e, fun z => iff_false_intro (he z)⟩
  simpa only [iff_false] using h

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\{a, b\}$ — the unique $p$ with $\forall x\,(x \in p \leftrightarrow x = a \lor x = b)$, obtained by Pairing. The
        singleton is $\{a\} := \{a, a\}$, and finite sets $\{a_0,\ldots,a_n\}$ are defined by induction from Pairing and
        binary union.
-/
theorem existsUnique_pair (hext : S ⊨ extensionalitySentence) (hp : S ⊨ pairingSentence)
    (a b : S) : ∃! p : S, ∀ z : S, member z p ↔ z = a ∨ z = b :=
  existsUnique_of_members hext _ ((models_pairing_iff S).mp hp a b)

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\bigcup x$ — the unique $u$ with $\forall z\,(z \in u \leftrightarrow \exists y\,(z \in y \land y \in x))$,
        obtained by Union. The binary union is $x \cup y := \bigcup \{x, y\}$.
-/
theorem existsUnique_union (hext : S ⊨ extensionalitySentence) (hu : S ⊨ unionSentence)
    (x : S) : ∃! v : S, ∀ z : S, member z v ↔ ∃ y : S, member z y ∧ member y x :=
  existsUnique_of_members hext _ ((models_union_iff S).mp hu x)

/-- Binary intersection uses Separation on the first input. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $x \cap y$ — the unique $i$ with $\forall z\,(z \in i \leftrightarrow z \in x \land z \in y)$, obtained by the
        derived Separation schema applied to $x$.
-/
theorem existsUnique_intersection (hext : S ⊨ extensionalitySentence)
    (hs : S ⊨ separationSentence (memberAt (1 : Fin 2) 0)) (x y : S) :
    ∃! p : S, ∀ z : S, member z p ↔ member z x ∧ member z y := by
  obtain ⟨p, hp⟩ := (realize_separation S _).mp hs (fun _ => y) x
  apply existsUnique_of_members hext
  refine ⟨p, ?_⟩
  intro z
  simpa [realize_memberAt, Fin.snoc] using hp z

/-- Every member of the family contains the tested object. -/
def familyIntersectionBody : ForcingFormulas.Formula 2 :=
  ((memberAt (2 : Fin 3) 0).imp (memberAt 1 2)).all

lemma realize_familyIntersectionBody (family z : S) :
    familyIntersectionBody.Realize Empty.elim (Fin.snoc (fun _ : Fin 1 => family) z) ↔
      ∀ y : S, member y family → member z y := by
  simp [familyIntersectionBody, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt, Fin.snoc]

/-- For a nonempty family, separate inside one of its members. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\bigcap x$ — contextual notation for nonempty families: if $x \ne \emptyset$, it denotes the unique $i$ with
        $\forall z\,(z \in i \leftrightarrow \forall y \in x\, z \in y)$. To construct it, choose some $a \in x$ and apply
        the derived Separation schema to $a$. Thus $\bigcap x$ is used only for nonempty families unless an ambient universe
        is explicitly specified.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Contextual term notations**, such as the application $f(a)$ and the intersection $\bigcap x$ of a nonempty family:
        no total new function symbol is added when the notation is partial or convention-dependent. Instead the notation is
        unfolded *in context*: an atomic formula containing $f(a)$ is rewritten via $\langle a, \cdot\rangle \in f$, with
        quantifier scope determined by where $f(a)$ sits, as detailed below.
-/
theorem existsUnique_familyIntersection (hext : S ⊨ extensionalitySentence)
    (hs : S ⊨ separationSentence familyIntersectionBody) (family : S)
    (hne : ∃ a : S, member a family) :
    ∃! p : S, ∀ z : S, member z p ↔ ∀ y : S, member y family → member z y := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hp⟩ := (realize_separation S _).mp hs (fun _ => family) a
  apply existsUnique_of_members hext
  refine ⟨p, ?_⟩
  intro z
  have h : member z p ↔ member z a ∧ ∀ y : S, member y family → member z y := by
    simpa only [realize_familyIntersectionBody] using hp z
  exact h.trans ⟨And.right, fun hz => ⟨hz a ha, hz⟩⟩

/-- Once an ambient set is available, Separation with a false predicate gives the empty object. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\emptyset$ — the unique $e$ with $\forall z\,(z \notin e)$, whose existence follows directly from the
        displayed Infinity axiom, before Separation is derived.
        Afterwards, Separation with $z \ne z$ gives another construction.
-/
theorem existsUnique_empty_of_separation (hext : S ⊨ extensionalitySentence)
    (hs : S ⊨ separationSentence ((equalAt (0 : Fin 1) 0).not)) (x : S) :
    ∃! e : S, ∀ z : S, ¬member z e := by
  obtain ⟨e, he⟩ := (realize_separation S _).mp hs Fin.elim0 x
  have h : ∃! e : S, ∀ z : S, member z e ↔ False := by
    apply existsUnique_of_members hext
    refine ⟨e, ?_⟩
    intro z
    simpa [BoundedFormula.realize_not, realize_equalAt] using he z
  simpa only [iff_false] using h

/-- Binary union is the union of the pair of its inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\bigcup x$ — the unique $u$ with $\forall z\,(z \in u \leftrightarrow \exists y\,(z \in y \land y \in x))$,
        obtained by Union. The binary union is $x \cup y := \bigcup \{x, y\}$.
-/
theorem existsUnique_binaryUnion (hext : S ⊨ extensionalitySentence)
    (hp : S ⊨ pairingSentence) (hu : S ⊨ unionSentence) (x y : S) :
    ∃! v : S, ∀ z : S, member z v ↔ member z x ∨ member z y := by
  obtain ⟨p, hpair⟩ := (models_pairing_iff S).mp hp x y
  obtain ⟨v, hv⟩ := (models_union_iff S).mp hu p
  apply existsUnique_of_members hext
  refine ⟨v, ?_⟩
  intro z
  rw [hv z]
  constructor
  · rintro ⟨a, hza, hap⟩
    rcases (hpair a).mp hap with rfl | rfl
    · exact Or.inl hza
    · exact Or.inr hza
  · rintro (hz | hz)
    · exact ⟨x, hz, (hpair x).mpr (Or.inl rfl)⟩
    · exact ⟨y, hz, (hpair y).mpr (Or.inr rfl)⟩

/-- Inductively construct the set of entries of any finite list. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\{a, b\}$ — the unique $p$ with $\forall x\,(x \in p \leftrightarrow x = a \lor x = b)$, obtained by Pairing. The
        singleton is $\{a\} := \{a, a\}$, and finite sets $\{a_0,\ldots,a_n\}$ are defined by induction from Pairing and
        binary union.
-/
theorem existsUnique_finiteSet (hext : S ⊨ extensionalitySentence)
    (hinf : S ⊨ infinitySentence) (hp : S ⊨ pairingSentence) (hu : S ⊨ unionSentence)
    (xs : List S) : ∃! p : S, ∀ z : S, member z p ↔ z ∈ xs := by
  apply existsUnique_of_members hext
  induction xs with
  | nil =>
    obtain ⟨e, he, _⟩ := existsUnique_empty hext hinf
    exact ⟨e, fun z => by simpa using iff_false_intro (he z)⟩
  | cons a xs ih =>
    obtain ⟨p, hp'⟩ := ih
    obtain ⟨q, hq, _⟩ := existsUnique_pair hext hp a a
    obtain ⟨v, hv, _⟩ := existsUnique_binaryUnion hext hp hu q p
    refine ⟨v, ?_⟩
    intro z
    simpa only [hq z, or_self, hp' z, List.mem_cons] using hv z

/-- Kuratowski pairs are constructed by three applications of Pairing.
The witnesses are internal objects even in a nontransitive membership structure. -/
theorem exists_kuratowskiPair (hext : S ⊨ extensionalitySentence)
    (hp : S ⊨ pairingSentence) (a b : S) :
    ∃ singleton pair ordered : S,
      (∀ z : S, member z singleton ↔ z = a) ∧
      (∀ z : S, member z pair ↔ z = a ∨ z = b) ∧
      (∀ z : S, member z ordered ↔ z = singleton ∨ z = pair) := by
  obtain ⟨singleton, hs, _⟩ := existsUnique_pair hext hp a a
  obtain ⟨pair, hab, _⟩ := existsUnique_pair hext hp a b
  obtain ⟨ordered, ho, _⟩ := existsUnique_pair hext hp singleton pair
  exact ⟨singleton, pair, ordered, fun z => by simpa only [or_self] using hs z,
    hab, ho⟩

/-- The internal membership characterization of an unordered pair. -/
def IsUnorderedPair (p a b : S) : Prop :=
  ∀ z : S, member z p ↔ z = a ∨ z = b

/-- Kuratowski's construction, expressed using only the interpreted membership relation. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   Kuratowski's ordered pair $\langle a, b\rangle \;:=\; \{\{a\}, \{a, b\}\}$. A \termdefine{function graph} $f$ is a
        set of ordered pairs with $\langle a, b\rangle, \langle a, b'\rangle \in f \to b = b'$.
-/
def IsKuratowskiPair (q a b : S) : Prop :=
  ∃ singleton pair : S, IsUnorderedPair singleton a a ∧
    IsUnorderedPair pair a b ∧ IsUnorderedPair q singleton pair

lemma unorderedPair_unique (hext : S ⊨ extensionalitySentence)
    {p q a b : S} (hp : IsUnorderedPair p a b) (hq : IsUnorderedPair q a b) : p = q :=
  (models_extensionality_iff S).mp hext p q (fun z => (hp z).trans (hq z).symm)

/-- Extensionality makes all three witnesses in the Kuratowski construction unique. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   Kuratowski's ordered pair $\langle a, b\rangle \;:=\; \{\{a\}, \{a, b\}\}$. A \termdefine{function graph} $f$ is a
        set of ordered pairs with $\langle a, b\rangle, \langle a, b'\rangle \in f \to b = b'$.
-/
theorem existsUnique_kuratowskiPair (hext : S ⊨ extensionalitySentence)
    (hp : S ⊨ pairingSentence) (a b : S) : ∃! q : S, IsKuratowskiPair q a b := by
  obtain ⟨s, p, q, hs, hab, hq⟩ := exists_kuratowskiPair hext hp a b
  have hs' : IsUnorderedPair s a a := fun z => by simpa only [or_self] using hs z
  refine ⟨q, ⟨s, p, hs', hab, hq⟩, ?_⟩
  rintro q' ⟨s', p', hs'', hab', hq'⟩
  have hss : s' = s := unorderedPair_unique hext hs'' hs'
  have hpp : p' = p := unorderedPair_unique hext hab' hab
  subst s'
  subst p'
  exact unorderedPair_unique hext hq' hq

/-- Application is pair membership, with no total function symbol added to the language. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
def GraphApplication (f a b : S) : Prop :=
  ∃ q : S, IsKuratowskiPair q a b ∧ member q f

/-- A graph consists of ordered pairs and is single-valued on its domain. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   Kuratowski's ordered pair $\langle a, b\rangle \;:=\; \{\{a\}, \{a, b\}\}$. A \termdefine{function graph} $f$ is a
        set of ordered pairs with $\langle a, b\rangle, \langle a, b'\rangle \in f \to b = b'$.
-/
def IsFunctionGraph (f : S) : Prop :=
  (∀ q : S, member q f → ∃ a b : S, IsKuratowskiPair q a b) ∧
    ∀ a b c : S, GraphApplication f a b → GraphApplication f a c → b = c

/-- A graph has a unique value exactly at the inputs for which a pair occurs. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   **Contextual term notations**, such as the application $f(a)$ and the intersection $\bigcap x$ of a nonempty family:
        no total new function symbol is added when the notation is partial or convention-dependent. Instead the notation is
        unfolded *in context*: an atomic formula containing $f(a)$ is rewritten via $\langle a, \cdot\rangle \in f$, with
        quantifier scope determined by where $f(a)$ sits, as detailed below.
-/
theorem graphApplication_existsUnique {f a : S} (hf : IsFunctionGraph f)
    (ha : ∃ b : S, GraphApplication f a b) : ∃! b : S, GraphApplication f a b := by
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, hb, fun c hc => hf.2 a c b hc hb⟩

/-- Both coordinates of an internal ordered pair belong to the double union of its graph.
No transitivity or external interpretation of model elements is used. -/
theorem coordinates_mem_doubleUnion {f a b u v : S}
    (hu : ∀ z : S, member z u ↔ ∃ y : S, member z y ∧ member y f)
    (hv : ∀ z : S, member z v ↔ ∃ y : S, member z y ∧ member y u)
    (hab : GraphApplication f a b) : member a v ∧ member b v := by
  obtain ⟨q, ⟨s, p, hs, hp, hq⟩, hqf⟩ := hab
  have hpu : member p u := (hu p).mpr ⟨q, (hq p).mpr (Or.inr rfl), hqf⟩
  exact ⟨(hv a).mpr ⟨p, (hp a).mpr (Or.inl rfl), hpu⟩,
    (hv b).mpr ⟨p, (hp b).mpr (Or.inr rfl), hpu⟩⟩

/-- The bounded expansion of application-membership is valid even before assuming
single-valuedness; for a function graph it tests membership of its unique value. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $f(a) = b \;:\equiv\; \langle a, b\rangle \in f$ — application as ordered-pair membership. This is a contextual
        notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
        graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\langle
        a,b\rangle\in f$ and $\exists v \in \bigcup\bigcup f\,(\langle a,v\rangle\in f \land v\in y)$ respectively, so the
        displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
        function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
        contexts with negations or repeated occurrences, unfold application before applying logical connectives.
-/
theorem graphApplication_member_bounded {f a y u v : S}
    (hu : ∀ z : S, member z u ↔ ∃ w : S, member z w ∧ member w f)
    (hv : ∀ z : S, member z v ↔ ∃ w : S, member z w ∧ member w u) :
    (∃ b : S, GraphApplication f a b ∧ member b y) ↔
      ∃ b : S, member b v ∧ GraphApplication f a b ∧ member b y := by
  constructor
  · rintro ⟨b, hab, hby⟩
    exact ⟨b, (coordinates_mem_doubleUnion hu hv hab).2, hab, hby⟩
  · rintro ⟨b, _, hab, hby⟩
    exact ⟨b, hab, hby⟩

/-- Pure membership syntax for an internal unordered pair. -/
def internalPairFormula {n : ℕ} (p a b : Fin n) : ForcingFormulas.Formula n :=
  ((memberAt (Fin.last n) p.castSucc).iff
    (equalAt (Fin.last n) a.castSucc ⊔ equalAt (Fin.last n) b.castSucc)).all

lemma realize_internalPairFormula {n : ℕ} (p a b : Fin n) (xs : Fin n → S) :
    (internalPairFormula p a b).Realize Empty.elim xs ↔
      IsUnorderedPair (xs p) (xs a) (xs b) := by
  simp only [internalPairFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_sup, realize_memberAt, realize_equalAt,
    Fin.snoc_last, Fin.snoc_castSucc, IsUnorderedPair]

/-- The Kuratowski construction as a formula in the original membership language. -/
def internalKuratowskiFormula {n : ℕ} (q a b : Fin n) : ForcingFormulas.Formula n :=
  ((internalPairFormula (Fin.last n).castSucc a.castSucc.castSucc a.castSucc.castSucc ⊓
    internalPairFormula (Fin.last (n + 1)) a.castSucc.castSucc b.castSucc.castSucc ⊓
    internalPairFormula q.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n + 1))).ex).ex

lemma realize_internalKuratowskiFormula {n : ℕ} (q a b : Fin n) (xs : Fin n → S) :
    (internalKuratowskiFormula q a b).Realize Empty.elim xs ↔
      IsKuratowskiPair (xs q) (xs a) (xs b) := by
  simp only [internalKuratowskiFormula, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, realize_internalPairFormula,
    Fin.snoc_last, Fin.snoc_castSucc, IsKuratowskiPair, and_assoc]

/-- Application as an atomic contextual abbreviation, not an extra function symbol. -/
def internalApplicationFormula {n : ℕ} (f a b : Fin n) : ForcingFormulas.Formula n :=
  (internalKuratowskiFormula (Fin.last n) a.castSucc b.castSucc ⊓
    memberAt (Fin.last n) f.castSucc).ex

lemma realize_internalApplicationFormula {n : ℕ} (f a b : Fin n) (xs : Fin n → S) :
    (internalApplicationFormula f a b).Realize Empty.elim xs ↔
      GraphApplication (xs f) (xs a) (xs b) := by
  simp only [internalApplicationFormula, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, realize_internalKuratowskiFormula, realize_memberAt,
    Fin.snoc_last, Fin.snoc_castSucc, GraphApplication]

/-- The defining predicate for the domain, with the graph retained as a parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\mathrm{dom}\, f \;:=\; \{a : \exists b\,\langle a, b\rangle \in f\}$, obtained by the derived Separation schema on
        $\bigcup \bigcup f$.
-/
def internalDomainBody : ForcingFormulas.Formula 2 :=
  (internalApplicationFormula (0 : Fin 3) 1 2).ex

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\mathrm{dom}\, f \;:=\; \{a : \exists b\,\langle a, b\rangle \in f\}$, obtained by the derived Separation schema on
        $\bigcup \bigcup f$.
-/
lemma realize_internalDomainBody (f a : S) :
    internalDomainBody.Realize Empty.elim (Fin.snoc (fun _ : Fin 1 => f) a) ↔
      ∃ b : S, GraphApplication f a b := by
  simp [internalDomainBody, BoundedFormula.realize_ex,
    realize_internalApplicationFormula, Fin.snoc]

/-- Separation on the double union constructs the domain in an arbitrary model. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\mathrm{dom}\, f \;:=\; \{a : \exists b\,\langle a, b\rangle \in f\}$, obtained by the derived Separation schema on
        $\bigcup \bigcup f$.
-/
theorem existsUnique_graphDomain (hext : S ⊨ extensionalitySentence)
    (hu : S ⊨ unionSentence) (hs : S ⊨ separationSentence internalDomainBody) (f : S) :
    ∃! d : S, ∀ a : S, member a d ↔ ∃ b : S, GraphApplication f a b := by
  obtain ⟨u, huf, _⟩ := existsUnique_union hext hu f
  obtain ⟨v, hvu, _⟩ := existsUnique_union hext hu u
  obtain ⟨d, hd⟩ := (realize_separation S internalDomainBody).mp hs (fun _ => f) v
  apply existsUnique_of_members hext
  refine ⟨d, ?_⟩
  intro a
  have ha := hd a
  rw [realize_internalDomainBody] at ha
  exact ha.trans ⟨And.right, fun ⟨b, hab⟩ =>
    ⟨(coordinates_mem_doubleUnion huf hvu hab).1, b, hab⟩⟩

/-- Russell's argument uses Separation alone, rather than Foundation or transitivity. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    That $V$ and $\mathrm{Ord}$ are not sets is the \termdefine{Russell paradox} and \termdefine{Burali-Forti paradox}
    respectively.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $V := \{x : x = x\}$, the universe of all sets.
    *   $\mathrm{Ord} := \{x : \mathrm{Ord}(x)\}$, the class of ordinals.
    *   $\mathrm{Card}$, the class of cardinals.
-/
theorem no_universal_set_of_separation
    (hs : S ⊨ separationSentence ((memberAt (0 : Fin 1) 0).not)) :
    ¬ ∃ v : S, ∀ z : S, member z v := by
  rintro ⟨v, hv⟩
  obtain ⟨r, hr⟩ := (realize_separation S _).mp hs (fun i => Fin.elim0 i) v
  have hrr : member r r ↔ ¬member r r := by
    simpa [BoundedFormula.realize_not, realize_memberAt, Fin.snoc, hv r] using hr r
  have hn : ¬member r r := fun h => (hrr.mp h) h
  exact hn (hrr.mpr hn)

end PolishSpaceBook.SetTheoryModels.AbstractMembership
