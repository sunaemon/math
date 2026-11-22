module

public import PolishSpaceBook.FirstOrderEqualityTemplates

@[expose] public section

/-! # Lambda programs enumerating equality-template candidates

The enumeration uses numerical lists and structural syntax recursion. Cartesian
products of child candidates are constructed by a list fold and actual maps;
there is no unbounded search over possible predicate templates.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false

namespace TemplatePrograms

private theorem appCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem lamCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

/-- Apply the syntax application constructor to a fixed left child and a list of right children. -/
def mapApplicationTerm : AlphaTerm := lam 42
  (app listMapTerm (app applicationCodeTerm (var 42)))

theorem mapApplicationTerm_closed : mapApplicationTerm.Closed := by
  unfold mapApplicationTerm Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [listMapTerm_closed, appCode_closed]
  simp

theorem mapApplicationTerm_apply (a e : ℕ) : Relation.ReflTransGen Beta
    (app (app mapApplicationTerm (numeral a)) (numeral e))
    (numeral (NatListCode.encode ((NatListCode.decode e).map (fun b => 3 * Nat.pair a b + 1)))) := by
  have hs : Beta (app mapApplicationTerm (numeral a))
      (app listMapTerm (app applicationCodeTerm (numeral a))) := by
    simpa only [mapApplicationTerm, subst_app, subst_var, ↓reduceIte,
      subst_closed _ _ _ listMapTerm_closed, subst_closed _ _ _ appCode_closed] using
      Beta.contract 42 (app listMapTerm (app applicationCodeTerm (var 42))) (numeral a)
  exact (Relation.ReflTransGen.single (.app_left _ hs)).trans
    (listMapTerm_apply (closed_app appCode_closed (numeral_closed a)) _
      (taggedPairCodeTerm_apply 1 a) e)

namespace Program
open Grammar

def binary (B : AlphaTerm) (b : ℕ → ℕ → ℕ) (hc : B.Closed)
    (hb : ∀ i j, Relation.ReflTransGen Beta (app (app B (numeral i)) (numeral j)) (numeral (b i j)))
    (p q : Program) : Program :=
  ⟨numericalCombine B p.term q.term, fun n => b (p.value n) (q.value n),
    p.computes.combine q.computes hc b hb⟩

def mapApplication (a e : Program) : Program := binary mapApplicationTerm
  (fun a e => NatListCode.encode ((NatListCode.decode e).map (fun b => 3 * Nat.pair a b + 1)))
  mapApplicationTerm_closed mapApplicationTerm_apply a e

def append (a b : Program) : Program := binary listAppendTerm
  (fun a b => NatListCode.encode (NatListCode.decode a ++ NatListCode.decode b))
  listAppendTerm_closed listAppendTerm_apply a b

end Program

/-- Input is `(right-list,(left-child,accumulator))`. -/
def crossStep : Grammar.Program :=
  let right := Grammar.Program.ident.first
  let left := Grammar.Program.ident.second.first
  let acc := Grammar.Program.ident.second.second
  Program.append (Program.mapApplication left right) acc

/-- First argument is the right list, second argument is the left list. -/
def crossTerm : AlphaTerm := lam 43
  (app (app listRecursorTerm (app (curryThird crossStep.term) (var 43))) (numeral 0))

theorem crossTerm_closed : crossTerm.Closed := by
  unfold crossTerm Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [listRecursorTerm_closed, curryThird_closed crossStep.computes.1, numeral_closed]
  simp

theorem crossTerm_code (xs ys : List ℕ) : Relation.ReflTransGen Beta
    (app (app crossTerm (numeral (NatListCode.encode ys))) (numeral (NatListCode.encode xs)))
    (numeral (NatListCode.encode (xs.flatMap (fun a => ys.map (fun b => 3 * Nat.pair a b + 1))))) := by
  let H := app (curryThird crossStep.term) (numeral (NatListCode.encode ys))
  have hH : H.Closed := closed_app (curryThird_closed crossStep.computes.1) (numeral_closed _)
  have hs : Beta (app crossTerm (numeral (NatListCode.encode ys)))
      (app (app listRecursorTerm H) (numeral 0)) := by
    simpa only [crossTerm, H, subst_app, subst_var, ↓reduceIte,
      subst_closed _ _ _ listRecursorTerm_closed,
      subst_closed _ _ _ (curryThird_closed crossStep.computes.1),
      subst_closed _ _ _ (numeral_closed 0)] using
      Beta.contract 43 (app (app listRecursorTerm (app (curryThird crossStep.term) (var 43)))
        (numeral 0)) (numeral (NatListCode.encode ys))
  apply (Relation.ReflTransGen.single (.app_left _ hs)).trans
  apply listRecursorTerm_apply hH (numeral_closed 0)
    (fun xs => numeral (NatListCode.encode (xs.flatMap (fun a => ys.map (fun b => 3 * Nat.pair a b + 1))))) .refl
  intro a xs
  apply (curryThird_apply crossStep.computes.1 _ _ _).trans
  have h := crossStep.computes.2 (Nat.pair (NatListCode.encode ys)
    (Nat.pair a (NatListCode.encode (xs.flatMap (fun a => ys.map (fun b => 3 * Nat.pair a b + 1))))))
  simpa only [crossStep, Program.append, Program.mapApplication, Program.binary,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, id_eq,
    Nat.unpair_pair, NatListCode.decode_encode, List.flatMap_cons] using h

theorem crossTerm_apply (e d : ℕ) : Relation.ReflTransGen Beta
    (app (app crossTerm (numeral d)) (numeral e))
    (numeral (NatListCode.encode ((NatListCode.decode e).flatMap
      (fun a => (NatListCode.decode d).map (fun b => 3 * Nat.pair a b + 1))))) := by
  simpa only [NatListCode.encode_decode] using crossTerm_code (NatListCode.decode e) (NatListCode.decode d)


namespace Program
open Grammar

def cons (a b : Program) : Program := binary listConsTerm
  (fun a b => Nat.pair a b + 1) listConsTerm_closed listConsTerm_apply a b

end Program

def variableCandidates (x t z : ℕ) : List ℕ :=
  if x = 2 * t then [(Term.var x).code, (Term.var (2 * z)).code] else [(Term.var x).code]

/-- Input is `(leaf-name,(source-name,distinguished-name))`. -/
def variableProgram : Grammar.Program :=
  let x := Grammar.Program.ident.first
  let t := Grammar.Program.ident.second.first
  let z := Grammar.Program.ident.second.second
  let c := x.varCode
  (x.equal ((Grammar.Program.const 2).mul t)).ifZero
    (Program.cons c (Grammar.Program.const 0))
    (Program.cons c (Program.cons (((Grammar.Program.const 2).mul z).varCode)
      (Grammar.Program.const 0)))

theorem variableProgram_value (x t z : ℕ) :
    variableProgram.value (Nat.pair x (Nat.pair t z)) = NatListCode.encode (variableCandidates x t z) := by
  simp only [variableProgram, Grammar.Program.ifZero, Grammar.Program.equal, Grammar.Program.mul,
    Grammar.Program.first, Grammar.Program.second, Grammar.Program.ident, Grammar.Program.const,
    Grammar.Program.varCode, Program.cons, Program.binary, id_eq, Nat.unpair_pair,
    variableCandidates]
  by_cases h : x = 2 * t <;> simp [h, NatListCode.encode]

/-- Lift cartesian product to two parameterized list functions. -/
def applicationHandler : AlphaTerm := lam 43 (lam 44
  (numericalCombine crossTerm (var 44) (var 43)))

theorem applicationHandler_closed : applicationHandler.Closed := by
  unfold applicationHandler numericalCombine Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [crossTerm_closed]
  decide

theorem applicationHandler_start {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed) :
    Relation.ReflTransGen Beta (app (app applicationHandler F) G)
      (numericalCombine crossTerm G F) := by
  have hs : Beta (app applicationHandler F) (lam 44 (numericalCombine crossTerm (var 44) F)) := by
    convert Beta.contract 43 (lam 44 (numericalCombine crossTerm (var 44) (var 43))) F using 1 <;> try rfl
    simp only [subst_lam_fresh _ _ 44 43 (by decide) (by rw [hF]; simp), numericalCombine,
      subst_lam_fresh _ _ 40 43 (by decide) (by rw [hF]; simp), subst_app, subst_var,
      subst_closed _ _ _ crossTerm_closed]
    simp
  have ht : Beta (app (lam 44 (numericalCombine crossTerm (var 44) F)) G)
      (numericalCombine crossTerm G F) := by
    convert Beta.contract 44 (numericalCombine crossTerm (var 44) F) G using 1
    simp only [numericalCombine, subst_lam_fresh _ _ 40 44 (by decide) (by rw [hG]; simp),
      subst_app, subst_var, subst_closed _ _ _ crossTerm_closed, subst_closed _ _ _ hF]
    simp
  exact .tail (.single (.app_left _ hs)) ht

/-- Map the original abstraction constructor over the body candidates. -/
def abstractionHandler : AlphaTerm := lam 43 (lam 44
  (numericalCompose (app listMapTerm (app abstractionCodeTerm (var 43))) (var 44)))

theorem abstractionHandler_closed : abstractionHandler.Closed := by
  unfold abstractionHandler numericalCompose Closed
  simp only [fv_lam, fv_app, fv_var]
  rw [listMapTerm_closed, lamCode_closed]
  decide

theorem abstractionHandler_start (x : ℕ) {F : AlphaTerm} (hF : F.Closed) :
    Relation.ReflTransGen Beta (app (app abstractionHandler (numeral x)) F)
      (numericalCompose (app listMapTerm (app abstractionCodeTerm (numeral x))) F) := by
  have hs : Beta (app abstractionHandler (numeral x))
      (lam 44 (numericalCompose (app listMapTerm (app abstractionCodeTerm (numeral x))) (var 44))) := by
    convert Beta.contract 43 (lam 44
      (numericalCompose (app listMapTerm (app abstractionCodeTerm (var 43))) (var 44))) (numeral x) using 1 <;> try rfl
    simp only [subst_lam_fresh _ _ 44 43 (by decide) (by rw [numeral_closed x]; simp), numericalCompose,
      subst_lam_fresh _ _ 40 43 (by decide) (by rw [numeral_closed x]; simp), subst_app, subst_var,
      subst_closed _ _ _ listMapTerm_closed, subst_closed _ _ _ lamCode_closed]
    simp
  have ht : Beta (app (lam 44
      (numericalCompose (app listMapTerm (app abstractionCodeTerm (numeral x))) (var 44))) F)
      (numericalCompose (app listMapTerm (app abstractionCodeTerm (numeral x))) F) := by
    convert Beta.contract 44
      (numericalCompose (app listMapTerm (app abstractionCodeTerm (numeral x))) (var 44)) F using 1
    simp only [numericalCompose, subst_lam_fresh _ _ 40 44 (by decide) (by rw [hF]; simp),
      subst_app, subst_var, subst_closed _ _ _ listMapTerm_closed,
      subst_closed _ _ _ lamCode_closed, subst_closed _ _ _ (numeral_closed x)]
    simp
  exact .tail (.single (.app_left _ hs)) ht

/-- The structurally finite procedure also has a meaning on malformed data. -/
def variants (t z : ℕ) : LTerm → List LTerm
  | .var x => if x = 2 * t then [.var x, .var (2 * z)] else [.var x]
  | .app A B => (variants t z A).flatMap (fun C => (variants t z B).map (.app C))
  | .lam x A => (variants t z A).map (.lam x)

def functionValue : LTerm → AlphaTerm
  | .var x => app (curryNumerical variableProgram.term) (numeral x)
  | .app A B => app (app applicationHandler (functionValue A)) (functionValue B)
  | .lam x A => app (app abstractionHandler (numeral x)) (functionValue A)

theorem functionValue_closed (M : LTerm) : (functionValue M).Closed := by
  induction M with
  | var x => exact closed_app (curryNumerical_closed variableProgram.computes.1) (numeral_closed x)
  | app A B ihA ihB => exact closed_app (closed_app applicationHandler_closed ihA) ihB
  | lam x A ih => exact closed_app (closed_app abstractionHandler_closed (numeral_closed x)) ih

theorem functionValue_apply (M : LTerm) (t z : ℕ) : Relation.ReflTransGen Beta
    (app (functionValue M) (numeral (Nat.pair t z)))
    (numeral (NatListCode.encode ((variants t z M).map Term.code))) := by
  induction M generalizing t z with
  | var x =>
    apply (curryNumerical_apply variableProgram.computes.1 x (Nat.pair t z)).trans
    have h := variableProgram.computes.2 (Nat.pair x (Nat.pair t z))
    rw [variableProgram_value] at h
    by_cases hx : x = 2 * t <;> simpa only [variants, variableCandidates, hx, ↓reduceIte, List.map_cons, List.map_nil] using h
  | app A B ihA ihB =>
    apply (beta_steps_app_left
      (applicationHandler_start (functionValue_closed A) (functionValue_closed B)) _).trans
    have hA : NumericalComputes (functionValue A)
        (fun p => NatListCode.encode ((variants p.unpair.1 p.unpair.2 A).map Term.code)) :=
      ⟨functionValue_closed A, fun p => by simpa only [Nat.pair_unpair] using ihA p.unpair.1 p.unpair.2⟩
    have hB : NumericalComputes (functionValue B)
        (fun p => NatListCode.encode ((variants p.unpair.1 p.unpair.2 B).map Term.code)) :=
      ⟨functionValue_closed B, fun p => by simpa only [Nat.pair_unpair] using ihB p.unpair.1 p.unpair.2⟩
    have h := (hB.combine hA crossTerm_closed
      (fun d e => NatListCode.encode ((NatListCode.decode e).flatMap
        (fun a => (NatListCode.decode d).map (fun b => 3 * Nat.pair a b + 1))))
      (fun d e => crossTerm_apply e d)).2 (Nat.pair t z)
    simpa only [Nat.unpair_pair, NatListCode.decode_encode, variants, List.map_flatMap,
      List.flatMap_map, List.map_map, Function.comp_def, Term.code] using h
  | lam x A ih =>
    apply (beta_steps_app_left (abstractionHandler_start x (functionValue_closed A)) _).trans
    have hMap : NumericalComputes (app listMapTerm (app abstractionCodeTerm (numeral x)))
        (fun e => NatListCode.encode ((NatListCode.decode e).map (fun a => 3 * Nat.pair x a + 2))) :=
      ⟨closed_app listMapTerm_closed (closed_app lamCode_closed (numeral_closed x)),
        listMapTerm_apply (closed_app lamCode_closed (numeral_closed x)) _ (taggedPairCodeTerm_apply 2 x)⟩
    have hA : NumericalComputes (functionValue A)
        (fun p => NatListCode.encode ((variants p.unpair.1 p.unpair.2 A).map Term.code)) :=
      ⟨functionValue_closed A, fun p => by simpa only [Nat.pair_unpair] using ih p.unpair.1 p.unpair.2⟩
    simpa only [Nat.unpair_pair, NatListCode.decode_encode, variants, List.map_map,
      Function.comp_def, Term.code] using (hMap.comp hA).2 (Nat.pair t z)

/-- Input syntax code, then the pair of source and distinguished variable names. -/
def candidatesTerm : AlphaTerm := syntaxFold (curryNumerical variableProgram.term)
  applicationHandler abstractionHandler

theorem candidatesTerm_closed : candidatesTerm.Closed := syntaxFold_closed
  (curryNumerical_closed variableProgram.computes.1) applicationHandler_closed abstractionHandler_closed

theorem candidatesTerm_code (M : LTerm) (t z : ℕ) : Relation.ReflTransGen Beta
    (app (app candidatesTerm (numeral M.code)) (numeral (Nat.pair t z)))
    (numeral (NatListCode.encode ((variants t z M).map Term.code))) := by
  have hf := syntaxFold_apply (curryNumerical_closed variableProgram.computes.1)
    applicationHandler_closed abstractionHandler_closed functionValue
    (fun _ => .refl) (fun _ _ => .refl) (fun _ _ => .refl) M
  exact (beta_steps_app_left hf _).trans (functionValue_apply M t z)

theorem candidatesTerm_apply (n t z : ℕ) : Relation.ReflTransGen Beta
    (app (app candidatesTerm (numeral n)) (numeral (Nat.pair t z)))
    (numeral (NatListCode.encode ((variants t z (Term.decode n)).map Term.code))) := by
  simpa only [Term.code_decode] using candidatesTerm_code (Term.decode n) t z

theorem variants_dataTerm (A : BindingTree) (t z : ℕ) :
    variants t z A.dataTerm = (BindingTree.templates t z A).map BindingTree.dataTerm := by
  induction A with
  | free v =>
    have hv : 2 * v = 2 * t ↔ v = t := by omega
    by_cases h : v = t <;> simp [BindingTree.dataTerm, BindingTree.templates, variants, hv, h]
  | bound i =>
    have hi : 2 * i + 1 ≠ 2 * t := by omega
    simp [BindingTree.dataTerm, BindingTree.templates, variants, hi]
  | app A B ihA ihB =>
    simp only [BindingTree.dataTerm, variants, BindingTree.templates, ihA, ihB,
      List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  | lam A ih => simp [BindingTree.dataTerm, variants, BindingTree.templates, ih, List.map_map]

/-- The actual lambda enumerator computes the finite list used by the proved
unannotated equality-template equivalence. -/
theorem candidatesTerm_tree (A : BindingTree) (t z : ℕ) : Relation.ReflTransGen Beta
    (app (app candidatesTerm (numeral A.code)) (numeral (Nat.pair t z)))
    (numeral (NatListCode.encode ((BindingTree.templates t z A).map BindingTree.code))) := by
  have h := candidatesTerm_code A.dataTerm t z
  rw [variants_dataTerm, List.map_map] at h
  exact h

end TemplatePrograms
end PolishSpaceBook.FirstOrderLambdaEncoding
