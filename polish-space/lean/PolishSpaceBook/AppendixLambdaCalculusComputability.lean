module

public import PolishSpaceBook.AppendixLogic
public import PolishSpaceBook.LambdaNumericalProjections
public import PolishSpaceBook.LambdaOracleRecursion
public import PolishSpaceBook.LambdaReductionCertificates
public import PolishSpaceBook.LambdaSyntaxInspection
public import PolishSpaceBook.LambdaSyntaxRecursion
public import PolishSpaceBook.LambdaFreshVariables
public import PolishSpaceBook.LambdaCodeSubstitution
public import PolishSpaceBook.LambdaBindingCodes
public import PolishSpaceBook.LambdaFiniteLists
public import PolishSpaceBook.LambdaBetaSuccessors
public import PolishSpaceBook.LambdaCertificateChecker
public import PolishSpaceBook.LambdaProgramCodes
public import PolishSpaceBook.LambdaProgramSpecialization
public import PolishSpaceBook.LambdaInputPrefixes
public import PolishSpaceBook.LambdaContinuousCoding
public import PolishSpaceBook.LambdaOracleOutputSearch
public import PolishSpaceBook.LambdaAnswerAgreement
public import PolishSpaceBook.LambdaInputCertificateChecker
public import PolishSpaceBook.LambdaInputCertificates
public import PolishSpaceBook.LambdaOutputSearch
public import PolishSpaceBook.LambdaHeadStandardization
public import PolishSpaceBook.LambdaOracleSearch

@[expose] public section

/-!
# Appendix: lambda calculus and computability

Formalization targets for `polish-space/src/polish-space-book/appendix-lambda-calculus-computability.md`.

`LambdaSyntaxSubstitution` implements the stated named syntax, least-fresh
variable choice and capture-avoiding substitution, with a proof that a bound
by the original syntax-tree size suffices. It proves the exact free-variable
formula and preservation of closed terms under finite beta-reduction.
`LambdaNamedAlpha` defines alpha-equivalence by named binder renaming.
`LambdaNameCorrespondence` compares named terms under corresponding variable
names and proves substitution compatibility and independence of contraction
from binder names directly. `LambdaAlphaEquivalence` uses these proofs to
construct substitution and beta-reduction on alpha-classes. Class reduction is exactly raw reduction between some
representatives; finite reduction preserves closedness on classes as well.
`LambdaReductionSubstitution` proves substitution composition and compatibility
with one-step and finite beta-reduction. Its strengthened induction uses finite
lists of substitutions to handle fresh renaming in abstraction contexts.
Reduction of every inserted copy is proved separately, including zero copies.
`LambdaParallelReduction` constructs parallel reduction on alpha-classes, proves
substitution compatibility and inversion with a prescribed binder, and uses the
diamond and finite-strip constructions to prove confluence, Church--Rosser, and
uniqueness of normal forms. `LambdaNumerals` constructs closed, distinct normal-form Church numerals.
`LambdaNumeralOperations` derives iteration, successor, addition, multiplication,
Church booleans, zero testing, functional pairs and selection, predecessor, and
truncated subtraction by explicit finite beta reductions. `LambdaPrimitiveRecursion`
constructs a closed recursor and uniform parameter passing. `LambdaNumericalPairing`
implements square-shell pairing and proves its numerical inverse identities.
`LambdaSquareRoot` implements bounded square-root iteration; `LambdaNumericalProjections`
uses it to implement both inverse projections, with finite beta-reduction proofs.
`LambdaOracleRecursion` extends the same recursor to input-name queries,
proves uniform Type-Two recursion, and implements adaptive iteration of a name.
`LambdaOracleSearch` constructs sequential search by self-application, proves
finite successful-prefix reductions and uniform least-witness realizers, and
finds the first zero of an input name. `LambdaSyntaxCoding` implements syntax
constructor codes; `LambdaSyntaxInspection` implements their tags, payloads,
and fields by closed lambda programs. `LambdaReductionCertificates` proves
sound and complete finite certificate checks at the meta level.
`LambdaCodeSubstitution` realizes the exact named substitution on syntax codes.
`LambdaAlphaEncoding` relates the named relation to the auxiliary indexed syntax
used by `LambdaBindingCodes` to decide alpha-equivalence by lambda terms.
`LambdaFiniteLists` supplies
finite-list recursion and operations. `LambdaBetaSuccessors` enumerates named
one-step reducts and decides the named step relation. `LambdaCertificateChecker`
combines these into a closed certificate checker and a finite-stage reduction
tester, proving that some stage succeeds exactly when a finite reduction exists.
`LambdaNumeralCodes` constructs the codes of the fixed Church numerals.
`LambdaProgramCodes` decides closedness by bounded free-variable testing,
implements the fallback convention of the program enumeration, and constructs
codes of programs applied to numerical inputs. Its total candidate tester
checks a paired output and finite stage, with an exact existential criterion
for numerical outputs. `LambdaHeadStandardization` proves equivalence with
inductive standard reduction and head exposure of every beta-reachable
abstraction. `LambdaHeadNormalization` moves head steps to the front and
excludes infinite head stages from terms having a numerical output.
`LambdaSearchResult` places the result function in the successful search
branch and proves both successful reduction and absence of numerical outputs
when every test fails. `LambdaOutputSearch` combines these constructions with
candidate testing and projection, proving the exact numerical graph and domain
of an ordinary universal evaluator. `LambdaInputCertificates` supplies finite
answer tables, exact named query reducts, and sound and complete certificates
for input-query reduction on alpha-classes. Their finite-stage detector has a
uniform input-prefix bound. `LambdaQuerySuccessors` implements the exact
finite-table query list and named input-step test on numerical codes.
`LambdaOracleLists` extends the same list fold to handlers with a free input name.
`LambdaAnswerAgreement` constructs the closed answer-agreement, candidate, and
bounded-certificate programs, proves their exact Boolean outputs, and identifies
finite input-query reduction with acceptance at some numerical bound.
`LambdaInputCertificateChecker` implements the table-dependent certificate
check by a closed lambda term. `LambdaOracleHeadStandardization` and
`LambdaOracleHeadNormalization` extend head exposure and infinite-stage
exclusion to input queries, using grouped argument reductions at a root query.
`LambdaOracleSearchResult` proves exact failed-search behavior with an input.
`LambdaOracleOutputSearch` assembles the closed indexed evaluator and proves
its full numerical graph and domain, with no termination assumption. Migrating
the remaining realizer clients still needs work; cross-model simulation is not
a prerequisite.
-/

namespace PolishSpaceBook

end PolishSpaceBook
