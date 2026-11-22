"""Regression checks for declared sorts versus contextual harvests."""

import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class SortAuditTests(unittest.TestCase):
    def audit(self, declaration, uses, *, dsl=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            macros = root / "macros.tex"
            macros.write_text(
                r"% notation-type: \LambdaSyntaxCode : a -> Nat"
                "\n"
                r"\newcommand{\LambdaSyntaxCode}[1]{\ulcorner #1\urcorner}"
                "\n"
                r"\newcommand{\LambdaTermName}[1]{\mathsf{#1}}"
                "\n"
                r"% notation-type: \Pair : a x b -> Prod(a,b)"
                "\n"
                r"\newcommand{\Pair}[2]{\langle #1,#2\rangle}"
                "\n"
                r"% notation-type: \NamePair : Name x Name -> Name"
                "\n"
                r"\newcommand{\NamePair}[2]{\langle #1,#2\rangle}"
                "\n"
                r"% notation-type: \NatPair : Nat x Nat -> Nat"
                "\n"
                r"\newcommand{\NatPair}[2]{\langle #1,#2\rangle}"
                "\n"
                r"% notation-type: \BinaryPair : Nat x Nat -> Seq(Nat)"
                "\n"
                r"\newcommand{\BinaryPair}[2]{\langle #1,#2\rangle}"
                "\n"
                r"% notation-type: \NaturalUse : Nat -> Nat"
                "\n"
                r"\newcommand{\NaturalUse}[1]{#1}"
                "\n"
                r"% notation-type: \RealUse : Real -> Real"
                "\n"
                r"\newcommand{\RealUse}[1]{#1}"
                "\n"
                r"% notation-type: \NameUse : Name -> Name"
                "\n"
                r"\newcommand{\NameUse}[1]{#1}"
                "\n"
            )
            source = root / "source.md"
            source.write_text(
                "# Test\n\n"
                + ("\\begin{mathmeta}\n" + declaration + "\n\\end{mathmeta}\n" if declaration else "")
                + "\n"
                + uses
                + "\n"
            )
            result = subprocess.run(
                [
                    str(ROOT / "build/book-filter"),
                    "lint",
                    "--dsl-audit" if dsl else "--sort-audit",
                    f"--macros={macros}",
                    str(source),
                ],
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stderr

    def test_multiline_argument_preserves_application_coverage(self):
        for uses in (r"$\NaturalUse{n}$.", "$\\NaturalUse{\nn}$."):
            with self.subTest(uses=uses):
                report = self.audit(r"\vars{n}{Nat}", uses)
                self.assertIn("1 signed applications, 1 fully inferred, 0 mismatch(es)", report)

    def test_multiline_lambda_syntax_code_regression(self):
        uses = "$\\LambdaSyntaxCode{\n\\LambdaTermName{opposite}_T}$."
        report = self.audit("", uses)
        self.assertIn("1 signed applications", report)
        self.assertEqual(report, self.audit("", uses.replace("\n", " ")))

    def test_multiline_mismatch_reports_opening_line(self):
        report = self.audit(r"\vars{p}{Name}", "$\\NaturalUse{\np}$.")
        self.assertIn("1 signed applications, 1 fully inferred, 1 mismatch(es)", report)
        self.assertIn("source.md:7: sort mismatch:", report)
        self.assertIn("expected sort Nat but inferred Name", report)

    def test_multiline_nested_applications_are_all_counted(self):
        uses = "$\\NaturalUse{\n\\NameUse{p}}$."
        report = self.audit(r"\vars{p}{Name}", uses)
        self.assertIn("2 signed applications", report)
        single_line = self.audit(r"\vars{p}{Name}", uses.replace("\n", " "))
        self.assertEqual(report, single_line)

    def test_multiline_inline_and_display_spans_remain_separate(self):
        uses = "$\\NaturalUse{\nn}$ then $$\\NaturalUse{\nn}$$ and $\\NaturalUse{n}$."
        report = self.audit(r"\vars{n}{Nat}", uses)
        self.assertIn("3 signed applications, 3 fully inferred, 0 mismatch(es)", report)

    def test_unclosed_inline_does_not_cross_block_boundary(self):
        boundaries = (
            "\n\n",
            "\n## Next\n",
            "\n```\nignored\n```\n",
            "\n\\begin{mathmeta}\n\\vars{n}{Nat}\n\\end{mathmeta}\n",
        )
        for boundary in boundaries:
            with self.subTest(boundary=boundary):
                report = self.audit("", "$unfinished" + boundary + r"$\NaturalUse{0}$.")
                self.assertIn("1 signed applications, 1 fully inferred, 0 mismatch(es)", report)

    def test_escaped_dollars_do_not_delimit_math(self):
        report = self.audit(r"\vars{n}{Nat}", r"Literal \$ and $\NaturalUse{n}$; \$ again.")
        self.assertIn("1 signed applications, 1 fully inferred, 0 mismatch(es)", report)

    def test_comments_in_multiline_math_are_ignored(self):
        uses = "$\\NaturalUse{ % $\\NameUse{p}$\n<!-- $\\NameUse{p}$ -->\nn}$"
        report = self.audit(r"\vars{n}{Nat}", uses)
        self.assertIn("1 signed applications, 1 fully inferred, 0 mismatch(es)", report)

    def test_multiline_math_uses_new_sections_declarations(self):
        uses = r"""$\NaturalUse{
n}$.
## Next
\begin{mathmeta}
\vars{n}{Name}
\end{mathmeta}
$\NaturalUse{
n}$."""
        report = self.audit(r"\vars{n}{Nat}", uses)
        self.assertIn("2 signed applications, 2 fully inferred, 1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Name", report)

    def test_declared_natural_can_be_used_as_real(self):
        report = self.audit(r"\vars{R}{Nat}", r"$\RealUse{R}$ and $\NaturalUse{R}$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertNotIn("harvest conflict", report)

    def test_explicit_incompatible_sort_still_reports_mismatch(self):
        report = self.audit(r"\vars{R}{Real}", r"$\NaturalUse{R}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Real", report)

    def test_undeclared_conflicting_uses_remain_visible(self):
        report = self.audit("", r"$\NameUse{r}$ and $\NaturalUse{r}$.")
        self.assertIn("harvest conflict", report)

    def test_function_result_and_domain(self):
        declaration = r"\vars{f}{Fun(Nat,Real)}" + "\n" + r"\vars{n}{Nat}"
        report = self.audit(declaration, r"$\NaturalUse{f(n)}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Real", report)
        report = self.audit(declaration + "\n" + r"\vars{x}{Name}", r"$f(x)$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Name", report)

    def test_greek_function_on_structured_sequence(self):
        declaration = r"\vars{\sigma}{Fun(Seq(Nat),Nat)}" + "\n" + r"\vars{s}{Seq(Nat)}"
        report = self.audit(declaration, r"$\NaturalUse{\sigma(s)}$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("2 fully inferred", report)

    def test_decorated_function_keeps_its_own_codomain(self):
        declaration = r"\vars{g}{Fun(Real,Nat)}" + "\n" + r"\vars{\tilde{g}}{Fun(Real,Real)}"
        report = self.audit(declaration, r"$\NaturalUse{\tilde{g}(0)}$ and $\NaturalUse{g(0)}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Real", report)
        self.assertIn("4 fully inferred", report)

    def test_product_domain_checks_each_argument(self):
        declaration = r"""\vars{f}{Fun(Prod(Nat,Nat),Nat)}
\vars{k,r}{Nat}
\vars{p}{Name}"""
        report = self.audit(declaration, r"$\NaturalUse{f(k,r)}$ and $f(k,p)$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("f argument 2: expected sort Nat but inferred Name", report)
        self.assertIn("3 fully inferred", report)

    def test_multiargument_call_preserves_nested_commas(self):
        declaration = r"""\vars{f}{Fun(Prod(Nat,Nat,Nat),Nat)}
\vars{k,r,a_*}{Nat}"""
        report = self.audit(declaration, r"$\NaturalUse{f(a_{i,j},f(k,r,0),r)}$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("3 fully inferred", report)

    def test_product_pair_argument_and_comma_call_agree(self):
        declaration = r"\vars{f}{Fun(Prod(Nat,Name),Nat)}" + "\n" + r"\vars{p}{Name}"
        report = self.audit(declaration, r"$f(0,p)$ and $f(\Pair{0}{p})$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("3 fully inferred", report)

    def test_product_association_is_not_erased(self):
        declaration = r"\vars{f}{Fun(Prod(Nat,Prod(Name,Nat)),Nat)}" + "\n" + r"\vars{p}{Name}"
        report = self.audit(declaration, r"$f(\Pair{\Pair{0}{p}}{0})$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat x (Name x Nat)", report)
        self.assertIn("inferred (Nat x Name) x Nat", report)
        report = self.audit(declaration, r"$f(0,\Pair{p}{0})$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("2 fully inferred", report)

    def test_nested_product_does_not_enable_flat_call(self):
        declaration = r"\vars{f}{Fun(Prod(Nat,Prod(Nat,Nat)),Nat)}"
        report = self.audit(declaration, r"$f(0,1,2)$.")
        self.assertIn("0 signed applications", report)

    def test_legacy_pair_sort_is_a_product_alias(self):
        declaration = r"\vars{f}{Fun(Pair(Nat,Nat),Nat)}"
        report = self.audit(declaration, r"$f(\Pair{0}{1})$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("2 fully inferred", report)

    def test_names_and_natural_functions_agree_without_widening_outputs(self):
        declaration = r"""\vars{g}{Fun(Nat,Nat)}
\vars{h}{Fun(Nat,Real)}
\vars{F}{Fun(Fun(Nat,Nat),Nat)}
\vars{p}{Name}"""
        report = self.audit(declaration, r"$\NameUse{g}$, $\NameUse{h}$, $\NaturalUse{F(p)}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Name but inferred (Nat -> Real)", report)
        self.assertIn("4 fully inferred", report)

    def test_family_entry_overrides_and_scalar_are_distinct(self):
        declaration = r"""\vars{a_*}{Nat}
\vars{a_0}{Int}
\vars{a}{Name}"""
        report = self.audit(declaration, r"$\NaturalUse{a_1}$, $\NaturalUse{a_{0}}$, $\NameUse{a}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Int", report)
        self.assertIn("3 fully inferred", report)

    def test_parameterized_sequence_entry(self):
        report = self.audit(r"\vars{s}{Seq(Nat)}", r"$\NaturalUse{s_{2}}$ and $\NameUse{s_3}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Name but inferred Nat", report)

    def test_element_sort_of_set_and_sequence(self):
        declaration = r"""\vars{A}{Set(Name)}
\vars{x}{Elem(A)}
\vars{s}{Seq(Nat)}
\vars{k}{Elem(s)}"""
        report = self.audit(declaration, r"$\NameUse{x}$, $\NaturalUse{k}$, $\NaturalUse{x}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Name", report)
        self.assertIn("3 fully inferred", report)

    def test_family_declaration_obeys_local_scope(self):
        declaration = r"\vars{s_*}{Name}"
        uses = r"""\begin{mathmeta}
\scopebegin
\vars{s_*}{Nat}
\end{mathmeta}
$\NaturalUse{s_1}$.
\begin{mathmeta}
\scopeend
\end{mathmeta}
$\NameUse{s_1}$."""
        report = self.audit(declaration, uses)
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("2 fully inferred", report)

    def test_recursive_element_declaration_stays_unknown(self):
        declaration = r"\vars{x}{Elem(y)}" + "\n" + r"\vars{y}{Elem(x)}"
        report = self.audit(declaration, r"$\NaturalUse{x}$.")
        self.assertIn("0 fully inferred", report)
        self.assertIn("0 mismatch(es)", report)

    def test_dsl_membership_uses_parameterized_set(self):
        declaration = r"\vars{A}{Set(Prod(Nat,Nat))}" + "\n" + r"\vars{p,q}{Nat}"
        report = self.audit(declaration, r"$\langle p,q\rangle\in A$.", dsl=True)
        self.assertIn("Pair", report)
        self.assertNotIn("NatPair", report)
        self.assertIn("1 resolved", report)

    def test_dsl_function_domain_and_family_entries(self):
        declaration = r"\vars{f}{Fun(Name,Nat)}" + "\n" + r"\vars{p_*}{Name}"
        report = self.audit(declaration, r"$f(\langle p_1,p_2\rangle)$.", dsl=True)
        self.assertIn("NamePair", report)
        self.assertIn("1 resolved", report)

    def test_name_retains_its_sort_while_coordinates_are_natural(self):
        declaration = r"\vars{p,x}{Name}" + "\n" + r"\vars{n}{Nat}"
        report = self.audit(declaration, r"$\NameUse{p}$ and $\NaturalUse{p(n)}$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("3 fully inferred", report)
        report = self.audit(declaration, r"$p(x)$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Name", report)

    def test_sequence_coordinate_as_function_application(self):
        declaration = r"\vars{s}{Seq(Real)}" + "\n" + r"\vars{n}{Nat}"
        report = self.audit(declaration, r"$\RealUse{s(n)}$ and $\NaturalUse{s(n)}$.")
        self.assertIn("1 mismatch(es)", report)
        self.assertIn("expected sort Nat but inferred Real", report)

    def test_unbraced_subscript_does_not_capture_following_application(self):
        declaration = r"\vars{t}{Name}" + "\n" + r"\vars{v}{Seq(Nat)}"
        report = self.audit(declaration, r"$f_t(v)$ and $f_{t}(v)$.")
        self.assertIn("0 mismatch(es)", report)

    def test_indexed_names_have_natural_coordinates(self):
        declaration = r"\vars{a_*}{Name}" + "\n" + r"\vars{s,n}{Nat}"
        report = self.audit(declaration, r"$\NameUse{a_s}$ and $\NaturalUse{a_s(n)}$.")
        self.assertIn("0 mismatch(es)", report)
        self.assertIn("3 fully inferred", report)

    def test_dsl_name_coordinate_supplies_natural_input_context(self):
        declaration = r"\vars{p}{Name}" + "\n" + r"\vars{n,m}{Nat}"
        report = self.audit(declaration, r"$p(\langle n,m\rangle)$.", dsl=True)
        self.assertIn("NatPair", report)
        self.assertNotIn("BinaryPair", report)
        self.assertIn("1 resolved", report)


if __name__ == "__main__":
    unittest.main()
