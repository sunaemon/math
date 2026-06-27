---
macros-file: polish-space/tex/macros.tex
notation-watch:
  - FreeVarsTerm
  - FreeVarsFormula
  - SubstTerm
  - SubstFormula
---

\begin{mathmeta}
  \type{term}
  \type{formula}
  \notationtype{\FreeVars}{term}{\FreeVarsTerm}
  \notationtype{\FreeVars}{formula}{\FreeVarsFormula}
  \notationtype{\subst}{term}{SubstTerm}
  \notationtype{\subst}{formula}{SubstFormula}
  \inferbinder{\forallbind}{formula}
  \inferbinder{\existsbind}{formula}
  \inferatom{\bot}{formula}
  \inferinfix{=}{formula}{70}{non}
  \inferinfix{\land}{formula}{80}{left}
  \inferinfix{\lor}{formula}{85}{left}
  \inferinfix{\to}{formula}{90}{right}
  \inferhead{upper}{formula}
  \inferhead{lower}{term}
  \inferpostfix{\subst}
  \vars{x,t}{term}
  \vars{\varphi}{formula}
  \define{\FreeVarsTerm,SubstTerm}
\end{mathmeta}

Term variables: $\FreeVars{t}$.

Term substitution: $t\subst{x}{t}$.

\begin{mathmeta}
  \define{FreeVarsFormula,SubstFormula}
\end{mathmeta}

Formula variables: $\FreeVars{\varphi}$.

Quantified formula: $\FreeVars{\forallbind{x}{\varphi}}$.

Formula substitution: $\varphi\subst{x}{t}$.
