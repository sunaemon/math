---
macros-file: polish-space/tex/macros.tex
notation-watch:
  - Foo
---

\begin{mathmeta}
  \type{term}
  \vars{x}{term}
  \with{\vars{y}{term}}
\end{mathmeta}

> \begin{mathmeta}
>   \define{\Foo}
> \end{mathmeta}
>
> Nested definition: $\Foo{x}$ and $\Foo{y}$.

After the block: $\Foo{x}$.
