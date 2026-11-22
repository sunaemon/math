A half-open interval after a command must not gain a stray bracket:
$x\in[0,1)$ and $f\colon[0,1)\to X$.

Display math keeps the same shape: $$d:X\times X\to[0,\infty)$$

A genuine optional argument still round-trips: $\sqrt[3]{x}$.

A balanced interval after a command is unchanged: $x\in[0,1]$.

A tree body at the start of an alignment is mathematical content:
$$\begin{aligned}
[T]&=F,\\
[S]&=G.
\end{aligned}$$

An explicit alignment position remains an option:
$$\begin{aligned}[t]
[T]&=F.
\end{aligned}$$

Already disambiguated brackets remain unchanged:
$$\begin{aligned}\relax[T]&=F.\end{aligned}$$
