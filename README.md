# Quasi-RH at 11/12

This repository develops a Lean proof of the zero-free half-plane

\[
  \operatorname{Re}(s) > \frac{11}{12}
\]

for the Riemann zeta function and, more generally, finite-order Hecke
\(L\)-functions over \(\mathbb{Q}(\sqrt{-3})\).

The project has two equally important outputs:

1. a kernel-checked Lean proof of the theorem; and
2. a short mathematical guide that explains the conceptual spine of the
   argument and displays the corresponding Lean statements at the points
   where they matter.

## The argument in one page

For a fixed finite-order Hecke character \(\nu\), begin with a smoothly
truncated ideal-Mobius sum

\[
  A_1(N)=\sum_{\mathfrak n}\mu_K(\mathfrak n)\nu(\mathfrak n)
  W\!\left(\frac{N\mathfrak n}{N}\right).
\]

Embed it into the sextically twisted family

\[
  A_u(N)=\sum_{\mathfrak n}\mu_K(\mathfrak n)\nu(\mathfrak n)
  \left(\frac{u}{n}\right)_6
  W\!\left(\frac{N\mathfrak n}{N}\right).
\]

The central analytic estimate is the mean-square bound

\[
  S(N,H)=\sum_u V\!\left(\frac{N(u)}H\right)|A_u(N)|^2
  \ll_{\varepsilon}N^{1+\varepsilon}H,
  \qquad H=N^{1+\vartheta}.
\]

The sixth-power rows amplify the original sum. For a primary prime \(p\),

\[
  \left(\frac{p^6}{n}\right)_6=\mathbf 1_{p\nmid n},
  \qquad
  A_{p^6}(N)=A_1(N)+O(N/Y).
\]

There are about \(Y/\log Y\) such primes with \(N(p)\asymp Y\). Taking
\(Y=H^{1/6}\) and retaining these rows in the mean square gives

\[
  |A_1(N)|^2
  \ll N^{1+\varepsilon}H^{5/6}+N^2H^{-1/3},
\]

and therefore

\[
  A_1(N)\ll_\varepsilon N^{11/12+\varepsilon}.
\]

To prove the mean-square estimate, open the square and apply Poisson summation
in the Eisenstein-integer row variable. Sextic Gauss sums appear. A
Gauss--Jacobi identity combines them with the Mobius coefficient and produces
cubic Gauss-sum coefficients, which are recognized as Fourier coefficients of
Kubota's cubic theta function. Its transformation law supplies the dual
estimate, after the cube-divisor terms are separated and controlled.

Finally, the power saving for the Mobius sums implies analytic continuation of
the reciprocal \(1/L_K(s,\nu)\) into \(\operatorname{Re}(s)>11/12\), hence
nonvanishing there.

## Planned correspondence between prose and Lean

| Mathematical step | Intended Lean module |
| --- | --- |
| Eisenstein integers, primary generators, and norm conventions | `ElevenTwelfths.Arithmetic` |
| Smooth dyadic weights | `ElevenTwelfths.SmoothDyadic` |
| Sextic family, `A_u(N)`, and the smooth mean square `S(N,H)` | `ElevenTwelfths.SexticFamily` |
| Amplification/extraction of the \(u=p^6\) rows | `ElevenTwelfths.Amplification` |
| Poisson summation and sextic Gauss sums | `ElevenTwelfths.Poisson` |
| Gauss--Jacobi conversion to cubic coefficients | `ElevenTwelfths.GaussJacobi` |
| Cubic theta transformation and dual mean square | `ElevenTwelfths.CubicTheta` |
| \(D^{11/12+\varepsilon}\) bound | `ElevenTwelfths.MeanSquare` |
| Mobius bound implies the zero-free half-plane | `ElevenTwelfths.Nonvanishing` |

The expository document will quote only stable, meaningful theorem statements;
implementation lemmas will remain in the Lean files rather than overwhelming
the mathematical narrative.

## Status

Initial project scaffold. The proof modules and theorem names above are the
proposed architecture, not yet completed claims.

## Primary reference

OpenAI, *The Quasi-Riemann Hypothesis*, October 5, 2026 (the alternate
\(11/12\) proof).
