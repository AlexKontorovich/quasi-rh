# Quasi-RH at 11/12

This repository develops a Lean proof of the zero-free half-plane

\[
  \operatorname{Re}(s) > \frac{11}{12}
\]

for the Riemann zeta function.  We work with the untwisted ideal-Mobius sum
over \(\mathbb{Q}(\sqrt{-3})\), with ideal denominators coprime to \((6)\);
no auxiliary Hecke character is included.

The project has two equally important outputs:

1. a kernel-checked Lean proof of the theorem; and
2. a short mathematical guide that explains the conceptual spine of the
   argument and displays the corresponding Lean statements at the points
   where they matter.

## The argument in one page

Here \(K=\mathbb Q(\omega)\), \(\mathcal O=\mathbb Z[\omega]\), and
\(\omega\) is a primitive cube root of unity. Columns \(\mathfrak n\) are
nonzero integral ideals coprime to \((6)\); rows \(u\) range over every
element of \(\mathcal O\), with no primary or coprimality restriction.
The norms are \(\mathrm N\mathfrak n=\#(\mathcal O/\mathfrak n)\) and
\(\mathrm N(u)=u\bar u\). The [blueprint](blueprint/index.html) defines
these objects, the ideal Möbius function, and the sextic character in prose
and Lean. We denote the Möbius partial sums by \(M_u(N)\) throughout.

Begin with a smoothly truncated ideal-Mobius sum

\[
  M_1(N)=\sum_{\substack{0\ne\mathfrak n\subseteq\mathcal O\\(\mathfrak n,(6))=1}}\mu_K(\mathfrak n)
  W\!\left(\frac{\mathrm N\mathfrak n}{N}\right).
\]

Embed it into the sextically twisted family

\[
  M_u(N)=\sum_{\substack{0\ne\mathfrak n\subseteq\mathcal O\\(\mathfrak n,(6))=1}}\mu_K(\mathfrak n)
  \chi_{\mathfrak n}(u)
  W\!\left(\frac{\mathrm N\mathfrak n}{N}\right).
\]

The central analytic estimate is the mean-square bound

\[
  S(N,H)=\sum_{u\in\mathcal O} V\!\left(\frac{\mathrm N(u)}H\right)|M_u(N)|^2
  \ll_{\varepsilon}N^{1+\varepsilon}H,
  \qquad H=N^{1+\vartheta}.
\]

The sixth-power rows amplify the original sum. For a primary prime \(p\),

\[
  \left(\frac{p^6}{n}\right)_6=\mathbf 1_{p\nmid n},
  \qquad
  M_{p^6}(N)=M_1(N)+O(N/Y).
\]

There are about \(Y/\log Y\) such primes with \(N(p)\asymp Y\). Taking
\(Y=H^{1/6}\) and retaining these rows in the mean square gives

\[
  |M_1(N)|^2
  \ll N^{1+\varepsilon}H^{5/6}+N^2H^{-1/3},
\]

and therefore

\[
  M_1(N)\ll_\varepsilon N^{11/12+\varepsilon}.
\]

To prove the mean-square estimate, open the square and apply Poisson summation
in the Eisenstein-integer row variable. Sextic Gauss sums appear. A
Gauss--Jacobi identity combines them with the Mobius coefficient and produces
cubic Gauss-sum coefficients, which are recognized as Fourier coefficients of
Kubota's cubic theta function. Its transformation law supplies the dual
estimate, after the cube-divisor terms are separated and controlled.

Finally, the power saving for the Mobius sums gives the required zeta
nonvanishing in \(\operatorname{Re}(s)>11/12\).

## Planned correspondence between prose and Lean

| Mathematical step | Intended Lean module |
| --- | --- |
| Eisenstein integers, primary generators, and norm conventions | `ElevenTwelfths.Arithmetic` |
| Smooth dyadic weights | `ElevenTwelfths.SmoothDyadic` |
| Sextic family, `M_u(N)`, and the smooth mean square `S(N,H)` | `ElevenTwelfths.SexticFamily` |
| Amplification/extraction of the \(u=p^6\) rows | `ElevenTwelfths.Amplification` |
| Poisson summation and sextic Gauss sums | `ElevenTwelfths.Poisson` |
| Gauss--Jacobi conversion to cubic coefficients | `ElevenTwelfths.GaussJacobi` |
| Cubic theta transformation and dual mean square | `ElevenTwelfths.CubicTheta` |
| \(D^{11/12+\varepsilon}\) bound | `ElevenTwelfths.MeanSquare` |
| Mobius bound implies the zero-free half-plane | `ElevenTwelfths.Nonvanishing` |

The expository document will quote only stable, meaningful theorem statements;
implementation lemmas will remain in the Lean files rather than overwhelming
the mathematical narrative. When a definition already exists in mathlib, use it
directly and record its mathlib definition and source in the blueprint rather
than introduce a project wrapper.

## Side-by-side blueprint

The [HTML blueprint](blueprint/index.html) follows the format of the Zaremba
repository: mathematical exposition on the left, corresponding Lean
declarations on the right, with collapsible proof blocks where useful.

We will build this blueprint little by little together as we go through the
argument. Add each step's motivation, precise hypotheses, and meaningful Lean
statements as our understanding develops; keep planned estimates and missing
proofs explicitly marked. The starting page defines the field, ring of integers,
both norms, ideal
Möbius function, sextic character, Möbius partial sums, and mean square. Smooth
weights are background conventions, not separate blueprint entries.

Open `blueprint/index.html` directly in a browser, or serve the repository root:

```bash
python3 -m http.server 8000
```

Then visit <http://localhost:8000/blueprint/>. Math rendering uses MathJax from
a CDN and requires an internet connection. Edit `blueprint/index.html` directly
and keep its Lean excerpts synchronized with the linked source files; there is
no generation step. The prose notes in [docs/argument.md](docs/argument.md)
should remain consistent with the blueprint.

## Status

The arithmetic objects and the concrete sums `M` and `S` are defined in Lean.
The lattice norm-ball finiteness, whole-lattice identity, nonnegativity, and
zero-scale lemmas are proved. Character identities, primary-generator
correspondence, analytic estimates, and the final theorem remain to be proved;
the module table above is the proposed architecture.

The column restriction follows the reference paper. Restoring the omitted
Euler factors at 2 and 3 is recorded in [the argument notes](docs/argument.md).
It imposes no restriction on the row lattice used for Poisson summation.

## Primary reference

OpenAI, [*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex),
October 5, 2026 (the alternate \(11/12\) proof), especially Sections 2–4 for
the summation and residue-symbol conventions.
