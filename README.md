# Quasi-RH at 11/12

This repository develops a direct Lean proof of the zero-free half-plane

\[
  \operatorname{Re}(s)>\frac{11}{12}
  \quad\Longrightarrow\quad
  \zeta(s)\ne 0.
\]

The public endpoint is

```lean
theorem riemannZeta_ne_zero_of_re_gt_elevenTwelfths
    (z : ℂ) (hz : (11 / 12 : ℝ) < z.re) :
    riemannZeta z ≠ 0
```

This is not obtained by weakening a previously formalized `7 / 8` theorem.
The proof reuses the Eisenstein Poisson, Gauss--Jacobi, cubic-theta,
row-completion, and quadratic-sieve components of OpenAI's formalization, but
assembles them through an arbitrary-positive-radius mean square and a direct
sixth-power amplifier. Its direct import chain does not import
`OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion`.

## The argument

Let `W` and `V` be smooth weights supported in `[1 / 2, 1]`. For an
Eisenstein integer `u`, the public family is

\[
  A_u(N)=
  \sum_{\substack{n\ \mathrm{primary}\\N(n)\le N}}
    \mu_K((n))\,\chi_{(n)}(u)\,
    W\!\left(\frac{N(n)}N\right).
\]

Thus the Lean summand visibly contains primaryness, ideal Möbius, the actual
sextic twist, and the smooth cutoff. The public second moment is defined as
the finite sum

\[
  S(N,H)=\sum_{N(u)\le H}
    V\!\left(\frac{N(u)}H\right)|A_u(N)|^2.
\]

Immediately before entering the Poisson-summation interface, compact support
converts this finite sum to a `tsum` over the full Eisenstein lattice. The
checked bridges are `outsideA_eq_idealRowSum` and
`outsideS_eq_idealRowSum_tsum`.

The reused analytic core opens the square, applies Eisenstein Poisson
summation, evaluates the local Gauss sums, recognizes the resulting cubic
theta coefficients, applies theta reflection and a second Poisson passage,
and closes the estimate with the quadratic large sieve. A local
parameterization of its finite descent gives, for every `theta > 0`, the
schematic estimate

\[
  \sum_{N(z)\le Z^{1+\theta}} |A_z(Z)|^2
  \ll_{\theta,\varepsilon} Z^{2+\theta+\varepsilon}.
\]

On a sixth-power row,

\[
  \chi_{(n)}(b^6)=\mathbf 1_{(b,n)=1}.
\]

The final proof deliberately averages over all `b` in a smooth norm annulus,
rather than first restricting to prime amplifiers. This is the chosen
simplification: it keeps the same sixth-power amplification mechanism while
avoiding a separate prime-number-theorem dependency. With

\[
  \alpha=\frac{1+\theta}{6},\qquad Y=Z^\alpha,
\]

the amplified rows have norm at most `Z ^ (1 + theta)`. Cauchy--Schwarz and
division by the mass of the amplifier give the exponent

\[
  \frac{2+\theta-\alpha}{2}+\eta
  =\frac{11+5\theta}{12}+\eta.
\]

For a requested final loss `epsilon > 0`, Lean takes
`theta = 6 * epsilon / 5` and `eta = epsilon / 2`, yielding exactly
`11 / 12 + epsilon`.

The average is intentionally not forced back to a raw Möbius sum. It produces
the totient-weighted coefficient

\[
  \mu_K(I)\prod_{P\mid I}\left(1-\frac1{N(P)}\right).
\]

The inverse-Mellin stage then restores the corresponding Euler correction,
together with the finitely many excluded Euler factors. The resulting
analytic identity implies nonvanishing of the Dirichlet `L`-function and,
for the trivial character modulo one, of the Riemann zeta function.

## Why the radius can be arbitrarily small

The upstream finite descent used a fixed denominator `1000` and a fixed
reserve `1 / 20`, exposing only row radii greater than `1 / 20`. Here those
constants are collected in `CanonicalDescentScale`. Given any positive
reserve `kappa`,

```lean
CanonicalDescentScale.ofReserve kappa hkappa
```

chooses a sufficiently large finite denominator. Taking
`kappa = theta / 2` gives `outside_mean_square_of_theta_models_pos` for every
positive `theta`. The historical `1 / 20` entry point remains a compatibility
specialization; the direct `11 / 12` assembly does not use it.

## Lean landmarks

| Role | Declaration or module |
| --- | --- |
| Weights supported in `[1 / 2, 1]` | `ElevenTwelfths.SmoothDyadic` |
| Eisenstein norm, primaryness, and `mu_K ((n))` | `ElevenTwelfths.Arithmetic` |
| Explicit finite `A_u(N)` and `S(N,H)` | `ElevenTwelfths.ConcreteFamily` |
| Finite-to-`tsum` boundary | `outsideS_eq_idealRowSum_tsum` |
| Theta/reflection model below the packaged zero-free theorem | `ElevenTwelfths.ActualFixedShellModels` |
| Arbitrary-positive-radius mean square | `outside_mean_square_of_theta_models_pos` |
| Symbolic sixth-power exponent calculation | `outside_totient_moebius_bound_of_mean_square` |
| Smoothed bound at `11 / 12` | `actual_smoothedWeightedMobiusBound` |
| Inverse Mellin and nonvanishing | `ElevenTwelfths.Nonvanishing` |
| Direct final assembly | `ElevenTwelfths.Unconditional` |

The short mathematical guide is in [`docs/argument.md`](docs/argument.md).

## Building

Run the cache download before the build; otherwise Lake may spend a long time
building Mathlib `.olean` files locally.

```sh
lake exe cache get
lake build
```

The Lake configuration automatically applies and verifies the vendored Lean
4.34.1 compatibility patch for `rellich-kondrachov` before dependency
resolution. The hook checks the dependency's pinned origin and revision, is
idempotent when the patch is already present, and runs again after
`lake update`. No manual `git apply` step is needed.

## Provenance

The analytic components under `OAI/` come from OpenAI's
[`math`](https://github.com/openai/math) repository. This project reuses those
components below the packaged zero-free theorem and locally parameterizes
the finite descent needed for the direct `11 / 12` argument. The pinned
source revision and local adaptations are recorded under
[`upstream/`](upstream/), and the upstream Apache-2.0 license is included in
[`LICENSE`](LICENSE).
