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
sixth-power amplifier. The fixed-shell model is constructed from the
`RowCompletion.BranchDecoding` layer, while the public nonvanishing endpoint
is proved only in `ElevenTwelfths.Unconditional`.

## The argument

Let `W` and `V` be smooth weights supported in `[1 / 2, 1]`. For an
Eisenstein integer `h`, the public family is

\[
  M_h(X)=
  \sum_{\substack{n\ \mathrm{primary}\\\mathcal N(n)\le X}}
    \mu_K((n))\,\chi_{(n)}(h)\,
    W\!\left(\frac{\mathcal N(n)}X\right).
\]

Thus the Lean summand visibly contains primaryness, ideal Möbius, the actual
sextic twist, and the smooth cutoff. The public second moment is defined as
the finite sum

\[
  S(X,H)=\sum_{\mathcal N(h)\le H}
    V\!\left(\frac{\mathcal N(h)}H\right)|M_h(X)|^2.
\]

Immediately before entering the Poisson-summation interface, compact support
converts this finite sum to a `tsum` over the full Eisenstein lattice. The
checked bridges are `outsideM_eq_idealRowSum` and
`outsideS_eq_idealRowSum_tsum`.

The reused analytic core opens the square, applies Eisenstein Poisson
summation, evaluates the local Gauss sums, recognizes the resulting cubic
theta coefficients, applies theta reflection and a second Poisson passage,
and closes the estimate with the quadratic large sieve. A local
parameterization of its finite descent gives, for every `theta > 0`, the
schematic estimate

\[
  \sum_{\mathcal N(h)\le X^{1+\theta}} |M_h(X)|^2
  \ll_{\theta,\varepsilon} X^{2+\theta+\varepsilon}.
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
  \alpha=\frac{1+\theta}{6},\qquad B=X^\alpha,
\]

the amplified rows have norm at most `X ^ (1 + theta)`. Cauchy--Schwarz and
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
  \mu_K(I)\prod_{P\mid I}\left(1-\frac1{\mathcal N(P)}\right).
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
| Explicit finite `M_h(X)` and `S(X,H)` | `ElevenTwelfths.ConcreteFamily` |
| Finite-to-`tsum` boundary | `outsideS_eq_idealRowSum_tsum` |
| Theta/reflection model built from branch decoding | `ElevenTwelfths.ActualFixedShellModels` |
| Arbitrary-positive-radius mean square | `outside_mean_square_of_theta_models_pos` |
| Symbolic sixth-power exponent calculation | `outside_totient_moebius_bound_of_mean_square` |
| Smoothed bound at `11 / 12` | `actual_smoothedWeightedMobiusBound` |
| Inverse Mellin and nonvanishing | `ElevenTwelfths.Nonvanishing` |
| Direct final assembly | `ElevenTwelfths.Unconditional` |

The short mathematical guide is in [`docs/argument.md`](docs/argument.md).

## Side-by-side blueprint

The [HTML blueprint](blueprint/index.html) presents the direct proof
in mathematical stages, from the explicit Eisenstein family through the
two Poisson passages, cubic theta reflection, quadratic sieve, sixth-power
amplifier, Mellin continuation, and zeta nonvanishing. Each beat pairs a short
natural-language explanation with the definitions and theorem boundary that
Lean checks. The [ideal-family notes](docs/ideal-family.md) preserve an earlier
standalone prototype; they are not the proof spine shown in the blueprint.

Read the [published blueprint](https://alexkontorovich.github.io/quasi-rh/index.html).
GitHub Actions republishes it whenever `blueprint/index.html` or the Pages
workflow changes on `main`; it can also be deployed manually from Actions.
Only the standalone HTML is published. Source links require repository access.

Open `blueprint/index.html` directly, or run `python3 -m http.server 8000`
and visit <http://localhost:8000/blueprint/>. MathJax requires internet access.
The main readable interfaces are now:

- `ElevenTwelfths.ZetaFamily`: concrete zeta-only `M`, `S`, opening the square,
  sixth-power coprimality, and the unconditional mean-square bound for those
  same sums.
- `ElevenTwelfths.ThetaSums`: actual cubic coefficients, exact cube inversion,
  quadratic energy, and the sharp `L + Y` large sieve.
- `ElevenTwelfths.Voronoi`: the fixed-shell Voronoi identity for the same
  completed `thetaSum`, specialized to conductor one and smooth dyadic weights.
- `ElevenTwelfths.ZetaBound`: the explicit density-weighted Möbius sum and
  its unconditional `11/12 + ε` bound.

These are proved interfaces to the existing analytic core, not a replacement
proof by the introductory heuristics. In particular, the full reflected
moment is not claimed to equal a single quadratic-energy block: branch
weights, local phases, cube scales and the descent remain in the core.

Marked HTML panels are generated from actual Lean declarations:

```sh
node scripts/sync-blueprint.mjs
node scripts/sync-blueprint.mjs --check
```

Edit prose directly, but edit marked Lean excerpts in their source modules
and regenerate them. Definitions are included in full; theorem statements
omit only their proofs. Use existing mathlib definitions where available, and keep the
readable mathematical invariant separate from the longer formal interface.

## Building

Run the cache download before the build; otherwise Lake may spend a long time
building Mathlib `.olean` files locally.

```sh
lake exe cache get
lake build
lake env lean tests/Blueprint.lean
```

The Lake configuration automatically applies and verifies the vendored Lean
4.34.1 compatibility patch for `rellich-kondrachov` before dependency
resolution. The hook checks the dependency's pinned origin and revision, is
idempotent when the patch is already present, and runs again after
`lake update`. No manual `git apply` step is needed.

## Provenance

The analytic components under `OAI/` come from OpenAI's
[`math`](https://github.com/openai/math) repository. This project reuses those
Poisson, Gauss-sum, theta-reflection, row-completion, and sieve layers and
locally parameterizes the finite descent needed for the direct `11 / 12`
argument. The pinned source revision and local adaptations are recorded under
[`upstream/`](upstream/), and the upstream Apache-2.0 license is included in
[`LICENSE`](LICENSE).
