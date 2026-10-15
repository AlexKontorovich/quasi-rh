# The 11/12 argument, with Lean landmarks

The separate [ideal-family notes](ideal-family.md) and
[HTML blueprint](../blueprint/index.html) develop the ideal-indexed exposition.

The proof has one conceptual spine:

\[
  \text{sextic family}
  \longrightarrow \text{mean square}
  \longrightarrow \text{sixth-power amplification}
  \longrightarrow \text{weighted Möbius bound}
  \longrightarrow \zeta(s)\ne0.
\]

The long analytic middle is reused from OpenAI's formalization below its
packaged zero-free theorem. The new assembly keeps the mean-square radius
symbolic, chooses it as a function of the requested epsilon, and derives
`11 / 12` directly. It does not invoke
`OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion` and does not use a
stronger `7 / 8` theorem as a black box.

## 1. The visible Eisenstein sum

Write `O` for the Eisenstein integers. The public weight structures in
`ElevenTwelfths.SmoothDyadic` are smooth and supported in `[1 / 2, 1]`.
Consequently `W (N(n) / N)` restricts the column variable to
`N / 2 <= N(n) <= N`, and the analogous row cutoff has the clean upper bound
`H`, not `2 * H`.

The arithmetic is concrete:

```lean
def primary (n : 𝒪) : Prop := lambda ^ 2 ∣ n - 1

noncomputable def eisensteinNorm (n : 𝒪) : ℕ :=
  Ideal.absNorm (Ideal.span {n})

noncomputable def eisensteinMobius (n : 𝒪) : ℤ :=
  UniqueFactorizationMonoid.moebius (Ideal.span {n})
```

Thus the readable element sum and the ideal-indexed analytic core use
literally the same Möbius coefficient. Primaryness selects the distinguished
generator rather than summing over all six associates.

For a finite set `S` of excluded bad prime ideals, `outsidePrimaryBall S N`
contains the canonical primary generators of the admissible ideals of norm
at most `N`. The actual twisted sum is

```lean
noncomputable def outsideA ... (W : SmoothDyadicWeight ℂ)
    (u : 𝒪) (N : ℕ) : ℂ :=
  ∑ n ∈ outsidePrimaryBall S N,
    if primary n then
      (eisensteinMobius n : ℂ) * outsideSexticTwist S hbad N u n *
        W ((eisensteinNorm n : ℝ) / (N : ℝ))
    else 0
```

This is the promised explicit expression: primary, Möbius, sextic twist, and
smooth cutoff all remain visible.

## 2. A finite mean square until Poisson

The public mean square is definitionally a `Finset` sum:

```lean
noncomputable def outsideS ...
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑ u ∈ exactRowBall H,
    V ((eisensteinNorm u : ℝ) / (H : ℝ)) *
      ‖outsideA S hbad W u N‖ ^ 2
```

Columns and rows deliberately use different finite balls. Columns are
admissible ideals represented by primary generators; Poisson summation runs
over every Eisenstein integer in the row lattice. The two bridge theorems are

```lean
theorem outsideA_eq_idealRowSum ... :
    outsideA S hbad W u N = idealRowSum ... u

theorem outsideS_eq_idealRowSum_tsum ... :
    outsideS S hbad W V N H = ∑' u : 𝒪,
      V ((eisensteinNorm u : ℝ) / (H : ℝ)) *
        ‖idealRowSum ... u‖ ^ 2
```

The second equality is used at the interface to Poisson summation. Compact
support proves that every row outside `exactRowBall H` contributes zero, so
the initial definitions retain finite sums while the Fourier-analytic API
receives a whole-lattice `tsum`.

## 3. What the reused analytic core proves

After opening the square in the row variable, the formalized argument follows
these main beats:

1. Eisenstein Poisson summation produces sextic Gauss sums.
2. Local Gauss and Jacobi identities reorganize Möbius and the sextic phases
   into cubic Gauss-sum coefficients.
3. Those coefficients are completed to the cubic theta series.
4. Its reflection law, itself built from the lower Poisson and Gauss-sum
   layers, transfers the sum to the dual side.
5. A second Poisson passage exposes quadratic characters, and the quadratic
   sieve controls the remaining dual family.

The lower-level fixed-shell construction is exposed in this repository as

```lean
theorem ActualFixedShellModels.actual_fixedShellModels ... :
    HasFixedShellModels ...
```

It imports `RowCompletion.BranchDecoding`, not the packaged
`RowCompletion.ZeroFreeRegion`. The resulting canonical theta models feed the
mean-square endpoint

```lean
theorem outside_mean_square_of_theta_models_pos ...
    (theta epsilon : ℝ) (htheta : 0 < theta) (hepsilon : 0 < epsilon) :
    ∃ C > 0, ∀ D Z, 1 ≤ Z → ... → ∀ T : Finset 𝒪,
      (∀ z ∈ T, N(z) ≤ Z ^ (1 + theta)) →
      (∀ z ∈ T, z ≠ 0) →
      ∑ z ∈ T, ‖idealRowSum ... z‖ ^ 2
        ≤ C * Z * Z ^ (1 + theta) * Z ^ epsilon
```

The displayed signature suppresses only conductors, fixed bad primes, and
smoothness hypotheses. The important point is that `theta` may be any
positive real number.

## 4. Removing the fixed 1/20 reserve

The original descent encoded a reciprocal step `1 / 1000` and an initial
reserve `1 / 20`. Those values were conveniences for a finite combinatorial
descent, not a conceptual analytic barrier. They are replaced locally by

```lean
class CanonicalDescentScale where
  denominator : ℕ
  denominator_pos : 0 < denominator
  reserve : ℝ
  reserve_pos : 0 < reserve
  short_budget : 50 ≤ reserve * denominator
```

The last field is precisely the numerical budget needed by the short-cube
argument: twenty-five factors of size `Z ^ (1 / denominator)` consume at most
half of the reserve. For any `kappa > 0`,

```lean
CanonicalDescentScale.ofReserve kappa hkappa
```

chooses `denominator = ceil (50 / kappa) + 1`. To prove the mean square at
radius `theta > 0`, the new entry point installs the local scale with
`kappa = theta / 2`. Every descent remains finite; only its finite depth is
allowed to depend on `theta`.

The historical `denominator = 1000`, `reserve = 1 / 20` theorem is retained
as a compatibility entry point. It is not used in the direct `11 / 12`
assembly.

## 5. Sixth-power amplification

For the actual Eisenstein sextic row, the local identity is

\[
  \chi_I(b^6)=\mathbf 1_{(b,I)=1}.
\]

It appears in Lean as `idealSexticRow_sixth_mask`. The public algebraic layer
also records that `b ↦ b ^ 6` has fibers of size at most six:

```lean
theorem sixthPowerFiber_card (s : Finset R) (z : R) :
    (s.filter fun b ↦ b ^ 6 = z).card ≤ 6
```

The final proof intentionally averages over all `b` in a smooth annulus,
rather than restricting `b` to primes. Prime sixth powers illustrate the same
amplification mechanism, but the all-`b` average is the chosen simplification:
it is already strong enough and avoids importing a separate prime-counting
argument.

Put

\[
  Y=Z^\alpha,
  \qquad
  \alpha=\frac{1+\theta}{6}.
\]

Then `N(b ^ 6) <= Z ^ (1 + theta)`, so every amplified row lies inside the
mean-square range. Averaging the coprimality mask over `b` has the deliberate
main term

\[
  \operatorname{totientDensity}(I)
  =\prod_{P\mid I}\left(1-\frac1{N(P)}\right).
\]

Accordingly, the theorem produced by the amplifier bounds the intentionally
totient-weighted Möbius sum, rather than pretending at this stage to recover
the raw Möbius sum:

```lean
theorem outside_totient_moebius_bound_of_mean_square ... :
    ∃ C > 0, ∀ D Z, ... →
      ‖∑ I ∈ outsideIdealsUpTo S D,
        baseChangeWeight chi I * W (N(I) / Z) * totientDensity I‖
      ≤ C * Z ^ ((11 + 5 * theta) / 12 + eta)
```

## 6. The exponent 11/12

Suppose the mean square is written with loss `2 * eta`:

\[
  \sum_z |A_z(Z)|^2\ll Z^{2+\theta+2\eta}.
\]

Cauchy--Schwarz applied to an amplifier of mass `Y` gives a numerator bounded
by

\[
  \sqrt{Y Z^{2+\theta+2\eta}}.
\]

Dividing by the main-term mass `Y` therefore gives

\[
  Z^{(2+\theta-\alpha)/2+\eta}.
\]

Substituting `alpha = (1 + theta) / 6` yields

\[
  \frac{2+\theta-\alpha}{2}
  =\frac{11+5\theta}{12}.
\]

Given the final requested loss `epsilon > 0`, the assembly takes

\[
  \theta=\frac{6\varepsilon}{5},
  \qquad
  \eta=\frac{\varepsilon}{2}.
\]

Then

\[
  \frac{11+5\theta}{12}+\eta
  =\frac{11}{12}+\varepsilon.
\]

This calculation is carried out by
`smoothedWeightedMobiusBound_of_theta_models_pos`; it is the point at which
the symbolic mean square becomes the desired exponent.

## 7. Euler correction and inverse Mellin

The property passed to the final analytic bridge is

```lean
def SmoothedWeightedMobiusBound ... (sigma : ℝ) : Prop :=
  ∀ W, ContDiff ℝ ∞ W →
    Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 1 →
    ∀ epsilon > 0,
      (fun Z ↦ ∑' I, outsideWeight chi S I * W (N(I) / Z))
        =O[atTop] (fun Z ↦ Z ^ (sigma + epsilon))
```

Here `outsideWeight` contains the Möbius factor, the Dirichlet character, the
totient density, and the removal of finitely many bad Euler factors. This is
intentional. The density contributes an Euler product that is analytic and
nonvanishing in the relevant half-plane; `Nonvanishing.lean` restores it as
`eulerCorrection`, while `finiteEulerFactor` restores the omitted local
factors.

The Mellin layer expects an auxiliary cutoff supported in `[1, 2]`. The
public `[1 / 2, 1]` convention is converted by the explicit dilation
`U x = W (2 * x)` and the simultaneous scale change `Z ↦ 2 * Z`; a fixed
dilation does not change the power exponent. Inverse Mellin then gives
analytic continuation of the corrected reciprocal `L`-factor to
`re s > sigma`.

The last two assembled statements are

```lean
theorem actual_smoothedWeightedMobiusBound
    (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) :
    SmoothedWeightedMobiusBound chi (reflectionExcludedPrimes q)
      (11 / 12 : ℝ)

theorem riemannZeta_ne_zero_of_re_gt_elevenTwelfths
    (z : ℂ) (hz : (11 / 12 : ℝ) < z.re) :
    riemannZeta z ≠ 0
```

The first is the complete analytic estimate assembled from the actual theta
models, arbitrary-positive-radius mean square, and all-`b` sixth-power
average. The second specializes the per-character nonvanishing theorem to the
trivial character modulo one and rewrites its `LFunction` as `riemannZeta`.

## 8. Reproducing the build

Fetch cached `.olean` files before asking Lake to compile the project:

```sh
lake exe cache get
lake build
```

The `lakefile.lean` configuration automatically applies OpenAI's vendored
Lean 4.34.1 compatibility patch to the pinned `rellich-kondrachov` dependency
before dependency resolution. It verifies the dependency origin and commit,
recognizes an already-applied patch, and repeats the check after
`lake update`; no manual patch command is required.
