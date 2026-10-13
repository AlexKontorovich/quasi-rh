# The 11/12 argument, with Lean landmarks

This document will be the short, human-readable route through the proof. Each
section will contain:

1. the mathematical idea;
2. the precise estimate used by the next section;
3. the corresponding Lean declaration; and
4. a brief note about formalization details that are mathematically invisible
   on paper.

## Proposed route

1. Smoothed ideal-Mobius sums and the nonvanishing criterion.
2. The sextically twisted family.
3. Sixth-power amplification.
4. Opening the mean square and Poisson summation.
5. The Gauss--Jacobi identity.
6. Cubic theta coefficients and the reflection estimate.
7. Closing the mean-square recurrence.
8. Extracting the exponent \(11/12\).
9. Passing from the Mobius estimate to \(L_K(s,\nu)\ne0\).

The exposition should emphasize why each transformation is introduced, while
the Lean source records the local conditions, conductors, coprimality
hypotheses, smooth weights, and uniformity of constants in full.

## 1. The family and its mean square

We use a fixed smooth weight `W : ℝ → ℂ` supported on `[1, 2]`. Thus
`W (norm n / N)` restricts the column variable to `norm n ∼ N`. A second,
nonnegative smooth weight `V : ℝ → ℝ`, also supported on `[1, 2]`, restricts
the row variable to `norm u ∼ H`.

The corresponding Lean definitions are:

```lean
noncomputable def A (data : SexticMobiusData 𝒪)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ data.normBall (2 * N),
    if data.admissible n then
      data.coefficient u n * W ((data.norm n : ℝ) / (N : ℝ))
    else 0

noncomputable def S (data : SexticMobiusData 𝒪)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑ u ∈ data.normBall (2 * H),
    V ((data.norm u : ℝ) / (H : ℝ)) * ‖data.A W u N‖ ^ 2
```

Here `data.coefficient u n` expands to

```lean
(data.mobius n : ℂ) * data.heckeChar n * data.sexticTwist u n
```

The `normBall` bounds do not impose a sharp analytic cutoff: they merely give
Lean a finite ambient set. The actual localization is supplied by `W` and `V`.
