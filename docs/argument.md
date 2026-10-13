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

We use a fixed smooth weight `W : ℝ → ℂ` supported on `[1/2, 1]`. Thus
`W (norm n / N)` restricts the column variable to `N/2 ≤ norm n ≤ N`. A
second, nonnegative smooth weight `V : ℝ → ℝ`, also supported on `[1/2, 1]`,
restricts the row variable to `H/2 ≤ norm u ≤ H`.

The corresponding Lean definitions are:

```lean
noncomputable def A (data : SexticMobiusData 𝒪)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ data.normBall N,
    if data.admissible n then
      data.coefficient u n * W ((data.norm n : ℝ) / (N : ℝ))
    else 0

noncomputable def S (data : SexticMobiusData 𝒪)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑' u : 𝒪,
    V ((data.norm u : ℝ) / (H : ℝ)) * ‖data.A W u N‖ ^ 2
```

Here `data.coefficient u n` expands to

```lean
(data.mobius n : ℂ) * data.heckeChar n * data.sexticTwist u n
```

The column sum is definitionally finite over `normBall N`.  The mean square is
instead a `tsum` over the whole row lattice, which is the form needed for
Poisson summation.  Compact support gives the checked identity

```lean
theorem S_eq_sum_normBall ... :
    data.S W V N H = ∑ u ∈ data.normBall H,
      V ((data.norm u : ℝ) / (H : ℝ)) * ‖data.A W u N‖ ^ 2
```

Thus the analytic cutoff remains smooth, while the upper endpoints of its
finite realization are the clean parameters `N` and `H`.
