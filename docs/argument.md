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
9. Passing from the Mobius estimate to zeta nonvanishing.

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
noncomputable def A (norm : 𝒪 → ℕ) (normBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ)
    (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ normBall N,
    if primary n then
      (mobius n : ℂ) * sexticTwist u n * W ((norm n : ℝ) / (N : ℝ))
    else 0

noncomputable def S (norm : 𝒪 → ℕ) (normBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ)
    (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑ u ∈ normBall H,
    V ((norm u : ℝ) / (H : ℝ)) *
      ‖A norm normBall primary mobius sexticTwist W u N‖ ^ 2
```

For Eisenstein integers, `primary n` will mean the standard congruence
`lambda ^ 2 ∣ n - 1`.  Keeping it visible in the summation records that we
sum over the distinguished primary generator of each admissible ideal rather
than over all six associates.

Both quantities are definitionally finite: the column sum uses `normBall N`
and the mean square uses `normBall H`. Immediately before Poisson summation,
compact support gives the checked identity

```lean
theorem S_eq_tsum ... :
    S norm normBall primary mobius sexticTwist W V N H = ∑' u : 𝒪,
      V ((norm u : ℝ) / (H : ℝ)) *
        ‖A norm normBall primary mobius sexticTwist W u N‖ ^ 2
```

This isolates `tsum` at exactly the point where the Poisson API requires it,
while the basic definitions retain the clean finite bounds `N` and `H`.
