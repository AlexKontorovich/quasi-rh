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

