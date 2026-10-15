import ElevenTwelfths.Arithmetic
import ElevenTwelfths.SmoothDyadic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Smooth partial sums of the ideal Möbius function

`M W u N` sums over nonzero integral ideals coprime to `(6)`.
`S W V N H` sums over elements of the Eisenstein lattice, not ideals or
primary representatives. All arithmetic objects are fixed in `Arithmetic`.
The finite row sum equals a whole-lattice sum by compact support.
No analytic estimate is asserted here.
-/

namespace ElevenTwelfths

open scoped BigOperators

/-- The smooth sextically twisted partial sum `M_u(N)` of `μ_K`. -/
noncomputable def M (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ :=
  ∑ n ∈ idealBall N,
    (mobiusK n : ℂ) * chi n u * W ((Ideal.absNorm n : ℝ) / (N : ℝ))

/-- The smooth mean square over elements, without a primary or coprimality filter. -/
noncomputable def S (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑ u ∈ rowBall H, V ((elementNorm u : ℝ) / (H : ℝ)) * ‖M W u N‖ ^ 2

/-- Compact support exposes the whole lattice for Poisson summation. -/
theorem S_eq_tsum (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : S W V N H =
      ∑' u : 𝒪, V ((elementNorm u : ℝ) / (H : ℝ)) * ‖M W u N‖ ^ 2 := by
  classical
  unfold S
  rw [tsum_eq_sum (s := rowBall H)]
  intro u hu
  have hnorm : H < elementNorm u :=
    Nat.lt_of_not_ge (fun hle ↦ hu (mem_rowBall.mpr hle))
  by_cases hH : H = 0
  · have hV : V 0 = 0 := V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
    simp [hH, hV]
  · have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
    have hratio : (1 : ℝ) < (elementNorm u : ℝ) / (H : ℝ) := by
      rw [lt_div_iff₀ hHpos]
      have hnorm' : (H : ℝ) < elementNorm u := by exact_mod_cast hnorm
      simpa using hnorm'
    rw [V.toSmoothDyadicWeight.eq_zero_of_one_lt hratio, zero_mul]

theorem S_nonnegative (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : 0 ≤ S W V N H := by
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (V.apply_nonnegative _) (sq_nonneg _)

@[simp]
theorem M_zero_scale (W : SmoothDyadicWeight ℂ) (u : 𝒪) : M W u 0 = 0 := by
  have hW : W 0 = 0 := W.eq_zero_of_lt_half (by norm_num)
  simp [M, hW]

@[simp]
theorem S_zero_row_scale (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N : ℕ) : S W V N 0 = 0 := by
  have hV : V 0 = 0 := V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
  simp [S, hV]

end ElevenTwelfths
