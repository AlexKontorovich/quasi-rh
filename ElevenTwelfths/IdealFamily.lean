import ElevenTwelfths.IdealArithmetic
import ElevenTwelfths.SmoothDyadic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Smooth partial sums of the ideal Möbius function

`M W h X` sums over nonzero integral ideals coprime to `(6)`.
`S W V X H` sums over elements of the Eisenstein lattice, not ideals or
primary representatives. All arithmetic objects are fixed in `IdealArithmetic`.
The finite row sum equals a whole-lattice sum by compact support.
No analytic estimate is asserted here.
-/

namespace ElevenTwelfths.IdealFamily

open scoped BigOperators

/-- The smooth sextically twisted partial sum `M_h(X)` of `μ_K`. -/
noncomputable def M (W : SmoothDyadicWeight ℂ) (h : 𝒪) (X : ℕ) : ℂ :=
  ∑ n ∈ idealBall X,
    (mobiusK n : ℂ) * chi n h * W ((Ideal.absNorm n : ℝ) / (X : ℝ))

/-- The smooth mean square over elements, without a primary or coprimality filter. -/
noncomputable def S (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) : ℝ :=
  ∑ h ∈ rowBall H, V ((elementNorm h : ℝ) / (H : ℝ)) * ‖M W h X‖ ^ 2

/-- Compact support exposes the whole lattice for Poisson summation. -/
theorem S_eq_tsum (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) : S W V X H =
      ∑' h : 𝒪, V ((elementNorm h : ℝ) / (H : ℝ)) * ‖M W h X‖ ^ 2 := by
  classical
  unfold S
  rw [tsum_eq_sum (s := rowBall H)]
  intro h hu
  have hnorm : H < elementNorm h :=
    Nat.lt_of_not_ge (fun hle ↦ hu (mem_rowBall.mpr hle))
  by_cases hH : H = 0
  · have hV : V 0 = 0 := V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
    simp [hH, hV]
  · have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
    have hratio : (1 : ℝ) < (elementNorm h : ℝ) / (H : ℝ) := by
      rw [lt_div_iff₀ hHpos]
      have hnorm' : (H : ℝ) < elementNorm h := by exact_mod_cast hnorm
      simpa using hnorm'
    rw [V.toSmoothDyadicWeight.eq_zero_of_one_lt hratio, zero_mul]

theorem S_nonnegative (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) : 0 ≤ S W V X H := by
  apply Finset.sum_nonneg
  intro h hu
  exact mul_nonneg (V.apply_nonnegative _) (sq_nonneg _)

@[simp]
theorem M_zero_scale (W : SmoothDyadicWeight ℂ) (h : 𝒪) : M W h 0 = 0 := by
  have hW : W 0 = 0 := W.eq_zero_of_lt_half (by norm_num)
  simp [M, hW]

@[simp]
theorem S_zero_row_scale (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X : ℕ) : S W V X 0 = 0 := by
  have hV : V 0 = 0 := V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
  simp [S, hV]

end ElevenTwelfths.IdealFamily
