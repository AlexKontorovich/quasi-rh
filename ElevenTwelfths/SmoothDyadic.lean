import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Smooth dyadic weights

The analytic sums in this project are localized by smooth functions supported
on `[1/2, 1]`.  Keeping the support interval fixed makes the scale parameter
visible in the argument of the weight: `W (x / X)` localizes `x` to
`[X/2, X]`.
-/

namespace ElevenTwelfths

open Set
open scoped ContDiff

/-- A smooth function supported on the standard dyadic interval `[1/2, 1]`. -/
@[ext]
structure SmoothDyadicWeight (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  contDiff : ContDiff ℝ ∞ toFun
  support_subset : Function.support toFun ⊆ Icc (1 / 2) 1

namespace SmoothDyadicWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (SmoothDyadicWeight E) fun _ ↦ ℝ → E :=
  ⟨SmoothDyadicWeight.toFun⟩

/-- A dyadic weight vanishes away from `[1/2, 1]`. -/
theorem eq_zero_of_not_mem (W : SmoothDyadicWeight E) {x : ℝ}
    (hx : x ∉ Icc (1 / 2 : ℝ) 1) :
    W x = 0 := by
  by_contra hne
  exact hx (W.support_subset hne)

theorem eq_zero_of_lt_half (W : SmoothDyadicWeight E) {x : ℝ} (hx : x < 1 / 2) : W x = 0 := by
  apply W.eq_zero_of_not_mem
  simp only [mem_Icc, not_and_or]
  exact Or.inl (not_le.mpr hx)

theorem eq_zero_of_one_lt (W : SmoothDyadicWeight E) {x : ℝ} (hx : 1 < x) : W x = 0 := by
  apply W.eq_zero_of_not_mem
  simp only [mem_Icc, not_and_or]
  exact Or.inr (not_le.mpr hx)

end SmoothDyadicWeight

/-- A real smooth dyadic weight suitable for weighting a mean square. -/
@[ext]
structure SmoothDyadicCutoff extends SmoothDyadicWeight ℝ where
  nonnegative : ∀ x, 0 ≤ toFun x

namespace SmoothDyadicCutoff

instance : CoeFun SmoothDyadicCutoff fun _ ↦ ℝ → ℝ :=
  ⟨fun V ↦ V.toFun⟩

theorem apply_nonnegative (V : SmoothDyadicCutoff) (x : ℝ) : 0 ≤ V x :=
  V.nonnegative x

end SmoothDyadicCutoff

end ElevenTwelfths
