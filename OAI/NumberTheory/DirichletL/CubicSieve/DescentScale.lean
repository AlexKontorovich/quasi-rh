-- Modified in quasi-rh-eleven-twelfths to parameterize the canonical descent scale.
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

noncomputable section

/-- Numerical data for the finite canonical descent.

`denominator` is the reciprocal step size, while `reserve` is the initial
power saving.  The last field is exactly the compatibility needed by the
short-cube argument: twenty-five factors of size `Z^(1 / denominator)` spend
at most half of the reserve.  There is deliberately no global instance;
public theorems install the scale they need locally. -/
class CanonicalDescentScale where
  denominator : ℕ
  denominator_pos : 0 < denominator
  reserve : ℝ
  reserve_pos : 0 < reserve
  short_budget : 50 ≤ reserve * denominator

namespace CanonicalDescentScale

def step (scale : CanonicalDescentScale) : ℝ :=
  1 / (scale.denominator : ℝ)

def rankCap (scale : CanonicalDescentScale) : ℕ :=
  3 * scale.denominator

def shortMargin (scale : CanonicalDescentScale) : ℝ :=
  scale.reserve / 2

def fixedFactorExponent (scale : CanonicalDescentScale) : ℝ :=
  scale.reserve / 4

def strictReserve (scale : CanonicalDescentScale) : ℝ :=
  3 * scale.reserve / 4

theorem denominator_real_pos (scale : CanonicalDescentScale) :
    (0 : ℝ) < scale.denominator := by
  exact_mod_cast scale.denominator_pos

theorem denominator_real_ge_one (scale : CanonicalDescentScale) :
    (1 : ℝ) ≤ scale.denominator := by
  exact_mod_cast scale.denominator_pos

theorem step_pos (scale : CanonicalDescentScale) : 0 < scale.step := by
  exact div_pos zero_lt_one scale.denominator_real_pos

theorem step_le_one (scale : CanonicalDescentScale) : scale.step ≤ 1 := by
  rw [step, div_le_one scale.denominator_real_pos]
  exact scale.denominator_real_ge_one

theorem reserve_nonneg (scale : CanonicalDescentScale) : 0 ≤ scale.reserve :=
  scale.reserve_pos.le

theorem shortMargin_pos (scale : CanonicalDescentScale) :
    0 < scale.shortMargin := by
  exact div_pos scale.reserve_pos (by norm_num)

theorem fixedFactorExponent_pos (scale : CanonicalDescentScale) :
    0 < scale.fixedFactorExponent := by
  exact div_pos scale.reserve_pos (by norm_num)

theorem fixedFactorExponent_le_shortMargin (scale : CanonicalDescentScale) :
    scale.fixedFactorExponent ≤ scale.shortMargin := by
  unfold fixedFactorExponent shortMargin
  linarith [scale.reserve_pos]

theorem rankCap_pos (scale : CanonicalDescentScale) : 0 < scale.rankCap := by
  unfold rankCap
  exact Nat.mul_pos (by norm_num) scale.denominator_pos

theorem strictReserve_pos (scale : CanonicalDescentScale) :
    0 < scale.strictReserve := by
  unfold strictReserve
  exact div_pos (mul_pos (by norm_num) scale.reserve_pos) (by norm_num)

/-- The numerical hypothesis used by the short-cube algebra. -/
theorem short_spend (scale : CanonicalDescentScale) :
    25 * scale.step ≤ scale.shortMargin := by
  have hq := scale.denominator_real_pos
  have hb : (50 : ℝ) ≤ scale.reserve * (scale.denominator : ℝ) := by
    exact scale.short_budget
  rw [step, shortMargin]
  calc
    25 * (1 / (scale.denominator : ℝ)) = 25 / scale.denominator := by ring
    _ ≤ scale.reserve / 2 := (div_le_iff₀ hq).2 (by nlinarith)

theorem reserve_decomposition (scale : CanonicalDescentScale) :
    scale.strictReserve - scale.fixedFactorExponent = scale.shortMargin := by
  unfold strictReserve fixedFactorExponent shortMargin
  ring

/-- A scale with prescribed positive reserve.  The extra `+ 1` makes the
denominator positive without a case split. -/
def ofReserve (κ : ℝ) (hκ : 0 < κ) : CanonicalDescentScale where
  denominator := ⌈50 / κ⌉₊ + 1
  denominator_pos := by omega
  reserve := κ
  reserve_pos := hκ
  short_budget := by
    have hceil : 50 / κ ≤ (⌈50 / κ⌉₊ : ℝ) := Nat.le_ceil _
    have hadd : (⌈50 / κ⌉₊ : ℝ) ≤ (⌈50 / κ⌉₊ + 1 : ℕ) := by
      exact_mod_cast Nat.le_add_right ⌈50 / κ⌉₊ 1
    have hdiv : 50 / κ ≤ (⌈50 / κ⌉₊ + 1 : ℕ) := hceil.trans hadd
    have := (div_le_iff₀ hκ).1 hdiv
    push_cast at this ⊢
    nlinarith

/-- Historical parameters, exposed as a value rather than a global instance. -/
def historical : CanonicalDescentScale where
  denominator := 1000
  denominator_pos := by norm_num
  reserve := (1 : ℝ) / 20
  reserve_pos := by norm_num
  short_budget := by norm_num

end CanonicalDescentScale

end

end OAI
