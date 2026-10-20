import ElevenTwelfths.SmoothDyadic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity

/-!
# The sextically twisted Mobius family

This file defines the two quantities used throughout the argument:

* `M`, the smoothly localized sextically twisted Mobius sum;
* `S`, its smoothly localized mean square over the row `h`.

The defining sum deliberately displays its four mathematical ingredients:
the primary condition, Mobius coefficient, sextic twist, and smooth cutoff.
-/

namespace ElevenTwelfths

open scoped BigOperators

variable {𝒪 : Type*}

/--
The smooth dyadic sextically twisted Mobius sum

`M_h(X) = sum_n mu_K(n) chi_n(h) W(norm(n) / X)`.

Because `W` is supported on `[1/2, 1]`, only `X/2 ≤ norm(n) ≤ X` contributes.
The ambient `normBall X` makes this a finite sum from the outset.
-/
noncomputable def M (norm : 𝒪 → ℕ) (normBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (h : 𝒪) (X : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ normBall X,
    if primary n then
      (mobius n : ℂ) * sexticTwist h n * W ((norm n : ℝ) / (X : ℝ))
    else 0

/--
The smooth dyadic mean square

`S(X,H) = sum_h V(norm(h) / H) * |M_h(X)|^2`.

The nonnegative row cutoff `V` is supported on `[1/2, 1]`, so this is a smooth
version of a sum over rows with norm comparable to `H`.  It is definitionally
a finite sum; `S_eq_tsum` supplies the whole-lattice form used by Poisson
summation.
-/
noncomputable def S (norm : 𝒪 → ℕ) (columnBall rowBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) : ℝ :=
  ∑ h ∈ rowBall H,
    V ((norm h : ℝ) / (H : ℝ)) *
      ‖M norm columnBall primary mobius sexticTwist W h X‖ ^ 2

/-- Immediately before Poisson summation, compact support lets us regard the
finite mean square as a `tsum` over the whole row lattice. -/
theorem S_eq_tsum (norm : 𝒪 → ℕ) (columnBall rowBall : ℕ → Finset 𝒪)
    (mem_rowBall : ∀ {B : ℕ} {n : 𝒪}, n ∈ rowBall B ↔ norm n ≤ B)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) :
    S norm columnBall rowBall primary mobius sexticTwist W V X H = ∑' h : 𝒪,
      V ((norm h : ℝ) / (H : ℝ)) *
        ‖M norm columnBall primary mobius sexticTwist W h X‖ ^ 2 := by
  classical
  unfold S
  rw [tsum_eq_sum (s := rowBall H)]
  intro h hu
  have hnorm : H < norm h :=
    Nat.lt_of_not_ge (fun hle ↦ hu (mem_rowBall.mpr hle))
  by_cases hH : H = 0
  · have hV : V 0 = 0 := V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
    simp [hH, hV]
  · have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
    have hratio : (1 : ℝ) < (norm h : ℝ) / (H : ℝ) := by
      rw [lt_div_iff₀ hHpos]
      have hnorm' : (H : ℝ) < norm h := by exact_mod_cast hnorm
      simpa using hnorm'
    rw [V.toSmoothDyadicWeight.eq_zero_of_one_lt hratio, zero_mul]

theorem S_nonnegative (norm : 𝒪 → ℕ) (columnBall rowBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) :
    0 ≤ S norm columnBall rowBall primary mobius sexticTwist W V X H := by
  unfold S
  apply Finset.sum_nonneg
  intro h hu
  exact mul_nonneg (V.apply_nonnegative _) (sq_nonneg _)

@[simp]
theorem M_zero_scale (norm : 𝒪 → ℕ) (normBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (h : 𝒪) :
    M norm normBall primary mobius sexticTwist W h 0 = 0 := by
  classical
  have hW : W 0 = 0 := W.eq_zero_of_lt_half (by norm_num)
  simp [M, hW]

@[simp]
theorem S_zero_row_scale (norm : 𝒪 → ℕ) (columnBall rowBall : ℕ → Finset 𝒪)
    (primary : 𝒪 → Prop) (mobius : 𝒪 → ℤ) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X : ℕ) :
    S norm columnBall rowBall primary mobius sexticTwist W V X 0 = 0 := by
  classical
  have hV : V 0 = 0 :=
    V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
  simp [S, hV]

end ElevenTwelfths
