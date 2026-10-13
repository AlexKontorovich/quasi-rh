import ElevenTwelfths.SmoothDyadic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity

/-!
# The sextically twisted Mobius family

This file defines the two quantities used throughout the argument:

* `A data W u N`, the smoothly localized sextically twisted Mobius sum;
* `S data W V N H`, its smoothly localized mean square over the row `u`.

The arithmetic is packaged in `SexticMobiusData`.  This lets us fix the analytic
shape of the proof before constructing primary Eisenstein generators, ideal
Mobius, Hecke characters, and the sextic residue symbol.
-/

namespace ElevenTwelfths

open scoped BigOperators

/-- Arithmetic input for the sextically twisted Mobius family.

The type `𝒪` will eventually be the primary Eisenstein integers.  The field
`normBall` is included so that all dyadic sums are definitionally finite;
`mem_normBall` says that it really enumerates the elements of bounded norm.
-/
structure SexticMobiusData (𝒪 : Type*) [DecidableEq 𝒪] where
  norm : 𝒪 → ℕ
  normBall : ℕ → Finset 𝒪
  mem_normBall : ∀ {B : ℕ} {x : 𝒪}, x ∈ normBall B ↔ norm x ≤ B
  admissible : 𝒪 → Prop
  mobius : 𝒪 → ℤ
  heckeChar : 𝒪 → ℂ
  sexticTwist : 𝒪 → 𝒪 → ℂ

namespace SexticMobiusData

variable {𝒪 : Type*} [DecidableEq 𝒪]

/-- The summand in `A_u(N)`, before applying the smooth dyadic weight. -/
def coefficient (data : SexticMobiusData 𝒪) (u n : 𝒪) : ℂ :=
  (data.mobius n : ℂ) * data.heckeChar n * data.sexticTwist u n

/--
The smooth dyadic sextically twisted Mobius sum

`A_u(N) = sum_n mu_K(n) nu(n) chi_n(u) W(norm(n) / N)`.

Because `W` is supported on `[1, 2]`, only `N ≤ norm(n) ≤ 2N` contributes.
The ambient `normBall (2 * N)` makes this a finite sum from the outset.
-/
noncomputable def A (data : SexticMobiusData 𝒪) (W : SmoothDyadicWeight ℂ)
    (u : 𝒪) (N : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ data.normBall (2 * N),
    if data.admissible n then
      data.coefficient u n * W ((data.norm n : ℝ) / (N : ℝ))
    else 0

/--
The smooth dyadic mean square

`S(N,H) = sum_u V(norm(u) / H) * |A_u(N)|^2`.

The nonnegative row cutoff `V` is supported on `[1, 2]`, so this is a smooth
version of a sum over rows with norm comparable to `H`.
-/
noncomputable def S (data : SexticMobiusData 𝒪) (W : SmoothDyadicWeight ℂ)
    (V : SmoothDyadicCutoff) (N H : ℕ) : ℝ :=
  ∑ u ∈ data.normBall (2 * H),
    V ((data.norm u : ℝ) / (H : ℝ)) * ‖data.A W u N‖ ^ 2

theorem S_nonnegative (data : SexticMobiusData 𝒪) (W : SmoothDyadicWeight ℂ)
    (V : SmoothDyadicCutoff) (N H : ℕ) : 0 ≤ data.S W V N H := by
  unfold S
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (V.apply_nonnegative _) (sq_nonneg _)

@[simp]
theorem A_zero_scale (data : SexticMobiusData 𝒪) (W : SmoothDyadicWeight ℂ) (u : 𝒪) :
    data.A W u 0 = 0 := by
  classical
  have hW : W 0 = 0 := W.eq_zero_of_lt_one (by norm_num)
  simp [A, hW]

@[simp]
theorem S_zero_row_scale (data : SexticMobiusData 𝒪) (W : SmoothDyadicWeight ℂ)
    (V : SmoothDyadicCutoff) (N : ℕ) : data.S W V N 0 = 0 := by
  classical
  have hV : V 0 = 0 :=
    V.toSmoothDyadicWeight.eq_zero_of_lt_one (by norm_num)
  simp [S, hV]

end SexticMobiusData

end ElevenTwelfths
