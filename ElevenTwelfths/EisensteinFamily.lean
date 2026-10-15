import ElevenTwelfths.Arithmetic
import ElevenTwelfths.SexticFamily

/-!
# The concrete Eisenstein family

This file specializes the generic finite-sum notation to the actual arithmetic
objects fixed in `Arithmetic.lean`. Only the finite norm ball and the sextic
residue symbol remain arguments; their constructions belong in separate
modules, while Mobius, primaryness, and norm are no longer abstract data.
-/

namespace ElevenTwelfths

open scoped BigOperators

/-- The actual smooth Mobius sum, with the arithmetic factors visible. -/
noncomputable def eisensteinA
    (normBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ normBall N,
    if primary n then
      (eisensteinMobius n : ℂ) * sexticTwist u n *
        W ((eisensteinNorm n : ℝ) / (N : ℝ))
    else 0

/-- The actual smooth second moment over Eisenstein rows. -/
noncomputable def eisensteinS
    (columnBall rowBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (N H : ℕ) : ℝ :=
  ∑ u ∈ rowBall H,
    V ((eisensteinNorm u : ℝ) / (H : ℝ)) *
      ‖eisensteinA columnBall sexticTwist W u N‖ ^ 2

theorem eisensteinA_eq_A
    (normBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) :
    eisensteinA normBall sexticTwist W u N =
      A eisensteinNorm normBall primary eisensteinMobius sexticTwist W u N := rfl

theorem eisensteinS_eq_S
    (columnBall rowBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (N H : ℕ) :
    eisensteinS columnBall rowBall sexticTwist W V N H =
      S eisensteinNorm columnBall rowBall primary eisensteinMobius sexticTwist W V N H := rfl

end ElevenTwelfths
