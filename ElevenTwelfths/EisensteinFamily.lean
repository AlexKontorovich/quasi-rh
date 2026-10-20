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
noncomputable def eisensteinM
    (normBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (X : ℕ) : ℂ := by
  classical
  exact ∑ n ∈ normBall X,
    if primary n then
      (μ_K n : ℂ) * sexticTwist u n *
        W ((𝒩 n : ℝ) / (X : ℝ))
    else 0

/-- The actual smooth second moment over Eisenstein rows. -/
noncomputable def eisensteinS
    (columnBall rowBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) : ℝ :=
  ∑ u ∈ rowBall H,
    V ((𝒩 u : ℝ) / (H : ℝ)) *
      ‖eisensteinM columnBall sexticTwist W u X‖ ^ 2

theorem eisensteinM_eq_M
    (normBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (u : 𝒪) (X : ℕ) :
    eisensteinM normBall sexticTwist W u X =
      M 𝒩 normBall primary μ_K sexticTwist W u X := rfl

theorem eisensteinS_eq_S
    (columnBall rowBall : ℕ → Finset 𝒪) (sexticTwist : 𝒪 → 𝒪 → ℂ)
    (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) :
    eisensteinS columnBall rowBall sexticTwist W V X H =
      S 𝒩 columnBall rowBall primary μ_K sexticTwist W V X H := rfl

end ElevenTwelfths
