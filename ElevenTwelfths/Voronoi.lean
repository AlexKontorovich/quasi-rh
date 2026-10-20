import ElevenTwelfths.ThetaSums
import ElevenTwelfths.ActualFixedShellModels

/-!
# Voronoi for the completed sums in the guide

This specializes the actual fixed-shell identity to conductor one and the
public smooth dyadic weights. Auxiliary ray twists, cusp branches, common
divisors and local masks are still present: suppressing them is appropriate
in the introductory heuristic, but not in the exact theorem.

The left side uses the very same thetaSum as cube inversion. The right side
is the upstream reflected fiber, not a newly postulated coefficient system.
-/

namespace ElevenTwelfths.Theta

noncomputable section
open scoped BigOperators Classical
open OAI OAI.ActualEisensteinCubic
open OAI.CompletedGauss hiding O
open OAI.CanonicalRowCompletion
open OAI.CanonicalRowCompletion.ActualFiber
open OAI.CanonicalCoefficientClass
open OAI.CubicEisenstein hiding O

local instance : Fintype (O ⧸ Ideal.span {reflectionConductor 1}) := by
  let : Finite (O ⧸ Ideal.span {reflectionConductor 1}) :=
    OAI.ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero 1 (by norm_num))
  exact Fintype.ofFinite _

variable (m : O) (hm : m ≠ 0)
    (rows : Finset (Ideal O)) (R F : Ideal O) (hR : R ≠ 0)
    (hF : Squarefree F) (hrows : ∀ I ∈ rows, I ≠ 0) (v : Oˣ)

/-- The exact cubic Voronoi identity, specialized to zeta and [1/2,1].
Its row-dependent source twist and reflected cusp fiber remain explicit. -/
theorem theta_voronoi
    (Ψ : O →* ℂ) (hperiod : FactorsModulo (fixedBaseConductor 1) Ψ)
    (hΨ : ∀ n, ‖Ψ n‖ ≤ 1)
    (L : ℝ) (hshell : ∀ I ∈ rows,
      L / 2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ L)
    (ℓ : RowIndex 1 m rows R F)
    (W : SmoothDyadicWeight ℂ) (X : ℝ) (hX : 0 < X) :
    thetaSum
        (rowTwist Ψ (maskElement 1 m)
          (OAI.ConcretePrimeRowBridge.idealGenerator F)
          (v.val * OAI.ConcretePrimeRowBridge.idealGenerator ℓ.val)) W X =
      ActualFixedShellModels.actualReflectionScale *
        (reflectedFiber 1 (by norm_num) m hm rows R F hR hF hrows v L Ψ hΨ).idealValue
          W X 1 completedRamifiedStep (rowResidualPart ℓ.val (maskIdeal 1 m F)) := by
  exact ActualFixedShellModels.completedT_eq_reflectedFiber_idealValue_local
    1 (by norm_num) m hm rows R F hR hF hrows v Ψ hperiod hΨ L hshell ℓ
    W (1 / 2) 1 (by norm_num) W.support_subset W.contDiff X hX

end
end ElevenTwelfths.Theta
