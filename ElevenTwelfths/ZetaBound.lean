import ElevenTwelfths.ZetaFamily
import ElevenTwelfths.Unconditional

/-!
# The amplified Möbius estimate in the guide's notation

The all-element sixth-power average produces the totient density, rather
than the unweighted sum. We expose that coefficient and specialize the
existing unconditional estimate to zeta; no Dirichlet character parameter
appears in the public statement.
-/

namespace ElevenTwelfths.Zeta

noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics
open OAI OAI.ActualEisensteinCubic
open OAI.SixthPowerAverage
open OAI.ConcretePrimeRowBridge
open OAI.ShortDraftHeckeBridge

/-- The density of amplifier elements coprime to n. -/
abbrev density (n : Ideal 𝒪) : ℂ :=
  ∏ P ∈ OAI.IdealMobiusDivisorSum.primeSupport n,
    (1 - (1 : ℂ) / (Ideal.absNorm P : ℂ))

/-- The weighted Möbius sum actually produced by the smooth amplifier. -/
def densityM (W : SmoothDyadicWeight ℂ) (X : ℝ) : ℂ :=
  ∑' n : Ideal 𝒪, if ∀ P ∈ excludedPrimes, ¬ P ∣ n then
    (UniqueFactorizationMonoid.moebius n : ℂ) * density n *
      W ((Ideal.absNorm n : ℝ) / X) else 0

theorem densityM_eq_outsideWeight (W : SmoothDyadicWeight ℂ) (X : ℝ) :
    densityM W X = ∑' n : Ideal 𝒪,
      outsideWeight (1 : DirichletCharacter ℂ 1) excludedPrimes n *
        W ((Ideal.absNorm n : ℝ) / X) := by
  apply tsum_congr
  intro n
  have hchi : (1 : DirichletCharacter ℂ 1) (Ideal.absNorm n) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [outsideWeight, FiniteSFactor.outsideWeight, weightedMoebius,
    baseChangeWeight, hchi, mul_one, density, totientDensity]
  split_ifs <;> simp

/-- The unconditional amplified bound, with the same [1/2,1] smooth weight
as the family and with its density coefficient visible in densityM. -/
theorem densityM_bound (W : SmoothDyadicWeight ℂ) (ε : ℝ) (hε : 0 < ε) :
    (fun X : ℝ ↦ densityM W X) =O[atTop]
      (fun X : ℝ ↦ X ^ ((11 / 12 : ℝ) + ε)) := by
  simpa only [densityM_eq_outsideWeight] using
    actual_smoothedWeightedMobiusBound 1 (1 : DirichletCharacter ℂ 1)
      W W.contDiff W.support_subset ε hε

end
end ElevenTwelfths.Zeta
