import ElevenTwelfths.ActualFixedShellModels
import ElevenTwelfths.Nonvanishing
import ElevenTwelfths.SixthPowerMeanSquare

/-!
# The unconditional `11 / 12` zero-free half-plane

This file assembles three independent pieces:

* the actual fixed-shell models copied at the lower `BranchDecoding` layer;
* the arbitrary-positive-radius mean square;
* the direct sixth-power average and Mellin nonvanishing bridge.

It does not import OpenAI's packaged `ZeroFreeRegion` module and does not use
its `23 / 24` `DirichletTarget`.
-/

namespace ElevenTwelfths

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology Classical

open OAI
open OAI.ActualEisensteinCubic
open OAI.CanonicalCoefficientClass
open OAI.CanonicalRowCompletion
open OAI.CompletedGauss hiding O
open OAI.ConcretePrimeRowBridge hiding O
open OAI.CubicEisenstein hiding O
open OAI.InitialMeanSquare hiding O
open OAI.ShortDraftHeckeBridge hiding O
open OAI.SixthPowerAverage

/-- Arbitrarily short mean-square radii, followed by sixth-power averaging,
give the public `[1 / 2, 1]` smoothed Möbius estimate at `11 / 12`.

For a requested loss `epsilon`, take the row-radius parameter
`theta = 6 epsilon / 5` and give the post-square-root mean-square bound the
loss `epsilon / 2`.  Then
`(11 + 5 theta) / 12 + epsilon / 2 = 11 / 12 + epsilon`. -/
theorem smoothedWeightedMobiusBound_of_theta_models_pos
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hbad : OAI.CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P)
    (rho rowBase levelBound : ℝ)
    (hrho : 0 < rho) (hrowBase : 1 < rowBase) (hlevel : 1 ≤ levelBound)
    (hmodels : HasCanonicalThetaModels S
      (conjugateMonoid (normCharacter chi)) rho rowBase levelBound) :
    SmoothedWeightedMobiusBound chi S (11 / 12 : ℝ) := by
  intro W hW hsupp epsilon hepsilon
  let theta : ℝ := 6 * epsilon / 5
  let averageLoss : ℝ := epsilon / 2
  have htheta : 0 < theta := by
    dsimp only [theta]
    linarith
  have haverageLoss : 0 < averageLoss := by
    dsimp only [averageLoss]
    linarith
  obtain ⟨Cmean, hCmean, hmean⟩ :=
    outside_mean_square_of_theta_models_pos chi S hbad hSp
      rho rowBase levelBound hrho hrowBase hlevel hmodels
      W (1 / 2 : ℝ) 1 (by norm_num) hsupp hW theta epsilon htheta hepsilon
  have hmean' : ∀ (D : ℕ) (Z : ℝ), 1 ≤ Z → 1 * Z ≤ D →
      ∀ T : Finset O,
      (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤
        Z ^ (1 + theta : ℝ)) →
      (∀ z ∈ T, z ≠ 0) →
      (∑ z ∈ T,
        ‖idealRowSum (outsideIdealsUpTo S D)
          (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad)
          chi (fun n ↦ W (n / Z)) z‖ ^ 2) ≤
        Cmean * Z ^ ((2 + theta : ℝ) + 2 * averageLoss) := by
    intro D Z hZ hD T hT hT0
    have hZpos : 0 < Z := by linarith
    apply (hmean D Z hZ hD T hT hT0).trans_eq
    calc
      Cmean * Z * Z ^ (1 + theta : ℝ) * Z ^ epsilon =
          Cmean * (Z ^ (1 : ℝ) * Z ^ (1 + theta : ℝ) *
            Z ^ epsilon) := by rw [Real.rpow_one]; ring
      _ = Cmean * Z ^ (1 + (1 + theta) + epsilon) := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
      _ = Cmean * Z ^ ((2 + theta : ℝ) + 2 * averageLoss) := by
        congr 2
        dsimp only [averageLoss]
        ring
  obtain ⟨C, hC, hfinite⟩ := outside_totient_moebius_bound_of_mean_square
    chi S hbad W (1 / 2 : ℝ) 1 (by norm_num) hsupp hW
    theta averageLoss Cmean htheta.le haverageLoss hCmean hmean'
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
  have hZpos : 0 < Z := by linarith
  let D : ℕ := ⌈Z⌉₊
  have hD : 1 * Z ≤ (D : ℝ) := by
    simpa only [one_mul, D] using (Nat.le_ceil Z)
  rw [(ideal_weighted_hasSum chi S W 1 Z hZpos
      (fun x hx ↦ (hsupp hx).2) D hD).tsum_eq,
    Real.norm_of_nonneg (Real.rpow_nonneg hZpos.le _)]
  have h := hfinite D Z hZ hD
  convert h using 1
  all_goals
    dsimp only [theta, averageLoss]
    ring_nf

/-- The actual fixed-shell construction supplies the canonical models needed
by the arbitrary-positive-radius mean square. -/
theorem actual_smoothedWeightedMobiusBound
    (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) :
    SmoothedWeightedMobiusBound chi (reflectionExcludedPrimes q)
      (11 / 12 : ℝ) := by
  obtain ⟨rays, scale, hfixed⟩ :=
    ActualFixedShellModels.exists_actual_fixedShellModels q chi
  have hmodels : HasCanonicalThetaModels (reflectionExcludedPrimes q)
      (conjugateMonoid (normCharacter chi)) 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
    exact hasCanonicalThetaModels_of_fixed_shell_models
      (reflectionExcludedPrimes q) (initialBase chi) rays scale
      1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) hfixed
  exact smoothedWeightedMobiusBound_of_theta_models_pos chi
    (reflectionExcludedPrimes q) (reflectionExcludedPrimes_bad q)
    (reflectionExcludedPrimes_prime q) 1 completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor q)) (by norm_num)
    completedRamifiedStep_gt_one
    (reflectionLevelBound_ge_one q (NeZero.ne q)) hmodels

/-- Direct Dirichlet nonvanishing at `11 / 12`, assembled from the actual
fixed-shell models rather than from a pre-existing zero-free theorem. -/
theorem dirichletL_ne_zero_of_re_gt_elevenTwelfths
    (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
    (z : ℂ) (hz : (11 / 12 : ℝ) < z.re)
    (hpole : ¬ (chi = 1 ∧ z = 1)) :
    chi.LFunction z ≠ 0 :=
  dirichletL_ne_zero_of_smoothedWeightedMobiusBound chi
    (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
    (11 / 12 : ℝ) (by norm_num) (by norm_num)
    (actual_smoothedWeightedMobiusBound q chi) z hz hpole

/-- The unconditional `11 / 12` zero-free half-plane for Riemann zeta. -/
theorem riemannZeta_ne_zero_of_re_gt_elevenTwelfths
    (z : ℂ) (hz : (11 / 12 : ℝ) < z.re) :
    riemannZeta z ≠ 0 :=
  riemannZeta_ne_zero_of_elevenTwelfths_weightedMobiusBound
    (reflectionExcludedPrimes 1) (reflectionExcludedPrimes_prime 1)
    (actual_smoothedWeightedMobiusBound 1 (1 : DirichletCharacter ℂ 1)) z hz

end

end ElevenTwelfths
