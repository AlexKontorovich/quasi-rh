import OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage

/-!
# From the sextic mean square to the `11 / 12` Möbius bound

This module is the direct sixth-power amplifier used after the analytic
mean-square argument. The mean-square estimate is an explicit hypothesis.

For `alpha = (1 + theta) / 6`, average the rows `A (b ^ 6)` over
`Norm b \asymp N ^ alpha`.  Cauchy--Schwarz costs the square root of the
number of rows, while the zero Fourier mode contributes a factor
`N ^ alpha`.  Thus

`(2 + theta - alpha) / 2 = (11 + 5 * theta) / 12`.
-/

namespace ElevenTwelfths

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory

open OAI
open OAI.ActualEisensteinCubic
open OAI.ConcretePrimeRowBridge hiding O
open OAI.EisensteinSchwartzPoisson hiding O
open OAI.ConcreteTraceCRT OAI.ShortDraftHeckeBridge
open OAI.QuadraticInitialBound hiding O
open OAI.InitialMeanSquare
open OAI.SixthPowerAverage

/--
A symbolic-`theta` form of the sixth-power averaging argument.

The hypothesis `hmean` is the sole deep analytic input.  It says that every
finite collection of nonzero sextic rows of norm at most `Z ^ (1 + theta)`
has second moment `O(Z ^ (2 + theta + 2 * epsilon))`.  The conclusion is the
smooth weighted Eisenstein--Möbius bound with exponent
`(11 + 5 * theta) / 12 + epsilon`.
-/
theorem outside_totient_moebius_bound_of_mean_square
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal OAI.ActualEisensteinCubic.O))
    (hbad : OAI.CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (W : ℝ → ℂ) (a b : ℝ) (_ha : 0 < a)
    (hsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W)
    (theta epsilon Cmean : ℝ)
    (htheta : 0 ≤ theta) (hepsilon : 0 < epsilon)
    (hCmean : 0 < Cmean)
    (hmean : ∀ (D : ℕ) (Z : ℝ), 1 ≤ Z → b * Z ≤ D →
      ∀ T : Finset OAI.ActualEisensteinCubic.O,
      (∀ z ∈ T,
        (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z ^ (1 + theta : ℝ)) →
      (∀ z ∈ T, z ≠ 0) →
      (∑ z ∈ T,
        ‖idealRowSum (outsideIdealsUpTo S D)
          (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad)
          chi (fun n ↦ W (n / Z)) z‖ ^ 2) ≤
        Cmean * Z ^ ((2 + theta : ℝ) + 2 * epsilon)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (Z : ℝ), 1 ≤ Z → b * Z ≤ D →
      ‖∑ I ∈ outsideIdealsUpTo S D,
        baseChangeWeight chi I * W ((Ideal.absNorm I : ℝ) / Z) *
          totientDensity I‖ ≤
        C * Z ^ (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  obtain ⟨V, hV, hVs, hV0, hVhat⟩ := exists_averaging_test
  obtain ⟨Cerror, hCerror, herror⟩ :=
    average_remainder_small_power epsilon hepsilon
  have hWcompact : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  let Ws : 𝓢(ℝ, ℂ) := hWcompact.toSchwartzMap hW
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ := max 1 b
  let Error : ℝ := Cerror * G * pvControl V * B ^ (1 + epsilon)
  let Average : ℝ := Real.sqrt (768 * Cmean)
  let alpha : ℝ := (1 + theta) / 6
  let targetExponent : ℝ := (11 + 5 * theta) / 12 + epsilon
  let averageExponent : ℝ := alpha + targetExponent
  let C : ℝ := (Average + Error) / ‖paperRadialFourier V 0‖
  have hG : 0 ≤ G := apply_nonneg _ _
  have hB : 1 ≤ B := le_max_left _ _
  have hError : 0 ≤ Error :=
    mul_nonneg (mul_nonneg (mul_nonneg hCerror.le hG)
      (pvControl_nonneg V)) (by positivity)
  have hAverage : 0 < Average := Real.sqrt_pos.mpr (by positivity)
  have hhat : 0 < ‖paperRadialFourier V 0‖ := norm_pos_iff.mpr hVhat
  have halpha : 0 ≤ alpha := by
    dsimp [alpha]
    linarith
  refine ⟨C, div_pos (by linarith) hhat, ?_⟩
  intro D Z hZ hD
  have hZpos : 0 < Z := by linarith
  let Y : ℝ := Z ^ alpha
  have hY : 1 ≤ Y := Real.one_le_rpow hZ halpha
  have hYpos : 0 < Y := by linarith
  let F := outsideIdealsUpTo S D
  let A : OAI.ActualEisensteinCubic.O → ℂ :=
    idealRowSum F (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) chi (fun n ↦ W (n / Z))
  have hYpower : Y ^ 6 = Z ^ (1 + theta : ℝ) := by
    dsimp only [Y, alpha]
    rw [← Real.rpow_mul_natCast hZpos.le]
    congr 1
    ring
  have hsecondMoment :
      (∑ z ∈ (averagingRows Y).image (fun x ↦ x ^ 6), ‖A z‖ ^ 2) ≤
        Cmean * Z ^ ((2 + theta : ℝ) + 2 * epsilon) := by
    apply hmean D Z hZ hD
    · intro z hz
      have hnorm := (averagingRows_power_norm Y hY hz).2
      simpa only [hYpower] using hnorm
    · intro z hz
      exact (averagingRows_power_norm Y hY hz).1
  have havgSquare :=
    (average_tsum_cauchy V hV hVs hV0 Y hY A).trans
      (mul_le_mul_of_nonneg_left hsecondMoment (by positivity : 0 ≤ 768 * Y))
  have haverageIdentity :
      768 * Y * (Cmean * Z ^ ((2 + theta : ℝ) + 2 * epsilon)) =
        (Average * Z ^ averageExponent) ^ 2 := by
    dsimp only [Y, Average]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 768 * Cmean),
      ← Real.rpow_mul_natCast hZpos.le]
    calc
      _ = (768 * Cmean) *
          (Z ^ alpha * Z ^ ((2 + theta : ℝ) + 2 * epsilon)) := by
            ring
      _ = (768 * Cmean) *
          Z ^ (alpha + ((2 + theta : ℝ) + 2 * epsilon)) := by
            rw [← Real.rpow_add hZpos]
      _ = _ := by
        congr 2
        dsimp [averageExponent, targetExponent, alpha]
        ring
  rw [haverageIdentity] at havgSquare
  have havg :
      ‖∑' z : OAI.ActualEisensteinCubic.O,
        V (‖eisEmbedding z‖ ^ 2 / Y) * A (z ^ 6)‖ ≤
        Average * Z ^ averageExponent :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havgSquare
  have hremainder :
      ‖∑ I ∈ F,
        baseChangeWeight chi I * W ((Ideal.absNorm I : ℝ) / Z) *
          maskedPrincipalRemainder (fun i : primePool F ↦ i.val)
            (idealSupport F I) V Y‖ ≤
        Error * Z ^ (1 + epsilon) := by
    have hBZ : 1 ≤ B * Z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hZ)]
    have hbound := herror F (outsideIdealsUpTo_ne_bot S D) chi
      (fun n ↦ W (n / Z)) V Y (B * Z) G hYpos hBZ hG
      (fun n ↦ Ws.norm_le_seminorm ℝ (n / Z)) (by
        intro I hI hn
        have hsupportUpper := (hsupport hn).2
        exact ((div_le_iff₀ hZpos).mp hsupportUpper).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 b) hZpos.le))
    calc
      _ ≤ Cerror * G * pvControl V * (B * Z) ^ (1 + epsilon) := hbound
      _ = Error * Z ^ (1 + epsilon) := by
        rw [Real.mul_rpow (by linarith : 0 ≤ B) hZpos.le]
        dsimp only [Error]
        ring
  have herrorExponent : Z ^ (1 + epsilon) ≤ Z ^ averageExponent :=
    Real.rpow_le_rpow_of_exponent_le hZ (by
      dsimp [averageExponent, targetExponent, alpha]
      linarith)
  have hmain := totient_sum_normalized_bound F
    (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad) chi
    (fun n ↦ W (n / Z)) V Y hYpos
  have hbound :
      Y * ‖paperRadialFourier V 0‖ *
          ‖∑ I ∈ F,
            baseChangeWeight chi I * W ((Ideal.absNorm I : ℝ) / Z) *
              totientDensity I‖ ≤
        (Average + Error) * Z ^ averageExponent := by
    apply hmain.trans
    have hsum := add_le_add havg
      (hremainder.trans (mul_le_mul_of_nonneg_left herrorExponent hError))
    simpa only [add_mul] using hsum
  have hfactor : Z ^ averageExponent = Y * Z ^ targetExponent := by
    dsimp only [averageExponent, Y]
    rw [← Real.rpow_add hZpos]
  apply (mul_le_mul_iff_right₀ (mul_pos hYpos hhat)).mp
  apply hbound.trans_eq
  rw [hfactor]
  dsimp only [C, targetExponent]
  field_simp [hhat.ne']

end

end ElevenTwelfths
