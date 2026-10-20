import OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage

/-!
# From the sextic mean square to the `11 / 12` Möbius bound

This module is the direct sixth-power amplifier used after the analytic
mean-square argument. The mean-square estimate is an explicit hypothesis.

For `alpha = (1 + theta) / 6`, average the rows `A (b ^ 6)` over
`Norm b \asymp X ^ alpha`.  Cauchy--Schwarz costs the square root of the
number of rows, while the zero Fourier mode contributes a factor
`X ^ alpha`.  Thus

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
finite collection of nonzero sextic rows of norm at most `X ^ (1 + theta)`
has second moment `O(X ^ (2 + theta + 2 * epsilon))`.  The conclusion is the
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
    (hmean : ∀ (D : ℕ) (X : ℝ), 1 ≤ X → b * X ≤ D →
      ∀ T : Finset OAI.ActualEisensteinCubic.O,
      (∀ h ∈ T,
        (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ X ^ (1 + theta : ℝ)) →
      (∀ h ∈ T, h ≠ 0) →
      (∑ h ∈ T,
        ‖idealRowSum (outsideIdealsUpTo S D)
          (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad)
          chi (fun n ↦ W (n / X)) h‖ ^ 2) ≤
        Cmean * X ^ ((2 + theta : ℝ) + 2 * epsilon)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (X : ℝ), 1 ≤ X → b * X ≤ D →
      ‖∑ n ∈ outsideIdealsUpTo S D,
        baseChangeWeight chi n * W ((Ideal.absNorm n : ℝ) / X) *
          totientDensity n‖ ≤
        C * X ^ (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  obtain ⟨V, hV, hVs, hV0, hVhat⟩ := exists_averaging_test
  obtain ⟨Cerror, hCerror, herror⟩ :=
    average_remainder_small_power epsilon hepsilon
  have hWcompact : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  let Ws : 𝓢(ℝ, ℂ) := hWcompact.toSchwartzMap hW
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 Ws
  let supportBound : ℝ := max 1 b
  let Error : ℝ := Cerror * G * pvControl V * supportBound ^ (1 + epsilon)
  let Average : ℝ := Real.sqrt (768 * Cmean)
  let alpha : ℝ := (1 + theta) / 6
  let targetExponent : ℝ := (11 + 5 * theta) / 12 + epsilon
  let averageExponent : ℝ := alpha + targetExponent
  let C : ℝ := (Average + Error) / ‖paperRadialFourier V 0‖
  have hG : 0 ≤ G := apply_nonneg _ _
  have hSupportBound : 1 ≤ supportBound := le_max_left _ _
  have hError : 0 ≤ Error :=
    mul_nonneg (mul_nonneg (mul_nonneg hCerror.le hG)
      (pvControl_nonneg V)) (by positivity)
  have hAverage : 0 < Average := Real.sqrt_pos.mpr (by positivity)
  have hhat : 0 < ‖paperRadialFourier V 0‖ := norm_pos_iff.mpr hVhat
  have halpha : 0 ≤ alpha := by
    dsimp [alpha]
    linarith
  refine ⟨C, div_pos (by linarith) hhat, ?_⟩
  intro D X hX hD
  have hXpos : 0 < X := by linarith
  let B : ℝ := X ^ alpha
  have hB : 1 ≤ B := Real.one_le_rpow hX halpha
  have hBpos : 0 < B := by linarith
  let F := outsideIdealsUpTo S D
  let A : OAI.ActualEisensteinCubic.O → ℂ :=
    idealRowSum F (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) chi (fun n ↦ W (n / X))
  have hBpower : B ^ 6 = X ^ (1 + theta : ℝ) := by
    dsimp only [B, alpha]
    rw [← Real.rpow_mul_natCast hXpos.le]
    congr 1
    ring
  have hsecondMoment :
      (∑ h ∈ (averagingRows B).image (fun b ↦ b ^ 6), ‖A h‖ ^ 2) ≤
        Cmean * X ^ ((2 + theta : ℝ) + 2 * epsilon) := by
    apply hmean D X hX hD
    · intro h hz
      have hnorm := (averagingRows_power_norm B hB hz).2
      simpa only [hBpower] using hnorm
    · intro h hz
      exact (averagingRows_power_norm B hB hz).1
  have havgSquare :=
    (average_tsum_cauchy V hV hVs hV0 B hB A).trans
      (mul_le_mul_of_nonneg_left hsecondMoment (by positivity : 0 ≤ 768 * B))
  have haverageIdentity :
      768 * B * (Cmean * X ^ ((2 + theta : ℝ) + 2 * epsilon)) =
        (Average * X ^ averageExponent) ^ 2 := by
    dsimp only [B, Average]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 768 * Cmean),
      ← Real.rpow_mul_natCast hXpos.le]
    calc
      _ = (768 * Cmean) *
          (X ^ alpha * X ^ ((2 + theta : ℝ) + 2 * epsilon)) := by
            ring
      _ = (768 * Cmean) *
          X ^ (alpha + ((2 + theta : ℝ) + 2 * epsilon)) := by
            rw [← Real.rpow_add hXpos]
      _ = _ := by
        congr 2
        dsimp [averageExponent, targetExponent, alpha]
        ring
  rw [haverageIdentity] at havgSquare
  have havg :
      ‖∑' b : OAI.ActualEisensteinCubic.O,
        V (‖eisEmbedding b‖ ^ 2 / B) * A (b ^ 6)‖ ≤
        Average * X ^ averageExponent :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havgSquare
  have hremainder :
      ‖∑ n ∈ F,
        baseChangeWeight chi n * W ((Ideal.absNorm n : ℝ) / X) *
          maskedPrincipalRemainder (fun i : primePool F ↦ i.val)
            (idealSupport F n) V B‖ ≤
        Error * X ^ (1 + epsilon) := by
    have hBZ : 1 ≤ supportBound * X := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hSupportBound) (sub_nonneg.mpr hX)]
    have hbound := herror F (outsideIdealsUpTo_ne_bot S D) chi
      (fun n ↦ W (n / X)) V B (supportBound * X) G hBpos hBZ hG
      (fun n ↦ Ws.norm_le_seminorm ℝ (n / X)) (by
        intro n hI hn
        have hsupportUpper := (hsupport hn).2
        exact ((div_le_iff₀ hXpos).mp hsupportUpper).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 b) hXpos.le))
    calc
      _ ≤ Cerror * G * pvControl V * (supportBound * X) ^ (1 + epsilon) := hbound
      _ = Error * X ^ (1 + epsilon) := by
        rw [Real.mul_rpow (by linarith : 0 ≤ supportBound) hXpos.le]
        dsimp only [Error]
        ring
  have herrorExponent : X ^ (1 + epsilon) ≤ X ^ averageExponent :=
    Real.rpow_le_rpow_of_exponent_le hX (by
      dsimp [averageExponent, targetExponent, alpha]
      linarith)
  have hmain := totient_sum_normalized_bound F
    (outsideIdealsUpTo_ne_bot S D) (outside_good S D hbad) chi
    (fun n ↦ W (n / X)) V B hBpos
  have hbound :
      B * ‖paperRadialFourier V 0‖ *
          ‖∑ n ∈ F,
            baseChangeWeight chi n * W ((Ideal.absNorm n : ℝ) / X) *
              totientDensity n‖ ≤
        (Average + Error) * X ^ averageExponent := by
    apply hmain.trans
    have hsum := add_le_add havg
      (hremainder.trans (mul_le_mul_of_nonneg_left herrorExponent hError))
    simpa only [add_mul] using hsum
  have hfactor : X ^ averageExponent = B * X ^ targetExponent := by
    dsimp only [averageExponent, B]
    rw [← Real.rpow_add hXpos]
  apply (mul_le_mul_iff_right₀ (mul_pos hBpos hhat)).mp
  apply hbound.trans_eq
  rw [hfactor]
  dsimp only [C, targetExponent]
  field_simp [hhat.ne']

end

end ElevenTwelfths
