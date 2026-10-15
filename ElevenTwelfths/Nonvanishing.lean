import OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing

namespace ElevenTwelfths

/-!
# From the `11 / 12` Eisenstein--Möbius estimate to zeta nonvanishing

This file isolates the final analytic bridge.  Its hypothesis is the smoothed
weighted ideal sum produced by the sixth-power amplifier; unlike the OpenAI
`23 / 24` route, it does not assume canonical theta models or import an
already-proved zero-free region.
-/

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology ContDiff

open OAI
open OAI.ActualEisensteinCubic
open OAI.CanonicalRowCompletion
open OAI.CompactMellinBridge
open OAI.ShortDraftHeckeBridge hiding O
open OAI.SixthPowerAverage

/-- The analytic-number-theory input needed by the final bridge.

For every smooth weight supported in the public dyadic interval `[1 / 2, 1]`,
the Eisenstein ideal sum with the finite bad Euler factors removed and with
coefficient `weightedMoebius = baseChangeWeight * totientDensity` has
exponent `sigma + ε`. -/
def SmoothedWeightedMobiusBound
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (sigma : ℝ) : Prop :=
  ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W →
    Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 1 →
    ∀ epsilon : ℝ, 0 < epsilon →
      (fun Z : ℝ ↦ ∑' I : Ideal O,
        outsideWeight chi S I * W ((Ideal.absNorm I : ℝ) / Z)) =O[atTop]
          (fun Z : ℝ ↦ Z ^ (sigma + epsilon))

/-- Dilating a `[1, 2]` auxiliary weight by `x ↦ 2x` converts it to the
public `[1 / 2, 1]` convention.  The simultaneous scale change `Z ↦ 2Z`
does not alter a power exponent. -/
theorem idealSum_isBigO_of_smoothedWeightedMobiusBound
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (sigma : ℝ)
    (hbound : SmoothedWeightedMobiusBound chi S sigma)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsupp : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (fun Z : ℝ ↦ ∑' I : Ideal O,
      outsideWeight chi S I * W ((Ideal.absNorm I : ℝ) / Z)) =O[atTop]
        (fun Z : ℝ ↦ Z ^ (sigma + epsilon)) := by
  let U : ℝ → ℂ := fun x ↦ W (2 * x)
  have hU : ContDiff ℝ ∞ U := by
    dsimp only [U]
    fun_prop
  have hUsupp : Function.support U ⊆ Set.Icc (1 / 2 : ℝ) 1 := by
    intro x hx
    change W (2 * x) ≠ 0 at hx
    have hlower : 1 < 2 * x := by
      by_contra h
      exact hx (hsupp (2 * x) (Or.inl (le_of_not_gt h)))
    have hupper : 2 * x < 2 := by
      by_contra h
      exact hx (hsupp (2 * x) (Or.inr (le_of_not_gt h)))
    constructor <;> linarith
  have hscaled := (hbound U hU hUsupp epsilon hepsilon).comp_tendsto
    (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 2))
  have hscaled' :
      (fun Z : ℝ ↦ ∑' I : Ideal O,
        outsideWeight chi S I * U ((Ideal.absNorm I : ℝ) / (2 * Z))) =O[atTop]
          (fun Z : ℝ ↦ (2 * Z) ^ (sigma + epsilon)) := by
    simpa only [Function.comp_def, id_eq] using hscaled
  have hleft :
      (fun Z : ℝ ↦ ∑' I : Ideal O,
        outsideWeight chi S I * U ((Ideal.absNorm I : ℝ) / (2 * Z))) =ᶠ[atTop]
      (fun Z : ℝ ↦ ∑' I : Ideal O,
        outsideWeight chi S I * W ((Ideal.absNorm I : ℝ) / Z)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
    apply tsum_congr
    intro I
    have harg : 2 * ((Ideal.absNorm I : ℝ) / (2 * Z)) =
        (Ideal.absNorm I : ℝ) / Z := by
      have hZ0 : Z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hZ)
      field_simp [hZ0]
    simp only [U, harg]
  have hright :
      (fun Z : ℝ ↦ (2 * Z) ^ (sigma + epsilon)) =O[atTop]
        (fun Z : ℝ ↦ Z ^ (sigma + epsilon)) := by
    apply (isBigO_const_mul_self ((2 : ℝ) ^ (sigma + epsilon))
      (fun Z : ℝ ↦ Z ^ (sigma + epsilon)) atTop).congr'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Z hZ
      exact (Real.mul_rpow (by norm_num) hZ).symm
    · exact Filter.EventuallyEq.rfl
  exact (hscaled'.congr' hleft Filter.EventuallyEq.rfl).trans hright

/-- Rewrite the ideal-sum estimate in the `weightedCompactSum` form consumed
by inverse Mellin continuation. -/
theorem weightedCompactSum_isBigO_of_smoothedWeightedMobiusBound
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (sigma : ℝ)
    (hbound : SmoothedWeightedMobiusBound chi S sigma)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsupp : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (fun Z : ℝ ↦ weightedCompactSum chi S W Z⁻¹) =O[atTop]
      (fun Z : ℝ ↦ Z ^ (sigma + epsilon)) := by
  have hideal := idealSum_isBigO_of_smoothedWeightedMobiusBound
    chi S sigma hbound W hW hsupp epsilon hepsilon
  apply hideal.congr'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ
    symm
    exact weightedCompactSum_eq_ideal_tsum chi S W Z 2 (by linarith)
      (fun x hx ↦ by
        have h2 : x < 2 := by
          by_contra h
          exact hx (hsupp x (Or.inr (le_of_not_gt h)))
        exact h2.le)
  · exact Filter.EventuallyEq.rfl

/-- The smoothed weighted Möbius estimate gives analytic continuation of the
inverse Mellin factor to `re s > sigma`. -/
theorem weightedCompactMellin_analytic_of_smoothedWeightedMobiusBound
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (sigma : ℝ)
    (hbound : SmoothedWeightedMobiusBound chi S sigma)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsupp : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0) :
    AnalyticOnNhd ℂ
      (fun s : ℂ ↦ mellin (fun Z : ℝ ↦ weightedCompactSum chi S W Z⁻¹) (-s))
      {s : ℂ | sigma < s.re} := by
  have hsum := weightedCompactSum_hasSum chi S W
    (fun x hx ↦ hsupp x (Or.inr hx))
  have hlocal := weighted_sum_inv_locallyIntegrableOn_pos
    (weightedCoeff chi S) W (weightedCompactSum chi S W) hW
    (fun x hx ↦ hsupp x (Or.inr hx)) hsum
  have hzero := weighted_sum_zero_near_small_D
    (weightedCoeff chi S) (weightedCoeff_zero chi S) W
    (weightedCompactSum chi S W) (fun x hx ↦ hsupp x (Or.inr hx)) hsum
  intro s hs
  have hepsilon : 0 < (s.re - sigma) / 2 := by
    change sigma < s.re at hs
    linarith
  apply OAI.ShortDraftMellin.inverse_mellin_analytic
    (fun Z : ℝ ↦ weightedCompactSum chi S W Z⁻¹)
    (sigma + (s.re - sigma) / 2) hlocal
    (weightedCompactSum_isBigO_of_smoothedWeightedMobiusBound
      chi S sigma hbound W hW hsupp _ hepsilon) hzero s
  change sigma + (s.re - sigma) / 2 < s.re
  change sigma < s.re at hs
  linarith

/-- A direct per-character zero-free theorem from the `sigma` weighted
Eisenstein--Möbius estimate. -/
theorem dirichletL_ne_zero_of_smoothedWeightedMobiusBound
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (sigma : ℝ) (hsigma_pos : 0 < sigma) (hsigma : sigma < 1)
    (hbound : SmoothedWeightedMobiusBound chi S sigma)
    (z : ℂ) (hz : sigma < z.re) (hpole : ¬ (chi = 1 ∧ z = 1)) :
    chi.LFunction z ≠ 0 := by
  by_cases hz1 : z.re < 1
  · let W : ℝ → ℂ := OAI.ConcreteCompactWeight.weight z
    have hW : ContDiff ℝ ∞ W := OAI.ConcreteCompactWeight.weight_smooth z
    have hWs : ∀ x, x ≤ 1 ∨ 2 ≤ x → W x = 0 :=
      OAI.ConcreteCompactWeight.weight_support z
    have hM := weightedCompactMellin_analytic_of_smoothedWeightedMobiusBound
      chi S sigma hbound W hW hWs
    have hE := finiteEulerFactor_analytic chi S hS sigma
    have hH : AnalyticOnNhd ℂ (OAI.SmoothMobiusCorrection.eulerCorrection chi S)
        {s : ℂ | sigma < s.re} :=
      (OAI.SmoothMobiusCorrection.eulerCorrection_analytic chi S).mono (by
        intro s hs
        change 0 < s.re
        change sigma < s.re at hs
        exact hsigma_pos.trans hs)
    have hWanalytic := compact_weight_mellin_analytic W hW hWs sigma
    have hnotboth : chi ≠ 1 ∨ baseChangeChar chi ≠ 1 := by
      by_cases hchi : chi = 1
      · exact Or.inr (baseChangeChar_ne_one_of_one chi hchi)
      · exact Or.inl hchi
    have hzneq : z ≠ 1 := by
      intro he
      subst z
      norm_num at hz1
    exact (pair_zero_free_of_identity_gt_two chi (baseChangeChar chi) hnotboth
      sigma hsigma
      (fun s ↦ (finiteEulerFactor chi S s *
          OAI.SmoothMobiusCorrection.eulerCorrection chi S s) *
        mellin (fun Z : ℝ ↦ weightedCompactSum chi S W Z⁻¹) (-s))
      (mellin W) ((hE.mul hH).mul hM) hWanalytic
      (OAI.CanonicalRowCompletion.corrected_weighted_mellin_identity
        chi S hS W hW hWs)
      z hz hzneq (OAI.ConcreteCompactWeight.weight_mellin_ne_zero z)).1
  · exact OAI.ShortDraft.dirichlet_target_of_one_le_re
      q chi z (le_of_not_gt hz1) hpole

/-- The final bridge at the requested exponent.  The hypothesis is only the
smoothed weighted Eisenstein--Möbius bound for the trivial character modulo
one and one finite set of prime Euler factors. -/
theorem riemannZeta_ne_zero_of_elevenTwelfths_weightedMobiusBound
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbound : SmoothedWeightedMobiusBound
      (1 : DirichletCharacter ℂ 1) S (11 / 12 : ℝ))
    (z : ℂ) (hz : (11 / 12 : ℝ) < z.re) :
    riemannZeta z ≠ 0 := by
  by_cases hz1 : z = 1
  · simpa only [hz1] using riemannZeta_one_ne_zero
  · have hL := dirichletL_ne_zero_of_smoothedWeightedMobiusBound
      (1 : DirichletCharacter ℂ 1) S hS (11 / 12 : ℝ) (by norm_num)
      (by norm_num) hbound z hz (by
        intro h
        exact hz1 h.2)
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hL

end

end ElevenTwelfths
