import ElevenTwelfths.ConcreteFamily
import ElevenTwelfths.ActualFixedShellModels
import OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity
import OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage

/-!
# The zeta family in the notation of the blueprint

These are concrete sums, not a structure of conjectural analytic inputs.
The excluded primes are fixed once and for all at conductor one. The finite
element sums are definitionally the existing public family; the theorem
mean_square connects them to the actual theta construction and descent.

X and H are natural norm bounds. The estimate holds for H ≤ X^(1+θ);
taking H comparable to that radius gives S(X,H) ≪ X H X^ε.
We do not claim that bound uniformly for tiny H.
-/

namespace ElevenTwelfths.Zeta

noncomputable section
open scoped BigOperators Classical
open OAI
open OAI.ActualEisensteinCubic
open OAI.CompletedGauss
open OAI.ConcretePrimeRowBridge
open OAI.InitialMeanSquare
open OAI.ShortDraftHeckeBridge
open OAI.CanonicalRowCompletion
open OAI.CanonicalCoefficientClass
open OAI.CubicEisenstein

/-- The fixed finite exceptional set for zeta, not a varying conductor. -/
abbrev excludedPrimes : Finset (Ideal 𝒪) := reflectionExcludedPrimes 1

abbrev columns (X : ℕ) : Finset 𝒪 := outsidePrimaryBall excludedPrimes X
abbrev rows (H : ℕ) : Finset 𝒪 := exactRowBall H

/-- χ_n(h), the actual sextic character used in this finite column family. -/
abbrev sexticTwist (X : ℕ) (n h : 𝒪) : ℂ :=
  outsideSexticTwist excludedPrimes (reflectionExcludedPrimes_bad 1) X h n

/-- The four visible ingredients: primaryness, Möbius, sextic twist, cutoff. -/
def M (W : SmoothDyadicWeight ℂ) (h : 𝒪) (X : ℕ) : ℂ :=
  ∑ n ∈ columns X, if primary n then
    (μ_K n : ℂ) * sexticTwist X n h * W ((𝒩 n : ℝ) / X) else 0

/-- The untwisted Möbius sum M(X) from the intro. -/
def untwistedM (W : SmoothDyadicWeight ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ columns X, if primary n then
    (μ_K n : ℂ) * W ((𝒩 n : ℝ) / X) else 0

/-- The smoothly weighted finite second moment. -/
def S (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff) (X H : ℕ) : ℝ :=
  ∑ h ∈ rows H, V ((𝒩 h : ℝ) / H) * ‖M W h X‖ ^ 2

theorem M_eq_outsideM (W : SmoothDyadicWeight ℂ) (h : 𝒪) (X : ℕ) :
    M W h X = outsideM excludedPrimes (reflectionExcludedPrimes_bad 1) W h X := rfl

theorem S_eq_outsideS (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) :
    S W V X H = outsideS excludedPrimes (reflectionExcludedPrimes_bad 1) W V X H := rfl

theorem M_one (W : SmoothDyadicWeight ℂ) (X : ℕ) :
    M W 1 X = untwistedM W X := by
  simp only [M, untwistedM, sexticTwist, outsideSexticTwist, idealSexticRow_one,
    mul_one]

/-- Exact amplifier identity: sixth powers leave precisely a coprimality
restriction. No prime-counting or asymptotic approximation is hidden here. -/
theorem M_sixth_power (W : SmoothDyadicWeight ℂ) (b : 𝒪) (X : ℕ) :
    M W (b ^ 6) X =
      ∑ n ∈ outsideIdealsUpTo excludedPrimes X with IsCoprime n (Ideal.span {b}),
        (UniqueFactorizationMonoid.moebius n : ℂ) * W ((Ideal.absNorm n : ℝ) / X) := by
  rw [M_eq_outsideM, outsideM_eq_idealRowSum,
    OAI.SixthPowerAverage.idealRowSum_sixth_eq_coprime_sum]
  apply Finset.sum_congr rfl
  intro n hI
  have hchi : (1 : DirichletCharacter ℂ 1) (Ideal.absNorm n) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [baseChangeWeight, hchi, mul_one]

/-- The finite-to-lattice boundary immediately before applying Poisson. -/
theorem S_eq_tsum (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) :
    S W V X H = ∑' h : 𝒪, V ((𝒩 h : ℝ) / H) * ‖M W h X‖ ^ 2 :=
  outsideS_eq_tsum excludedPrimes (reflectionExcludedPrimes_bad 1) W V X H

/-- The column coefficient with its smooth cutoff, before twisting. -/
def mobiusWeight (W : SmoothDyadicWeight ℂ) (X : ℕ) (n : 𝒪) : ℂ :=
  if primary n then (μ_K n : ℂ) * W ((𝒩 n : ℝ) / X) else 0

theorem M_eq_sum (W : SmoothDyadicWeight ℂ) (h : 𝒪) (X : ℕ) :
    M W h X = ∑ n ∈ columns X, mobiusWeight W X n * sexticTwist X n h := by
  apply Finset.sum_congr rfl
  intro n hn
  simp only [mobiusWeight]
  split_ifs <;> ring

/-- Open the square and reverse the finite sums: h is now inside.
The complex cast on the real moment makes conjugation explicit. This is an
exact identity, before diagonal removal or the coprime heuristic. -/
theorem S_open_square (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (X H : ℕ) :
    (S W V X H : ℂ) =
      ∑ n₁ ∈ columns X, ∑ n₂ ∈ columns X,
        mobiusWeight W X n₁ * star (mobiusWeight W X n₂) *
          ∑ h ∈ rows H, (V ((𝒩 h : ℝ) / H) : ℂ) *
            sexticTwist X n₁ h * star (sexticTwist X n₂ h) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [S, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    ← Complex.mul_conj', M_eq_sum, map_sum, Finset.sum_mul, Finset.mul_sum,
    map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₂ hm
  apply Finset.sum_congr rfl
  intro h hu
  simp only [starRingEnd_apply]
  ring

/-- The actual analytic estimate, with no theta-model hypothesis left over.
The row sum is the same M that appears in the definition of S. -/
theorem row_mean_square (W : SmoothDyadicWeight ℂ)
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∀ T : Finset 𝒪,
      (∀ h ∈ T, (𝒩 h : ℝ) ≤ (X : ℝ) ^ (1 + θ)) →
      (∀ h ∈ T, h ≠ 0) →
      (∑ h ∈ T, ‖M W h X‖ ^ 2) ≤
        C * X * (X : ℝ) ^ (1 + θ) * (X : ℝ) ^ ε := by
  obtain ⟨C, hC, hmean⟩ := outside_mean_square_of_theta_models_pos
    (1 : DirichletCharacter ℂ 1) excludedPrimes
    (reflectionExcludedPrimes_bad 1) (reflectionExcludedPrimes_prime 1)
    1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor 1))
    (by norm_num) completedRamifiedStep_gt_one
    (reflectionLevelBound_ge_one 1 (by norm_num))
    (actual_hasCanonicalThetaModels 1 (1 : DirichletCharacter ℂ 1))
    W (1 / 2) 1 (by norm_num) W.support_subset W.contDiff θ ε hθ hε
  refine ⟨C, hC, ?_⟩
  intro X hX T hT hT0
  simpa only [M_eq_outsideM, outsideM_eq_idealRowSum] using
    hmean X X (by exact_mod_cast hX) (by simp) T hT hT0

/-- Smooth second moment for a cutoff bounded by one. A general bounded
cutoff can be rescaled; the column weight has no normalization assumption. -/
theorem mean_square (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (hV : ∀ t, V t ≤ 1) (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X H : ℕ, 1 ≤ X →
      (H : ℝ) ≤ (X : ℝ) ^ (1 + θ) →
      S W V X H ≤ C * X * (X : ℝ) ^ (1 + θ) * (X : ℝ) ^ ε := by
  obtain ⟨C, hC, hmean⟩ := row_mean_square W θ ε hθ hε
  refine ⟨C, hC, ?_⟩
  intro X H hX hH
  have hzero : V 0 = 0 :=
    V.toSmoothDyadicWeight.eq_zero_of_lt_half (by norm_num)
  have hremove : S W V X H =
      ∑ h ∈ rowNormDisk H, V ((𝒩 h : ℝ) / H) * ‖M W h X‖ ^ 2 := by
    simp [S, rows, exactRowBall, Finset.sum_insert, mem_rowNormDisk, hzero]
  rw [hremove]
  apply le_trans (Finset.sum_le_sum fun h hu ↦
    mul_le_of_le_one_left (sq_nonneg _) (hV _))
  apply hmean X hX
  · intro h hu
    exact (show (𝒩 h : ℝ) ≤ H by exact_mod_cast (mem_rowNormDisk.mp hu).2).trans hH
  · intro h hu hzero
    have := (mem_rowNormDisk.mp hu).1
    simp [hzero] at this

/-- The introductory X H bound, with the intended choice of row scale
made explicit. The constant absorbs the factor two in dyadic comparison. -/
theorem mean_square_dyadic (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (hV : ∀ t, V t ≤ 1) (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X H : ℕ, 1 ≤ X →
      (H : ℝ) ≤ (X : ℝ) ^ (1 + θ) →
      (X : ℝ) ^ (1 + θ) ≤ 2 * H →
      S W V X H ≤ C * X * H * (X : ℝ) ^ ε := by
  obtain ⟨C, hC, hmean⟩ := mean_square W V hV θ ε hθ hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro X H hX hupper hlower
  calc
    S W V X H ≤ C * X * (X : ℝ) ^ (1 + θ) * (X : ℝ) ^ ε :=
      hmean X H hX hupper
    _ ≤ C * X * (2 * H) * (X : ℝ) ^ ε := by gcongr
    _ = (2 * C) * X * H * (X : ℝ) ^ ε := by ring

end
end ElevenTwelfths.Zeta
