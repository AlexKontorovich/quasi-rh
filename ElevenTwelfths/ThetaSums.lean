import ElevenTwelfths.SmoothDyadic
import OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
import OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss

/-!
# Cubic completion and quadratic energy in readable notation

These interfaces reuse the upstream coefficients and the sharp sieve, rather
than inventing coefficients with the desired properties. In particular the
angular phase in c₃ and the square-root normalization in completion remain
visible. A completed sum is NOT asserted to equal the original sum: the
cube-inversion theorem gives the actual relation.
-/

namespace ElevenTwelfths.Theta

noncomputable section
open scoped BigOperators Classical
open OAI OAI.ActualEisensteinCubic
open OAI.CompletedGauss hiding O

/-- The squarefree cubic Gauss coefficient, including its angular phase. -/
abbrev c₃ (I : Ideal O) : ℂ := squarefreeGaussCoefficient I

theorem c₃_eq (I : Ideal O) (hsq : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    c₃ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI :=
  squarefreeGaussCoefficient_eq I hsq hI

/-- The squarefree coefficient sum, with the twist Ψ exposed. -/
def cubicSum (Ψ : O →* ℂ) (W : SmoothDyadicWeight ℂ) (X : ℝ) : ℂ :=
  ∑' n : Ideal O, c₃ n * Ψ (primaryGenerator n) * W ((Ideal.absNorm n : ℝ) / X)

/-- Completion restores the cube multiples I J³, with their actual weights. -/
def thetaSum (Ψ : O →* ℂ) (W : SmoothDyadicWeight ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O,
    (c₃ I * Ψ (primaryGenerator I)) / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      cubeWeight Ψ J *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

theorem thetaSum_eq_completedT (Ψ : O →* ℂ) (W : SmoothDyadicWeight ℂ) (X : ℝ) :
    thetaSum Ψ W X = completedT Ψ W X := rfl

/-- Exact bridge from the original cubic sum to completed theta sums.
The original sum is recovered at cube-divided scales, not by erasing weights. -/
theorem cubicSum_eq_cube_inversion (Ψ : O →* ℂ) (W : SmoothDyadicWeight ℂ)
    (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ * cubicSum Ψ W X =
      ∑' J : Ideal O, (UniqueFactorizationMonoid.moebius J : ℂ) * cubeWeight Ψ J *
        thetaSum Ψ W (X / (Ideal.absNorm J : ℝ) ^ 3) :=
  completed_cube_inverse Ψ W
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc W.support_subset) X hX

open OAI.CanonicalQuadraticSieve hiding O

/-- Quadratic character: exactly the cube of the singleton sextic row. -/
abbrev χ₂ (I : Ideal O) (u : O) : ℂ := quadraticRow I u

theorem χ₂_eq_sextic_cube (I : Ideal O) (hI : Admissible I) (u : O) :
    χ₂ I u =
      (OAI.ConcretePrimeRowBridge.idealSexticRow {I}
        (singletonPositive I hI) (singletonGood I hI) I u) ^ 3 := by
  exact dite_eq_left hI

/-- A block of the quadratic energy. Its column coefficients do not depend
on the row ℓ; obtaining such blocks from reflection is a separate step. -/
def quadraticEnergy (rows cols : Finset (Ideal O)) (a : Ideal O → ℂ) : ℝ :=
  ∑ ℓ ∈ rows, ‖∑ y ∈ cols, a y * χ₂ y (primaryGenerator ℓ)‖ ^ 2

/-- The SHARP L+Y estimate, not the initial L+Y² bound. -/
theorem quadratic_large_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L Y : ℝ, 1 ≤ L → 1 ≤ Y →
      ∀ rows cols : Finset (Ideal O),
      (∀ ℓ ∈ rows, Admissible ℓ ∧ (Ideal.absNorm ℓ : ℝ) ≤ L) →
      (∀ y ∈ cols, Admissible y ∧ (Ideal.absNorm y : ℝ) ≤ Y) →
      ∀ a : Ideal O → ℂ,
      quadraticEnergy rows cols a ≤
        C * (L * Y) ^ ε * (L + Y) * ∑ y ∈ cols, ‖a y‖ ^ 2 := by
  obtain ⟨C, hC, hsieve⟩ := finite_family_quadratic_large_sieve ε hε
  refine ⟨C, hC, ?_⟩
  intro L Y hL hY rows cols hrows hcols a
  have h := hsieve L Y hL hY
    (fun ℓ : rows ↦ (ℓ : Ideal O)) (fun y : cols ↦ (y : Ideal O))
    Subtype.val_injective Subtype.val_injective
    (fun ℓ ↦ hrows ℓ ℓ.property) (fun y ↦ hcols y y.property)
    (fun y ↦ a y)
  have sum_rows (f : Ideal O → ℝ) :
      (∑ ℓ : rows, f ℓ) = ∑ ℓ ∈ rows, f ℓ :=
    (Finset.sum_subtype rows (fun _ ↦ Iff.rfl) f).symm
  have sum_cols (f : Ideal O → ℂ) :
      (∑ y : cols, f y) = ∑ y ∈ cols, f y :=
    (Finset.sum_subtype cols (fun _ ↦ Iff.rfl) f).symm
  have sum_norm :
      (∑ y : cols, ‖a y‖ ^ 2) = ∑ y ∈ cols, ‖a y‖ ^ 2 :=
    (Finset.sum_subtype cols (fun _ ↦ Iff.rfl) (fun y ↦ ‖a y‖ ^ 2)).symm
  have inner (ℓ : rows) :
      (∑ y : cols, quadraticRow y (primaryGenerator ℓ) * a y) =
        ∑ y ∈ cols, quadraticRow y (primaryGenerator ℓ) * a y :=
    sum_cols (fun y ↦ quadraticRow y (primaryGenerator ℓ) * a y)
  simp only [inner, sum_norm] at h
  rw [sum_rows (fun ℓ ↦ ‖∑ y ∈ cols, quadraticRow y (primaryGenerator ℓ) * a y‖ ^ 2)] at h
  simpa only [quadraticEnergy, χ₂, mul_comm (a _) (quadraticRow _ _)] using h

/-- Algebra of the introductory sieve heuristic, conditional on its energy
bound. This is NOT a theorem that the full reflected moment is one block. -/
theorem reflected_energy_bound (X H L Y E B : ℝ)
    (hX : 0 < X) (hH : 0 ≤ H) (hL : 0 < L)
    (hY : Y = L ^ 2 / X) (hE : E ≤ B * (L + Y) * Y) :
    (H * X / L ^ 2) * E ≤ B * H * (L + Y) := by
  calc
    _ ≤ (H * X / L ^ 2) * (B * (L + Y) * Y) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by rw [hY]; field_simp

end
end ElevenTwelfths.Theta
