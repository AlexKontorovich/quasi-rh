import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

/-!
# Actual fixed-shell models from branch decoding

This fixed-shell construction is adapted from OpenAI's row-completion sources
at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.  It imports only the
immediate lower-level module `BranchDecoding` and exposes the fixed-shell
identity and model interface needed by the direct `11 / 12` argument.  The
nonvanishing conclusion is proved later, in `ElevenTwelfths.Unconditional`.
-/

namespace ElevenTwelfths

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff

open OAI
open OAI.ActualEisensteinCubic
open OAI.CanonicalRowCompletion
open OAI.CanonicalRowCompletion.ActualFiber
open OAI.CanonicalCoefficientClass
open OAI.CanonicalQuadraticSieve
open OAI.CompletedGauss
open OAI.CubicEisenstein
open UniqueFactorizationMonoid

namespace ActualFixedShellModels

local notation "Eis" => OAI.ActualEisensteinCubic.O

noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ := OAI.PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

variable (q : ℕ) (hq : q ≠ 0) (m : Eis) (hm : m ≠ 0)
    (rows : Finset (Ideal Eis)) (R F : Ideal Eis) (hR : R ≠ 0)
    (hF : Squarefree F) (hrows : ∀ I ∈ rows, I ≠ 0) (v : Eisˣ)
variable [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})]

theorem reflectedFiber_four_mul_value_local
    (K : ℝ) (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖ ≤ 1)
    (hbound : ∀ I ∈ rows, (Ideal.absNorm I : ℝ) ≤ K)
    (J : RowIndex q m rows R F)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X)
    (hK : 0 < completedResidualScale K R (maskIdeal q m F))
    (hk : completedResidualScale K R (maskIdeal q m F) / 2 ≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)) : ℝ)) :
    let k := fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI ↦ ⟨hrows I hI, hbound I hI⟩) J
    4 * (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).value
      W X 1 completedRamifiedStep k =
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀ h : Eis ⧸ Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q)
        (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun _ ↦ Fintype.ofFinite _
  let d := reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k := fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI ↦ ⟨hrows I hI, hbound I hI⟩) J
  let f := fun (h : Eis ⧸ Ideal.span {reflectionConductor q})
    (rho : (fixedFourierGeometry (reflectionConductor q)
      (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u : Eisˣ)
    (B : Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l : B → Fin 3) ↦
      (d.branch (fixedReflectionRayEquiv (reflectionConductor q)
        (reflectionConductor_ne_zero q hq) ⟨h, rho, u⟩,
          encodeReflectionSix ⟨B, l⟩)).value W X 1 completedRamifiedStep k
  let g := fun (h : Eis ⧸ Ideal.span {reflectionConductor q}) (u : Eisˣ)
    (B : Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l : B → Fin 3) ↦
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen := fun (h : Eis ⧸ Ideal.span {reflectionConductor q})
    (B : Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) ↦
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (OAI.CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h
        (fixedFourierGeometry (reflectionConductor q)
          (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let alpha := fun h ↦ sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape := fun h B ↦ sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w := FreeReflection.reflectionInactiveStratumWeight R F
    (maskIdeal q m F) (freeConductor q)
  have hbranch : ∀ h rho u B l, 4 * f h rho u B l =
      if rho = chosen h B then alpha h * shape h B * g h u B l else 0 := by
    intro h rho u B l
    exact reflectedFiber_encoded_branch_exact q hq m hm rows R F hR hF hrows v
      K Ψ hΨ hbound J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue : d.value W X 1 completedRamifiedStep k =
      ∑ h, ∑ rho, ∑ u, ∑ B, w B * ∑ l, f h rho u B l := by
    rw [reflectedFiber_value q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q)
      (reflectionConductor_ne_zero q hq) _
  change 4 * d.value W X 1 completedRamifiedStep k = _
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen alpha shape w hbranch

theorem completedT_eq_reflectedFiber_idealValue_local
    (Ψ : Eis →* ℂ)
    (hΨperiod : OAI.CanonicalCoefficientClass.FactorsModulo
      (OAI.CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨ : ∀ n, ‖Ψ n‖ ≤ 1)
    (K : ℝ) (hshell : ∀ I ∈ rows,
      K / 2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ K)
    (J : RowIndex q m rows R F)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT (rowTwist Ψ (maskElement q m)
      (OAI.ConcretePrimeRowBridge.idealGenerator F)
      (v.val * OAI.ConcretePrimeRowBridge.idealGenerator J.val)) W X =
      (4 * thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar) *
        (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).idealValue
          W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k := fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI ↦ ⟨hrows I hI, (hshell I hI).2⟩) J
  have hs := residual_shell q m rows R F K
    (fun I hI ↦ ⟨hrows I hI, hshell I hI⟩) J
  have he := reflectedFiber_four_mul_value_local q hq m hm rows R F hR hF hrows v
    K Ψ hΨ (fun I hI ↦ (hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [completedT_eq_compressedSourceTotal q hq m hm rows R F hR hF hrows v
    Ψ hΨperiod hΨ J W lo hi hlo hsupp hW X hX, ← he]
  have hid : rowResidualPart J.val (maskIdeal q m F) = k.val := rfl
  rw [hid, ReflectedFiberData.idealValue_at]
  ring

def actualReflectionScale : ℂ :=
  4 * thetaDerivativeScalar⁻¹ * fixedRadialCoefficientScalar

theorem actual_fixedShellModels (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase chi)
      (fixedReflectionRayCount (reflectionConductor q)
        (reflectionConductor_ne_zero q hq))
      actualReflectionScale 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
  let : Finite (Eis ⧸ Ideal.span {reflectionConductor q}) :=
    OAI.ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis ⧸ Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  apply fixedShellModels_of_actual_fiber_identity q hq chi actualReflectionScale
  intro Ψ hperiod hnorm m hm F hF u W a b ha hs hW K X hK hX rows hrows R hR J
  exact completedT_eq_reflectedFiber_idealValue_local q hq m hm rows R F
    (hrows R hR).1 hF (fun I hI ↦ (hrows I hI).1) u Ψ hperiod hnorm K
    (fun I hI ↦ (hrows I hI).2) J W a b ha hs hW X hX

theorem exists_actual_fixedShellModels (q : ℕ) [NeZero q]
    (chi : DirichletCharacter ℂ q) :
    ∃ (rays : ℕ) (scale : ℂ),
      HasFixedShellModels (reflectionExcludedPrimes q) (initialBase chi)
        rays scale 1 completedRamifiedStep
        (fixedCuspLevelBound (reflectionConductor q)) := by
  exact ⟨fixedReflectionRayCount (reflectionConductor q)
      (reflectionConductor_ne_zero q (NeZero.ne q)),
    actualReflectionScale, actual_fixedShellModels q (NeZero.ne q) chi⟩

end ActualFixedShellModels

end

end ElevenTwelfths
