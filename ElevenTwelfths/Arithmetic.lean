import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The arithmetic objects

Columns are nonzero integral ideals of the Eisenstein integers, coprime to `(6)`.
Rows are elements of the ring of integers, with no quotient by units.
The sextic symbol is defined by its residue-field congruence, then multiplied
across prime-ideal factors. Its character laws are subsequent proof obligations.
-/

namespace ElevenTwelfths

open scoped NumberField BigOperators Cyclotomic
open UniqueFactorizationMonoid NumberField

/-- The Eisenstein number field, isomorphic to `ℚ(√-3)`. -/
abbrev K := CyclotomicField 3 ℚ

-- Identify the cyclotomic algebra structure with the canonical rational one.
set_option backward.isDefEq.respectTransparency false in
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- Its full ring of integers, mathematically `ℤ[ω]`. -/
abbrev 𝒪 := NumberField.RingOfIntegers K

/-- A fixed primitive cube root of unity, as an algebraic integer. -/
noncomputable def omega : 𝒪 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

/-- Fix one of the two complex embeddings throughout the argument. -/
noncomputable def complexEmbedding : K →+* ℂ := Classical.choice inferInstance

/-- The induced embedding of the ring of integers. -/
noncomputable def toComplex : 𝒪 →+* ℂ :=
  complexEmbedding.comp (algebraMap 𝒪 K)

/-- The element norm is the norm of the principal ideal `(u)`. -/
noncomputable def elementNorm (u : 𝒪) : ℕ := Ideal.absNorm (Ideal.span {u})

/-- Compatibility with the algebraic norm to `ℤ`. -/
theorem elementNorm_eq (u : 𝒪) : elementNorm u = (Algebra.norm ℤ u).natAbs :=
  Ideal.absNorm_span_singleton u

/-- In the complex embedding, the element norm is squared absolute value. -/
theorem complex_norm_sq (u : 𝒪) (φ : K →+* ℂ) : ‖φ (u : K)‖ ^ 2 = (elementNorm u : ℝ) := by
  have hc : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by norm_num),
      IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3 K]
    decide
  let : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp hc.le
  let : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K (n := 3) (by norm_num)
  have hp := InfinitePlace.prod_eq_abs_norm (u : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ),
    (IsTotallyComplex.isComplex (InfinitePlace.mk φ)).mult_eq_two] at hp
  change ‖φ (u : K)‖ ^ 2 = _ at hp
  rw [elementNorm_eq, Nat.cast_natAbs, Int.cast_abs]
  rw [← Algebra.coe_norm_int] at hp
  simpa using hp

/-- The bounded norm region contains finitely many Eisenstein integers. -/
theorem finite_elementNorm_le (H : ℕ) : {u : 𝒪 | elementNorm u ≤ H}.Finite := by
  have hf := Embeddings.finite_of_norm_le K ℂ ((H : ℝ) + 1)
  apply Set.Finite.of_finite_image (f := fun u : 𝒪 ↦ (u : K)) _ Subtype.val_injective.injOn
  apply hf.subset
  rintro x ⟨u, hu, rfl⟩
  refine ⟨u.property, ?_⟩
  intro φ
  have hn := complex_norm_sq u φ
  have hbound : (elementNorm u : ℝ) ≤ H := by exact_mod_cast hu
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  nlinarith [norm_nonneg (φ (u : K))]

/-- All lattice elements of norm at most `H`, with no arithmetic restriction. -/
noncomputable def rowBall (H : ℕ) : Finset 𝒪 :=
  (finite_elementNorm_le H).toFinset

@[simp]
theorem mem_rowBall {H : ℕ} {u : 𝒪} : u ∈ rowBall H ↔ elementNorm u ≤ H :=
  Set.Finite.mem_toFinset _

/-- Primary generators in the reference paper satisfy `n ≡ 1 (mod 3)`.
This condition is used for representing ideals, never to restrict the rows. -/
def Primary (n : 𝒪) : Prop := (3 : 𝒪) ∣ n - 1

/-- The ideal Möbius function; the zero ideal is assigned zero. -/
noncomputable def mobiusK (n : Ideal 𝒪) : ℤ := by
  classical
  exact if n = ⊥ then 0 else
    if Squarefree n then (-1) ^ (normalizedFactors n).card else 0

/-- Allowed sextic denominators: nonzero integral ideals coprime to `(6)`. -/
def Admissible (n : Ideal 𝒪) : Prop :=
  n ≠ ⊥ ∧ n ⊔ Ideal.span {(6 : 𝒪)} = ⊤

/-- The six roots, enumerated without choosing a primary generator. -/
noncomputable def sixthRoot (j : Fin 6) : 𝒪 := (-omega) ^ (j : ℕ)

/-- For a nonzero prime ideal away from `(6)`, select the sixth root whose
residue is `u ^ ((N p - 1) / 6)`; return zero when `u ∈ p`.
The finite selector is a definition, not an assumed existence/uniqueness lemma.
Only prime factors of admissible ideals are used in `chi` below. -/
noncomputable def primeSextic (p : Ideal 𝒪) (u : 𝒪) : ℂ := by
  classical
  exact if u ∈ p then 0 else
    ∑ j : Fin 6,
      if Ideal.Quotient.mk p (sixthRoot j) =
          Ideal.Quotient.mk p u ^ ((Ideal.absNorm p - 1) / 6)
      then toComplex (sixthRoot j) else 0

/-- The sextic residue symbol `χ_n(u) = (u/n)₆`, extended multiplicatively
in the ideal denominator. Outside the admissible domain we set it to zero.
For the unit ideal the empty product is one, including when `u = 0`. -/
noncomputable def chi (n : Ideal 𝒪) (u : 𝒪) : ℂ := by
  classical
  exact if Admissible n then
    ((normalizedFactors n).map (fun p ↦ primeSextic p u)).prod
  else 0

/-- The finite set of admissible column ideals of norm at most `N`. -/
noncomputable def idealBall (N : ℕ) : Finset (Ideal 𝒪) := by
  classical
  exact (Ring.HasFiniteQuotients.finite_absNorm_le (R := 𝒪) N).toFinset.filter Admissible

end ElevenTwelfths
