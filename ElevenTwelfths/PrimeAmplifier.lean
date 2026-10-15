import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction

/-!
# The prime sixth-power amplifier

This is the parameterized form of OpenAI's prime-row extraction argument.
Set

`alpha = (1 + theta) / 6`.

The amplifying primes have norm about `N ^ alpha`, so their sixth powers fit
inside the row range `N ^ (1 + theta)`. The theorem below keeps `theta`
symbolic throughout the exponent calculation.
-/

namespace ElevenTwelfths

noncomputable section

open scoped BigOperators Classical

namespace PrimeAmplifier

/--
The exponent calculation at the end of prime amplification.

`J` is the number of prime sixth-power rows, `A` is the untwisted sum, and
`C * N ^ (1 - (1 + theta) / 6)` bounds the error between the untwisted row
and each prime sixth-power row.  The hypothesis `hextract` is precisely the
inequality delivered by `ShortDraft.complex_row_extraction`.
-/
theorem from_mean_square_and_prime_rows
    (N theta epsilon J A C : ℝ)
    (hN : 1 ≤ N) (htheta : 0 ≤ theta) (hepsilon : 0 ≤ epsilon)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hcount : N ^ (((1 + theta) / 6 : ℝ) - epsilon) ≤ J)
    (hextract : J * A ^ 2 ≤
      2 * N ^ ((2 + theta : ℝ) + epsilon) +
        2 * J * C ^ 2 *
          N ^ (2 * (1 - (1 + theta) / 6 : ℝ))) :
    A ≤ 2 * C *
      N ^ (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  let alpha : ℝ := (1 + theta) / 6
  let E : ℝ := (11 + 5 * theta) / 12 + epsilon
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hJpos : 0 < J :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hcount
  have hmainExponent :
      (2 + theta + epsilon : ℝ) = (alpha - epsilon) + 2 * E := by
    dsimp [alpha, E]
    ring
  have hmean : N ^ (2 + theta + epsilon) ≤ J * N ^ (2 * E) := by
    calc
      N ^ (2 + theta + epsilon) =
          N ^ (alpha - epsilon) * N ^ (2 * E) := by
            rw [← Real.rpow_add hNpos]
            rw [hmainExponent]
      _ ≤ J * N ^ (2 * E) :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hNpos.le _)
  have herrorExponent : 2 * (1 - alpha) ≤ 2 * E := by
    dsimp [alpha, E]
    linarith
  have herror : N ^ (2 * (1 - alpha)) ≤ N ^ (2 * E) :=
    Real.rpow_le_rpow_of_exponent_le hN herrorExponent
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hT : 0 ≤ J * N ^ (2 * E) := by positivity
  have hsquare : A ^ 2 ≤ 4 * C ^ 2 * N ^ (2 * E) := by
    have hbound : J * A ^ 2 ≤ 4 * J * C ^ 2 * N ^ (2 * E) := by
      calc
        J * A ^ 2 ≤
            2 * N ^ (2 + theta + epsilon) +
              2 * J * C ^ 2 * N ^ (2 * (1 - alpha)) := by
                simpa only [alpha] using hextract
        _ ≤ 2 * (J * N ^ (2 * E)) +
              2 * J * C ^ 2 * N ^ (2 * E) := by
                gcongr
        _ ≤ 4 * J * C ^ 2 * N ^ (2 * E) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hT]
    nlinarith
  have hpower : (N ^ E) ^ 2 = N ^ (2 * E) := by
    calc
      (N ^ E) ^ 2 = N ^ (E * 2) :=
        (Real.rpow_mul_natCast hNpos.le E 2).symm
      _ = N ^ (2 * E) := by congr 1; ring
  have htarget : 0 ≤ 2 * C * N ^ E := by positivity
  apply (sq_le_sq₀ hA htarget).mp
  rw [mul_pow, mul_pow, hpower]
  norm_num
  exact hsquare

/--
Prime amplification in the form used by the row family.

This applies OpenAI's reusable finite-row extraction lemma and then invokes
the symbolic exponent calculation above.  No zero-free theorem, and no
stronger final exponent from the OpenAI development, is used here.
-/
theorem from_finite_sixth_power_rows
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (N theta epsilon C : ℝ)
    (hN : 1 ≤ N) (htheta : 0 ≤ theta)
    (hepsilon : 0 ≤ epsilon) (hC : 1 ≤ C)
    (hrows : primes.image row ⊆ rows)
    (hinjective : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤
        C * N ^ (1 - (1 + theta) / 6 : ℝ))
    (hcount : N ^ (((1 + theta) / 6 : ℝ) - epsilon) ≤
      (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      N ^ ((2 + theta : ℝ) + epsilon)) :
    ‖A untwisted‖ ≤
      2 * C * N ^ (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hextract := OAI.ShortDraft.complex_row_extraction
    rows primes row A untwisted
    (C * N ^ (1 - (1 + theta) / 6 : ℝ))
    (N ^ ((2 + theta : ℝ) + epsilon))
    (by positivity) hrows hinjective happrox hmean
  have herror :
      (C * N ^ (1 - (1 + theta) / 6 : ℝ)) ^ 2 =
        C ^ 2 * N ^ (2 * (1 - (1 + theta) / 6 : ℝ)) := by
    rw [mul_pow]
    congr 1
    calc
      (N ^ (1 - (1 + theta) / 6 : ℝ)) ^ 2 =
          N ^ ((1 - (1 + theta) / 6 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hNpos.le _ 2).symm
      _ = N ^ (2 * (1 - (1 + theta) / 6 : ℝ)) := by
        congr 1; ring
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows N theta epsilon
    (primes.card : ℝ) ‖A untwisted‖ C hN htheta hepsilon
    (norm_nonneg _) hC hcount (by simpa only [mul_assoc] using hextract)

/--
The elementary error estimate for primes in the dyadic interval
`[N ^ ((1 + theta) / 6) / 2, N ^ ((1 + theta) / 6)]`.

The harmless upper bound `theta ≤ 5` says only that the complementary
exponent `1 - (1 + theta) / 6` is nonnegative.  The analytic argument uses
the much smaller range `0 < theta ≤ 1 / 10`.
-/
theorem dyadic_prime_error_bound
    (N Q : ℕ) (theta : ℝ) (hN : 1 ≤ N)
    (hthetaUpper : theta ≤ 5)
    (hQ : (N : ℝ) ^ ((1 + theta) / 6 : ℝ) / 2 ≤ (Q : ℝ)) :
    ((64 * (N / Q + 1) : ℕ) : ℝ) ≤
      192 * (N : ℝ) ^ (1 - (1 + theta) / 6 : ℝ) := by
  let alpha : ℝ := (1 + theta) / 6
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  have hscalePos : 0 < (N : ℝ) ^ alpha :=
    Real.rpow_pos_of_pos hNpos _
  have hQpos : (0 : ℝ) < Q := by
    dsimp [alpha] at hscalePos
    linarith
  have hpower :
      (N : ℝ) ^ (1 - alpha) * (N : ℝ) ^ alpha = N := by
    rw [← Real.rpow_add hNpos,
      show 1 - alpha + alpha = (1 : ℝ) by ring, Real.rpow_one]
  have hfraction : (N : ℝ) / Q ≤
      2 * (N : ℝ) ^ (1 - alpha) := by
    apply (div_le_iff₀ hQpos).mpr
    calc
      (N : ℝ) =
          (N : ℝ) ^ (1 - alpha) * (N : ℝ) ^ alpha :=
            hpower.symm
      _ = (2 * (N : ℝ) ^ (1 - alpha)) *
          ((N : ℝ) ^ alpha / 2) := by ring
      _ ≤ (2 * (N : ℝ) ^ (1 - alpha)) * Q :=
        mul_le_mul_of_nonneg_left (by simpa only [alpha] using hQ) (by positivity)
  have hcast : ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) / Q :=
    Nat.cast_div_le
  have hcomplement : 0 ≤ 1 - alpha := by
    dsimp [alpha]
    linarith
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 - alpha) :=
    Real.one_le_rpow hNreal hcomplement
  have hnatCast : ((64 * (N / Q + 1) : ℕ) : ℝ) =
      64 * (((N / Q : ℕ) : ℝ) + 1) := by
    push_cast
    ring
  rw [hnatCast]
  dsimp only [alpha] at hfraction hone ⊢
  nlinarith

/--
Primes of norm at most `N ^ ((1 + theta) / 6)` produce sixth-power rows in
the mean-square disk of radius `N ^ (1 + theta)`.
-/
theorem sixth_power_rows_in_rowNormDisk
    {β : Type*} (selected : Finset β)
    (p : β → OAI.ActualEisensteinCubic.O)
    (N H : ℕ) (theta : ℝ) (hN : 1 ≤ N)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hnormUpper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (N : ℝ) ^ ((1 + theta) / 6 : ℝ))
    (hH : Nat.floor ((N : ℝ) ^ (1 + theta : ℝ)) ≤ H) :
    selected.image (fun i ↦ p i ^ 6) ⊆
      OAI.ConcretePrimeRowBridge.rowNormDisk H := by
  classical
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [OAI.ConcretePrimeRowBridge.mem_rowNormDisk]
  have hpNorm : Ideal.absNorm (Ideal.span {p i}) ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (hp i hi))
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  have hupper : (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) ≤
      (N : ℝ) ^ (1 + theta : ℝ) := by
    calc
      (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
            exact_mod_cast
              OAI.ActualEisensteinCubic.principal_absNorm_pow (p i) 6
      _ ≤ ((N : ℝ) ^ ((1 + theta) / 6 : ℝ)) ^ 6 := by
        gcongr
        exact hnormUpper i hi
      _ = (N : ℝ) ^ (1 + theta : ℝ) := by
        rw [← Real.rpow_mul_natCast hNpos.le]
        congr 1
        ring
  constructor
  · rw [OAI.ActualEisensteinCubic.principal_absNorm_pow]
    exact pow_pos (Nat.pos_of_ne_zero hpNorm) 6
  · exact (Nat.le_floor hupper).trans hH

open OAI.ActualEisensteinCubic

/--
The generic prime amplifier specialized to OpenAI's actual Eisenstein sextic
rows.  It reuses the proved local sixth-power mask, prime-row error estimate,
and injectivity of prime sixth powers; only the exponent bookkeeping above is
new.
-/
theorem finite_actual_prime_extraction
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (N : ℕ) (theta epsilon : ℝ) (hN : 1 ≤ N)
    (htheta : 0 ≤ theta) (hthetaUpper : theta ≤ 5)
    (hepsilon : 0 ≤ epsilon)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinjective : Set.InjOn
      (fun i ↦ (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i ↦ p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolumnNorm : ∀ n ∈ columns,
      Ideal.absNorm (Ideal.span {n}) ≤ N)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormLower : ∀ i ∈ selected,
      (N : ℝ) ^ ((1 + theta) / 6 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hcount : (N : ℝ) ^ (((1 + theta) / 6 : ℝ) - epsilon) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (N : ℝ) ^ ((2 + theta : ℝ) + epsilon)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      384 * (N : ℝ) ^
        (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  classical
  let A : O → ℂ := fun u ↦
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjectiveRows :
      Set.InjOn (fun i ↦ p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i ↦ (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi
      rfl
    · exact hinjective
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤
        192 * (N : ℝ) ^ (1 - (1 + theta) / 6 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) N hsupport hcolumnNorm hweight).trans
      (dyadic_prime_error_bound N
        (Ideal.absNorm (Ideal.span {p i})) theta hN hthetaUpper
        (hnormLower i hi))
  have hbound := from_finite_sixth_power_rows
    rows selected (fun i ↦ p i ^ 6) A 1 (N : ℝ) theta epsilon 192
    (by exact_mod_cast hN) htheta hepsilon (by norm_num)
    hrows hinjectiveRows happrox hcount hmean
  simpa only [hone, show (2 : ℝ) * 192 = 384 by norm_num] using hbound

open OAI.ConcretePrimeRowBridge
open OAI.ShortDraftHeckeBridge

/--
The concrete ideal-sum interface to the generic amplifier.

Its analytic input is exactly the smooth sextic mean square over
`rowNormDisk H`; all remaining hypotheses describe the dyadic primary-prime
amplifier.  In particular, the conclusion is obtained directly from that
mean square and not from a stronger zero-free theorem.
-/
theorem baseChange_prime_extraction_from_mean_square
    {β : Type*} {q : ℕ}
    (chi : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (F : Finset (Ideal OAI.ActualEisensteinCubic.O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → OAI.ActualEisensteinCubic.O)
    (N H : ℕ) (theta epsilon : ℝ)
    (hN : 1 ≤ N) (htheta : 0 ≤ theta)
    (hthetaUpper : theta ≤ 5) (hepsilon : 0 ≤ epsilon)
    (hFnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected,
      (Ideal.span {p i} : Ideal OAI.ActualEisensteinCubic.O).IsMaximal)
    (hinjective : Set.InjOn
      (fun i ↦ (Ideal.span {p i} : Ideal OAI.ActualEisensteinCubic.O))
        (selected : Set β))
    (hnormLower : ∀ i ∈ selected,
      (N : ℝ) ^ ((1 + theta) / 6 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormUpper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (N : ℝ) ^ ((1 + theta) / 6 : ℝ))
    (hH : Nat.floor ((N : ℝ) ^ (1 + theta : ℝ)) ≤ H)
    (hcount : (N : ℝ) ^ (((1 + theta) / 6 : ℝ) - epsilon) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum F hFpos hFgood chi W u‖ ^ 2) ≤
        (N : ℝ) ^ ((2 + theta : ℝ) + epsilon)) :
    ‖∑ I ∈ F, baseChangeWeight chi I * W (Ideal.absNorm I)‖ ≤
      384 * (N : ℝ) ^
        (((11 + 5 * theta) / 12 : ℝ) + epsilon) := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  let P : primePool F → Ideal OAI.ActualEisensteinCubic.O := fun i ↦ i.1
  let support : OAI.ActualEisensteinCubic.O → Finset (primePool F) :=
    fun x ↦ idealSupport F (Ideal.span {x})
  let columns : Finset OAI.ActualEisensteinCubic.O := F.image idealGenerator
  let weight : OAI.ActualEisensteinCubic.O → ℂ := columnWeight chi W
  have hsupport : ∀ x ∈ columns, ∀ i ∈ support x, x ∈ P i := by
    intro x hx i hi
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    dsimp [support, P] at hi ⊢
    rw [span_idealGenerator I] at hi
    exact idealGenerator_mem_prime_of_support F hFpos I hIF i hi
  have hcolumnNorm : ∀ x ∈ columns,
      Ideal.absNorm (Ideal.span {x}) ≤ N := by
    intro x hx
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    rw [span_idealGenerator I]
    exact hFnorm I hIF
  have hweight : ∀ x ∈ columns, ‖weight x‖ ≤ 1 := by
    intro x hx
    exact columnWeight_norm_le_one chi W hW x
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖∑ x ∈ columns,
          weight x * finiteSquarefreeRow P (primePool_good F hFgood)
            (support x) u‖ ^ 2) ≤
        (N : ℝ) ^ ((2 + theta : ℝ) + epsilon) := by
    calc
      _ = ∑ u ∈ rowNormDisk H,
          ‖idealRowSum F hFpos hFgood chi W u‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            change ‖elementRow F hFpos hFgood chi W u‖ ^ 2 =
              ‖idealRowSum F hFpos hFgood chi W u‖ ^ 2
            rw [elementRow_eq_idealRowSum]
      _ ≤ _ := hmean
  have hrows : selected.image (fun i ↦ p i ^ 6) ⊆ rowNormDisk H :=
    sixth_power_rows_in_rowNormDisk selected p N H theta hN hp hnormUpper hH
  have hbound := finite_actual_prime_extraction
    P (primePool_good F hFgood) columns support weight selected p
    (rowNormDisk H) N theta epsilon hN htheta hthetaUpper hepsilon
    hp hprime hinjective hrows hsupport hcolumnNorm hweight hnormLower
    hcount hmean'
  have hsum :
      (∑ x ∈ columns, weight x) =
        ∑ I ∈ F, baseChangeWeight chi I * W (Ideal.absNorm I) := by
    change (∑ x ∈ F.image idealGenerator, columnWeight chi W x) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro I hIF
      exact columnWeight_idealGenerator chi W I
    · intro I hIF J hJF h
      exact idealGenerator_injective h
  rwa [hsum] at hbound

end PrimeAmplifier

end

end ElevenTwelfths
