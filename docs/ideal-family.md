# Ideal-indexed family and blueprint notes

These notes preserve the ideal-indexed development in
`ElevenTwelfths.IdealFamily`, with arithmetic in `IdealArithmetic.lean`.
The shared field, ring of integers, and root of unity come from `Arithmetic.lean`.
The public proof assembly and its current status are described in
[argument.md](argument.md). The character selector below is a separate
construction; its identification with the public proof's character remains a
proof obligation. The prime-amplifier route below is an exposition plan;
the public proof uses an all-element, totient-weighted amplifier.

# The 11/12 argument, with Lean landmarks

The [side-by-side blueprint](../blueprint/index.html) now presents the complete
twelve-beat proof spine. This document preserves the earlier ideal-indexed
prototype, pairing its own definitions with the corresponding mathematics.

## 1. Basic arithmetic objects

Let \(\omega\) be a primitive cube root of unity. We work with
\(K=\mathbb Q(\omega)=\mathbb Q(\sqrt{-3})\) and its ring of integers
\(\mathcal O=\mathbb Z[\omega]\). Lean uses `CyclotomicField 3 ℚ` and
`NumberField.RingOfIntegers K`, with a fixed complex embedding.

There are two kinds of norms:

- For a nonzero integral ideal, \(\mathrm N\mathfrak n=\#(\mathcal O/\mathfrak n)\).
- For an element \(u=a+b\omega\),
  \(\mathrm N(u)=u\bar u=|u|^2=a^2-ab+b^2\).

They agree on principal ideals: \(\mathrm N((u))=\mathrm N(u)\).
We use mathlib's `Ideal.absNorm` directly, without a project wrapper. Its
underlying function is `Submodule.cardQuot`, the cardinality of the quotient. `elementNorm` is the norm of
`Ideal.span {u}`; `elementNorm_eq` and `complex_norm_sq` prove its compatibility
with the algebraic norm and squared complex absolute value. The explicit
coordinate identification with \(a+b\omega\) remains to be formalized.

For a nonzero ideal \(\mathfrak n=\prod_{j=1}^r\mathfrak p_j^{e_j}\), define
\(\mu_K(\mathfrak n)=(-1)^r\) if all exponents are one, and zero otherwise.
Thus \(\mu_K(\mathcal O)=1\). `mobiusK` uses squarefreeness and the multiset
of prime-ideal factors. Its value at the zero ideal is defined as zero.
It is not the integer Möbius function applied to the ideal norm.

These definitions are in [IdealArithmetic.lean](../ElevenTwelfths/IdealArithmetic.lean).

## 2. Sextic characters and the two summation variables

The [OpenAI source, Sections 2–4](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex)
uses column ideals prime to a fixed set of primes containing those above 2 and
3 and the conductor of its auxiliary Hecke character. We omit that auxiliary
character and take the excluded primes to be those above 6.

For a nonzero prime ideal \(\mathfrak p\nmid(6)\), let
\(q=\mathrm N\mathfrak p\). If \(u\in\mathfrak p\), set
\(\chi_{\mathfrak p}(u)=0\). Otherwise \(\chi_{\mathfrak p}(u)\) is the unique
sixth root of unity congruent to \(u^{(q-1)/6}\) modulo \(\mathfrak p\).
For \(\mathfrak n\) prime to \((6)\), define

\[
\chi_{\mathfrak n}(u)=\left(\frac{u}{\mathfrak n}\right)_6
 =\prod_{\mathfrak p^{e_{\mathfrak p}}\parallel\mathfrak n}
   \chi_{\mathfrak p}(u)^{e_{\mathfrak p}}.
\]

The unit ideal gives the empty product, so \(\chi_{\mathcal O}(u)=1\),
including for \(u=0\). For other admissible ideals, the character is zero
when \((u)+\mathfrak n\ne\mathcal O\). We define it to be zero outside the
admissible denominator domain, which is excluded from the sums anyway.

`primeSextic` implements the residue-field rule by summing the matching root
among the six powers of `-ω`; `chi` multiplies over prime-ideal factors
with multiplicity. The unique-root property and character identities remain
proof obligations, not axioms.

**Columns are ideals; rows are elements.** The paper sometimes writes the
column ideal as its unique primary generator \(n\equiv1\pmod{3\mathcal O}\).
In that notation, \(\mu_K(n)=\mu_K((n))\) and \(\chi_n=\chi_{(n)}\), and each
ideal is counted once. `Primary` records this congruence, but our ideal sums
do not require a generator choice. The generator correspondence is a future
arithmetic lemma.

The row variable \(u\) ranges over all of \(\mathcal O\), not just primary,
squarefree, or coprime elements. All six associates occur as distinct lattice
points. This is the full lattice used for Poisson summation.

## 3. The Möbius partial sums and their mean square

Fix a smooth complex weight \(W\) supported on \([1/2,1]\), and a nonnegative
real smooth weight \(V\) with the same support. We use \(M\) for Möbius partial
sums throughout this project:

\[
M_u(N)=\sum_{\substack{0\ne\mathfrak n\subseteq\mathcal O\\
                      (\mathfrak n,(6))=1}}
 \mu_K(\mathfrak n)\chi_{\mathfrak n}(u)
 W\!\left(\frac{\mathrm N\mathfrak n}{N}\right),
\qquad
S(N,H)=\sum_{u\in\mathcal O}
 V\!\left(\frac{\mathrm N(u)}H\right)|M_u(N)|^2.
\]

For positive scales only \(N/2\le\mathrm N\mathfrak n\le N\) and
\(H/2\le\mathrm N(u)\le H\) contribute. The zero row contributes zero since
\(V(0)=0\). The weight structures stay in the implementation; they do not
need their own definition entries in the blueprint.

```lean
noncomputable def M (W : SmoothDyadicWeight ℂ) (u : 𝒪) (N : ℕ) : ℂ :=
  ∑ n ∈ idealBall N,
    (mobiusK n : ℂ) * chi n u * W ((Ideal.absNorm n : ℝ) / (N : ℝ))

noncomputable def S (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : ℝ :=
  ∑ u ∈ rowBall H, V ((elementNorm u : ℝ) / (H : ℝ)) * ‖M W u N‖ ^ 2
```

`idealBall N` is the finite set of admissible ideals of norm at most `N`.
`rowBall H` contains every lattice element of norm at most `H`; its finiteness
is proved for the actual ring, rather than supplied as an input. No norm,
Möbius function, or character is passed into `M`.

In [IdealFamily.lean](../ElevenTwelfths/IdealFamily.lean), compact support
proves the whole-lattice form:

```lean
theorem S_eq_tsum (W : SmoothDyadicWeight ℂ) (V : SmoothDyadicCutoff)
    (N H : ℕ) : S W V N H =
      ∑' u : 𝒪, V ((elementNorm u : ℝ) / (H : ℝ)) * ‖M W u N‖ ^ 2
```

The reference paper's Poisson argument uses a Schwartz majorant for the full
row ball; our dyadic cutoff is a localization convention. Relating the desired
ball estimate to these smooth localizations remains part of the analytic work.
When opening the square introduces a row coprimality indicator, the paper uses
inclusion–exclusion and then applies Poisson on lattice residue classes.
The ideal-denominator restriction does not remove rows from the lattice.

## 4. The omitted Euler factors

For \(\operatorname{Re}(s)>1\), the untwisted ideal series is

\[
\sum_{(\mathfrak n,(6))=1}\frac{\mu_K(\mathfrak n)}{(\mathrm N\mathfrak n)^s}
 =\frac{1}{\zeta_K(s)(1-4^{-s})(1-3^{-s})}.
\]

The prime above 2 has norm 4 and the prime above 3 has norm 3. The omitted
factors are nonzero in \(\operatorname{Re}(s)>0\). Their restoration and the
passage from ideal Möbius cancellation to zeta nonvanishing are still to be
formalized; they are not consequences of the definitions alone.

## Proposed next steps

1. Prove the arithmetic identities needed for the sextic characters.
2. Extract the sixth-power rows and establish amplification.
3. Open the mean square and apply Poisson summation.
4. Establish the Gauss–Jacobi conversion.
5. Identify cubic theta coefficients and prove the dual estimate.
6. Close the mean-square bound and extract the exponent \(11/12\).
7. Use the Mellin transform and restore local factors to deduce nonvanishing.
