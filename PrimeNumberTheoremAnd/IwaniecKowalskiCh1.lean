module

public import Architect
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

open scoped ArithmeticFunction.Moebius

open scoped LSeries.notation

namespace ArithmeticFunction

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
Here we collect facts from Chapter 1 that are not already in Mathlib.
We will try to upstream as much as possible.
-/

/-- `τ` (tau) is the divisor count function, equal to `σ 0`. -/
abbrev tau : ArithmeticFunction ℕ := σ 0

@[inherit_doc tau]
scoped notation "τ" => tau

variable {R : Type*}

/--
An arithmetic function `IsAdditive` if it satisfies the property that for any two coprime natural numbers `m` and `n`, the function evaluated at their product equals the sum of the function evaluated at each number individually.
-/
@[blueprint
  "IsAdditive"
  (title := "IsAdditive")
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (title := "IsCompletelyAdditive")
  (statement := /-- Completely additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for all $m, n \ne 0$. -/)]
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive.isAdditive"
  (title := "IsCompletelyAdditive.isAdditive")
  (statement := /-- A completely additive function is additive. -/)]
lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

/-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/
@[blueprint
  "zeta_mul_zeta"
  (title := "zeta mul zeta")
  (statement := /-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/)
  (proof := /--
  By definition of $\zeta$, we have $\zeta(n) = 1$ for all $n \geq 1$. Thus, the Dirichlet convolution
  $(\zeta * \zeta)(n)$ counts the number of ways to write $n$ as a product of two positive integers,
  which is exactly the number of divisors of $n$, i.e., $\tau(n)$.
  -/)]
theorem zeta_mul_zeta : (ζ : ArithmeticFunction ℕ) * ζ = τ := by
  ext n
  rw [zeta_mul_apply, tau, sigma_zero_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun d hd => by
    simp [zeta_apply, (Nat.pos_of_mem_divisors hd).ne']

/-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/
@[blueprint
  "LSeries_tau_eq_riemannZeta_sq"
  (title := "LSeries tau eq riemannZeta sq")
  (statement := /-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/)
  (proof := /--
  From the previous theorem, we have that the Dirichlet convolution of $\zeta$ with itself is $\tau$.
  Taking L-series on both sides, we get $L(\tau, s) = L(\zeta, s) \cdot L(\zeta, s)$.
  Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, we conclude that
  $L(\tau, s) = \zeta(s)^2$ for $\Re(s) > 1$.
  -/)]
theorem LSeries_tau_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗τ) s = riemannZeta s ^ 2 := by
  have h1 : LSeries (↗(ζ * ζ)) s = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1; ext n; simp only [← natCoe_mul, natCoe_apply]
  have h2 : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s = LSeries (↗ζ) s * LSeries (↗ζ) s :=
    LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs) (LSeriesSummable_zeta_iff.mpr hs)
  rw [← zeta_mul_zeta, h1, h2, LSeries_zeta_eq_riemannZeta hs, pow_two]

/-- `d k` is the k-fold divisor function: the number of ways to write n as an ordered
    product of k natural numbers. Equivalently, the Dirichlet convolution of ζ with
    itself k times. We have `d 0 = 1` (identity), `d 1 = ζ`, `d 2 = σ 0`. -/
@[blueprint
  "d"
  (title := "d")
  (statement := /-- $d_k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/)]
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
@[blueprint
  "d_zero"
  (title := "d zero")
  (statement := /-- $d_0$ is the multiplicative identity (indicator at 1). -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/)]
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
@[blueprint
  "d_one"
  (title := "d one")
  (statement := /-- $d_1$ is $\zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d_1 = \zeta^1 = \zeta$.
  -/)]
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
@[blueprint
  "d_two"
  (title := "d two")
  (statement := /-- $d_2$ is the classical divisor count function $\tau$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d_2 = \zeta^2 = \tau$.
  -/)]
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: `d_(k+1) = d_k * ζ`. -/
@[blueprint
  "d_succ"
  (title := "d succ")
  (statement := /-- Recurrence: $d_{k+1} = d_k * \zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d_{k + 1}$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d_k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d_{k + 1} = d_k * \zeta$.
  -/)]
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series for `d k` is summable -/
@[blueprint
  "LSeries_d_summable"
  (title := "LSeries d summable")
  (statement := /-- The L-series for $d_k$ is summable for $\Re(s) > 1$. -/)
  (proof := /--
  Since $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$, and we know that the L-series of $\zeta$ converges for $\Re(s) > 1$, it follows that the L-series of $d_k$ also converges for $\Re(s) > 1$. This is because the convolution of functions with convergent L-series will also have a convergent L-series in the same region. Therefore, we can conclude that $L(d_k, s)$ is summable for $\Re(s) > 1$.
  -/)]
theorem LSeries_d_summable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (↗(d k : ArithmeticFunction ℂ)) s := by
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, one_eq_delta]
    exact (hasSum_single 1 fun n hn => by simp [LSeries.term_delta, hn]).summable
  | succ k ih =>
    rw [(LSeriesSummable_congr s (fun {n} _ => show (d (k + 1) : ArithmeticFunction ℂ) n =
      ((d k : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]))]
    exact LSeriesSummable_mul ih (LSeriesSummable_zeta_iff.mpr hs)

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (title := "LSeries d eq riemannZeta pow")
  (statement := /-- The $L$-series of $d_k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d_k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d_k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d_k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  change LSeries (↗(d k : ArithmeticFunction ℂ)) s = riemannZeta s ^ k
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, pow_zero, one_eq_delta]
    exact congr_fun LSeries_delta s
  | succ j ih =>
    have hζ : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    rw [pow_succ, LSeries_congr (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]) s,
        LSeries_mul' (LSeries_d_summable j hs) hζ, ih]
    congr 1
    exact LSeries_zeta_eq_riemannZeta hs

/-- `d k` is multiplicative for all `k`. -/
@[blueprint
  "d_isMultiplicative"
  (title := "d isMultiplicative")
  (statement := /-- $d_k$ is multiplicative for all $k$. -/)
  (proof := /--
  The function $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$. Since $\zeta$ is a multiplicative function, and the Dirichlet convolution of multiplicative functions is also multiplicative, it follows that $d_k$ is multiplicative for all $k$. This can be shown by induction on $k$, using the fact that the convolution of a multiplicative function with another multiplicative function remains multiplicative.
  -/)]
theorem d_isMultiplicative (k : ℕ) : (d k).IsMultiplicative := by
  induction k with
  | zero => rw [d_zero]; exact isMultiplicative_one
  | succ k ih =>
      rw [d_succ]
      exact ih.mul isMultiplicative_zeta

/- MOVE HELPER LEMMA ESLEWHERE?? Not used in this file, but seems potentially useful? -/

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
@[blueprint
  "d_apply_prime_pow"
  (title := "d apply prime pow")
  (statement := /-- Explicit formula: $d_k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. -/)
  (proof := /--
  The function $d_k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/)]
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  obtain ⟨k', rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k' generalizing a with
  | zero => simp [d_one, hp.ne_zero]
  | succ k' ih =>
      rw [d_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
      simp_rw [fun i ↦ ih i (succ_pos _)]
      simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k'

/-- (1.25) in Iwaniec-Kowalski: a formula for `d_k` for all `n`. -/
@[blueprint
  "d_apply"
  (title := "d apply")
  (statement := /-- (1.25) in Iwaniec-Kowalski: a formula for $d_k$ for all $n$. -/)
  (proof := /--
  The function $d_k$ is multiplicative, so to compute $d_k(n)$ for a general natural number $n$, we can factor $n$ into its prime power decomposition: $n = p_1^{a_1} p_2^{a_2} ... p_m^{a_m}$. Since $d_k$ is multiplicative, we have:

  \[
  d_k(n) = d_k(p_1^{a_1}) \cdot d_k(p_2^{a_2}) \cdot ... \cdot d_k(p_m^{a_m})
  \]

  Using the explicit formula for prime powers from the previous theorem, we can substitute to get:

  \[
  d_k(n) = \prod_{i=1}^{m} (a_i + k - 1).choose (k - 1)
  \]

  This gives us a complete formula for $d_k(n)$ in terms of the prime factorization of $n$.
  -/)]
lemma d_apply {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    d k n = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
  have hmult : (d k).IsMultiplicative := d_isMultiplicative k
  rw [hmult.multiplicative_factorization (d k) hn, prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl (fun p hp => ?_)
  simpa using d_apply_prime_pow hk (prime_of_mem_primeFactors hp) _

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
@[blueprint
  "sigmaR"
  (title := "sigmaR")
  (statement := /-- Divisor power sum with complex exponent. -/)]
noncomputable def sigmaR {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- For natural exponents, sigmaR agrees with sigma. -/
@[blueprint
  "sigmaR_natCast"
  (title := "sigmaR-natCast")
  (statement := /-- For natural exponents, $\sigma^R$ agrees with $\sigma$. -/)
  (proof := /--
  The function $\sigma^R$ is defined as the sum of the $s$-th powers of the divisors of $n$. When
  $s$ is a natural number $k$, this definition coincides with the classical divisor power sum
  function $\sigma_k(n)$, which also sums the $k$-th powers of the divisors of $n$. Therefore, for
  natural exponents, we have $\sigma^R_k(n) = \sigma_k(n)$ when we view $\sigma_k(n)$ as a complex
  number. This can be shown by directly comparing the definitions and noting that both functions sum
  over the same set of divisors with the same exponentiation.
  -/)]
lemma sigmaR_natCast (k n : ℕ) :
    σᴿ k n = σ k n := by
  unfold sigmaR sigma
  simp only [cast_id, coe_mk]

@[blueprint
  "sigmaR_apply"
  (title := "sigmaR-apply")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}d^s.$
  -/)
  (proof := /--
    This follows immediately from the definition.
  -/)]
lemma sigmaR_apply {n : ℕ} {s : ℂ} : σᴿ s n = ∑ d ∈ divisors n, (d : ℂ) ^ s := by
  rfl

@[blueprint
  "sigmaR_natCast'"
  (title := "sigmaR-natCast'")
  (statement := /--
    A casting lemma for $\sigma^R$.
  -/)]
lemma sigmaR_natCast' (k n : ℕ) :
    σᴿ (k : ℂ) n = σᴿ k n := by
  simp only [sigmaR_apply, Complex.cpow_natCast, sigmaR_natCast, sigma_apply, cast_sum, cast_pow]

@[blueprint
  "sigmaR_apply_prime_pow"
  (title := "sigmaR-apply-prime-pow")
  (statement := /--
    For a prime power, we have that $\sigma^R_s(p^i)=\sum_{j=0}^ip^{js}$.
  -/)
  (proof := /--
    Note that $d\mid p^i$ implies that $d=p^j$ with $0\leq j\leq i$. Thus,
    $$\sigma^R_s(p^i)=\sum_{d\mid p^i}d^s=\sum_{j=0}^i(p^j)^s=\sum_{j=0}^ip^{js}.$$
  -/)]
lemma sigmaR_apply_prime_pow {p i : ℕ} {s : ℂ} (hp : p.Prime) :
    σᴿ s (p ^ i) = ∑ j ∈ .range (i + 1), (p : ℂ) ^ (j * s) := by
  simp only [sigmaR_apply, divisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, cast_pow]
  congr 1
  funext x
  exact Eq.symm (Complex.natCast_cpow_natCast_mul p x s)

@[blueprint
  "sigmaR_one_apply"
  (title := "sigmaR-one-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply (n : ℕ) : σᴿ (1 : ℂ) n = ∑ d ∈ divisors n, d := by
  simp only [sigmaR_apply, Complex.cpow_one, cast_sum]

@[blueprint
  "sigmaR_one_apply_prime_pow"
  (title := "sigmaR-one-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (1 : ℂ) (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp only [sigmaR_apply_prime_pow hp, mul_one, Complex.cpow_natCast, cast_sum, cast_pow]

@[blueprint
  "sigmaR_eq_sum_div"
  (title := "sigmaR-eq-sum-div")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}(n/d)^s$.
  -/)
  (proof := /--
    Note that $d \mapsto n/d$ forms a one-to-one mapping between the divisors of $n$. Using this in
    combination with the definiton we have that
    $$\sigma^R_s(n)=\sum_{d\mid n}d^s=\sum_{d\mid n}(n/d)^s.$$
  -/)]
lemma sigmaR_eq_sum_div {n : ℕ} {s : ℂ} :
    σᴿ s n = ∑ d ∈ divisors n, ((n / d) : ℂ) ^ s := by
  rw[sigmaR_apply, ← sum_div_divisors]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw[Nat.cast_div (dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]

@[blueprint
  "sigmaR_zero_apply"
  (title := "sigmaR-zero-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply (n : ℕ) :
    σᴿ (0 : ℂ) n = #n.divisors := by
  simp only [sigmaR_apply, Complex.cpow_zero, sum_const, nsmul_eq_mul, mul_one]

@[blueprint
  "sigmaR_zero_apply_prime_pow"
  (title := "sigmaR-zero-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (0 : ℂ) (p ^ i) = i + 1 := by
  simp only [sigmaR_apply_prime_pow hp, mul_zero, Complex.cpow_zero, sum_const, card_range,
    nsmul_eq_mul, cast_add, cast_one, mul_one]

@[blueprint
  "sigmaR_one"
  (title := "sigmaR-one")
  (statement := /--
    We have that $\sigma^R_s(1)=1$.
  -/)
  (proof := /--
    By definition we have that
    $$\sigma^R_s(1)=\sum_{d \mid 1}d^s=1^s=1.$$
  -/)]
lemma sigmaR_one (s : ℂ) :
    σᴿ s 1 = 1 := by
  simp only [sigmaR_apply, divisors_one, sum_singleton, cast_one, Complex.one_cpow]

@[blueprint
  "powR"
  (title := "powR")
  (statement := /-- Arithmetic function with complex parameter $\nu$. Evaluates as $n\mapsto n^{\nu}$ for $n\neq 0$ and $0$ at $n=0$. -/)]
noncomputable def powR (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by grind⟩

@[blueprint
  "isMultiplicative_powR"
  (title := "isMultiplicative-powR")
  (statement := /--
    For fixed $\nu$ the function $n\mapsto n^\nu$ is multiplicative.
  -/)
  (proof := /--
    This immediately follows from the fact that exponentiation with a fixed power is a homomorphism.
  -/)]
theorem isMultiplicative_powR {ν : ℂ} : IsMultiplicative (powR ν) := by
  refine ⟨by simp [powR], fun {m n : ℕ} mCn => ?_⟩
  simp only [powR, ArithmeticFunction.coe_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, ↓reduceIte, mul_ite, mul_zero, ite_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, ↓reduceIte]
  have hmn_pos : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  simp only [hm.ne', hn.ne', hmn_pos, ite_false]
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n ν

@[blueprint
  "sigmaR_eq_zeta_mul_powR"
  (title := "sigmaR-eq-zeta-mul-powR")
  (statement := /-- $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$, where $\zeta$ is the constant function $1$. -/)
  (proof := /--
  The function $\sigma^R(\nu)$ is defined as the sum of the $\nu$-th powers of the divisors of $n$. The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The Dirichlet convolution of $\zeta$ (the constant function $1$) and $\text{pow}^R(\nu)$ is exactly $\sigma^R(\nu)$, since for each divisor $d$ of $n$, we have $(\zeta * \text{pow}^R(\nu))(n) = \sum_{d|n} 1 \cdot d^\nu = \sigma^R(\nu)(n)$. Thus, we have $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$.
  -/)]
lemma sigmaR_eq_zeta_mul_powR (ν : ℂ) : sigmaR ν = (zeta : ArithmeticFunction ℂ) * powR ν := by
  ext n
  rw [sigmaR_apply, coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun d hd => by
    simp [powR, (Nat.pos_of_mem_divisors hd).ne']

@[blueprint
  "isMultiplicative_sigmaR"
  (title := "isMultiplicative-sigmaR")
  (statement := /--
    For fixed $s$ function $n\mapsto\sigma^R_s(n)$ is multiplicative.
  -/)
  (proof := /--
    Recall from Lemma \ref{sigmaR-eq-zeta-mul-powR} that $\sigma^R$ is $\zeta$ convolved with
    Definition \ref{powR}. Since both of these are multiplicative functions, their convolution is
    also multiplicative.
  -/)]
lemma isMultiplicative_sigmaR {s : ℂ} :
    IsMultiplicative (σᴿ s) := by
  rw [sigmaR_eq_zeta_mul_powR]
  exact isMultiplicative_zeta.natCast.mul  isMultiplicative_powR

@[blueprint
  "sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul"
  (title := "sigmaR-eq-prod-primeFactors-sum-range-factorization-pow-mul")
  (statement := /--
    We have that
    $$\sigma^R_s(n)=\prod_{p\mid n}\sum_{j=0}^{v_p(n)}p^{js}.$$
  -/)
  (proof := /--
    Since $\sigma^R_s$ is multiplicative, it suffices to understand it at primes powers.
    $$\sigma^R_s(n)=\prod_{p\mid n}\sigma^R_s(p^{v_p(n)}).$$
    Applying Lemma \ref{sigmaR-apply-prime-pow}.
  -/)]
lemma sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul {n : ℕ} {s : ℂ} (hn : n ≠ 0) :
    σᴿ s n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), (p : ℂ) ^ (i * s) := by
  rw [isMultiplicative_sigmaR.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigmaR_apply_prime_pow <| prime_of_mem_primeFactors h

@[blueprint
  "LSeries_powR_eq"
  (title := "LSeries powR eq")
  (statement := /-- $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ for $\Re(s - \nu) > 1$.
  \begin{verbatim}
  This is IK (1.27).
  \end{verbatim}
  -/)
  (proof := /--
  The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The L-series of $\text{pow}^R(\nu)$ at $s$ is given by the sum $\sum_{n=1}^{\infty} n^{\nu - s}$. This series converges to the Riemann zeta function $\zeta(s - \nu)$ for $\Re(s - \nu) > 1$, since the zeta function is defined as $\zeta(s) = \sum_{n=1}^{\infty} n^{-s}$ for $\Re(s) > 1$. Therefore, we have $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ under the condition that $\Re(s - \nu) > 1$.
  -/)]
lemma LSeries_powR_eq (ν : ℂ) {s : ℂ} (hs : 1 < (s - ν).re) :
    LSeries (powR ν) s = riemannZeta (s - ν) := by
  convert ( LSeries_congr _ _ ) using 1;
  · rw [ zeta_eq_tsum_one_div_nat_cpow hs ];
    · refine tsum_congr fun n => ?_;
      by_cases hn : n = 0
      · simp only [LSeries.term, hn, one_div, CharP.cast_eq_zero, ↓reduceIte, inv_eq_zero, Complex.cpow_eq_zero_iff,
          ne_eq, true_and]
        exact sub_ne_zero_of_ne (by rintro rfl; norm_num at hs)
      · simp only [one_div];
        rw [← Complex.cpow_neg, neg_sub, Complex.cpow_sub];
        · exact Eq.symm (LSeries.term_of_ne_zero hn (fun n ↦ ↑n ^ ν) s)
        · exact cast_ne_zero.mpr hn
  · unfold ArithmeticFunction.powR; aesop;

@[blueprint
  "abscissa_powR_le"
  (title := "abscissa powR le")
  (statement := /-- The abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$. -/)
  (proof := /--
  We apply \ref{LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow} which states that if there exists a constant $C$ such that $\|f(n)\| \leq C \cdot n^r$ for all $n$ sufficiently large, then the abscissa of absolute convergence of $L(f, s)$ is at most $r + 1$. In our case, we can take $f(n) = n^\nu$ and observe that $\|n^\nu\| = n^{\Re(\nu)}$. Thus, we can choose $C = 1$ and $r = \Re(\nu)$, which gives us the desired result that the abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$.
  -/)]
lemma abscissa_powR_le (ν : ℂ) : LSeries.abscissaOfAbsConv (powR ν) ≤ ν.re + 1 := by
  have h_abs_le : ∀ n : ℕ, n ≠ 0 → ‖(powR ν n : ℂ)‖ ≤ (n : ℝ) ^ ν.re := by
    intros n hn_nonzero
    simp only [ArithmeticFunction.powR, hn_nonzero, coe_mk, ↓reduceIte];
    rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn_nonzero ) ]
  apply_rules [ LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ];
  exact ⟨ 1, fun n hn => by simpa using h_abs_le n hn ⟩

/-- `ζ(s)ζ(s - ν) = Σ σ_ν(n) n^(-s)` for `Re(s) > 1` and `Re(s - ν) > 1`. -/
@[blueprint
  "LSeries_sigma_eq_riemannZeta_mul"
  (title := "LSeries sigma eq riemannZeta mul")
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(σᴿ ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← LSeries_powR_eq ν hsν, sigmaR_eq_zeta_mul_powR];
  apply ArithmeticFunction.LSeries_mul
  · apply (ArithmeticFunction.abscissaOfAbsConv_zeta.trans_lt _)
    exact_mod_cast hs
  · apply lt_of_le_of_lt (abscissa_powR_le ν)
    rw[Complex.sub_re] at hsν
    exact_mod_cast (by linarith)

@[blueprint
  "two_pow_omega_le_sigma_zero"
  (title := "two-pow-omega-le-sigma-zero")
  (statement := /--
    We have the inequality $2^{\omega(n)}\leq\sigma_0(n)$ when $n\neq 0$.
  -/)
  (proof := /--
    Recall that $\omega(n)$ is the number of distinct prime factors of $n$. Thus,
    $$2^{\omega(n)}=\prod_{p|n}2.$$
    Likewise, $\sigma_0(n)$ is the number of divisors of $n$. We can write this as
    $$\prod_{p|n}(1+v_p(n))=\sigma_0(n)$$
    where $v_p(n)$ denotes the $p$-adic valuation of $n$. For $p|n$ we have that $2\leq 1+v_p(n)$.
    Thus the result immediately follows.
  -/)]
lemma two_pow_omega_le_sigma_zero {n : ℕ} (hn : n ≠ 0) :
    2 ^ (ω n) ≤ σ 0 n := by
  rw [show ω n = (Nat.primeFactors n).card from rfl, ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod
  intro p hp
  simpa [two_mul] using
  (Nat.Prime.dvd_iff_one_le_factorization (prime_of_mem_primeFactors hp) hn).mp
    (dvd_of_mem_primeFactors hp)

@[blueprint
  "LSeriesSummable_two_pow_omega"
  (title := "LSeriesSummable-two-pow-omega")
  (statement := /--
    An L-series is convergent if the absolute value of each term is term wise less than a summable series.
  -/)
  (proof := /--
    Apply triangle inequality and comparison test.
  -/)]
lemma LSeriesSummable.of_norm_le_norm {f g : ℕ → ℂ} {s : ℂ}
  (hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ g n) s n‖ ≤ ‖LSeries.term (fun n ↦ f n) s n‖)
  (hf : Summable (fun n ↦ ‖LSeries.term (fun n ↦ f n) s n‖)) : LSeriesSummable (fun n ↦ g n) s := by
  have h_fSummable : LSeriesSummable (fun n => f n) s := by
    rw [LSeriesSummable, ← summable_norm_iff]
    exact hf
  rw [LSeriesSummable, ← summable_norm_iff] at *
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => _) h_fSummable
  exact hgf

@[blueprint
  "LSeriesSummable_two_pow_omega"
  (title := "LSeriesSummable-two-pow-omega")
  (statement := /--
    The $L$-series with coefficients given by $2^{\omega(n)}$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the $L$-series with coefficients given by $\sigma_0(n)$.
  -/)]
lemma LSeriesSummable_two_pow_omega {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ 2 ^ (ω n)) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ 2 ^ ω n) s n‖ ≤ ‖LSeries.term (fun n ↦ σ 0 n) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow, Complex.norm_ofNat,
        RCLike.norm_natCast]
      exact div_le_div_of_nonneg_right (by exact_mod_cast two_pow_omega_le_sigma_zero hn) (norm_nonneg _)
  apply LSeriesSummable.of_norm_le_norm hgf
  rw [summable_norm_iff, ← LSeriesSummable]
  convert LSeries_d_summable 2 hs using 1;
  exact funext fun n => by rw [d_two]; rfl

@[blueprint
  "LSeries.term_isMultiplicative_if_fun_isMultiplicative"
  (title := "LSeries.term-isMultiplicative-if-fun-isMultiplicative")
  (statement := /--
    If $f$ is a multiplicative function, then so to is $n\mapsto f(n)/n^s$.
  -/)
  (proof := /--
    Note that $f(mn)/(mn)^s=f(m)f(n)/(m^sn^s)=(f(m)/m^s)(f(n)/n^s)$.
  -/)]
lemma LSeries.term_isMultiplicative_if_fun_isMultiplicative {f : ℕ → ℂ} (hf : (toArithmeticFunction f).IsMultiplicative) (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
  simp only [LSeries.term, _root_.mul_eq_zero, cast_mul, mul_ite, mul_zero, ite_mul, zero_mul]
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  rw[← mul_div_mul_comm, Complex.natCast_mul_natCast_cpow]
  simp only [or_self, ↓reduceIte]
  congr 1
  simpa [toArithmeticFunction, m_eq_zero, n_eq_zero] using hf.2 mCn

@[blueprint
  "powOfAdditive_isMultiplicative"
  (title := "powOfAdditive-isMultiplicative")
  (statement := /--
    If $f$ is an additive function, then so to is $n\mapsto k^{f(n)}$ for any fixed $k$.
  -/)
  (proof := /--
    Note that $k^{f(mn)}=k^{f(m)+f(n)}=k^{f(m)}k^{f(n)}$.
  -/)]
lemma powOfAdditive_isMultiplicative
    {R : Type u_1} [CommMonoidWithZero R] (k : R)
    {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (toArithmeticFunction (fun n ↦ k ^ (f n))).IsMultiplicative := by
  simp only [IsAdditive, ne_eq] at hf
  have := hf one_ne_zero one_ne_zero (coprime_one_right 1)
  rw [mul_one, left_eq_add] at this
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, this,
    pow_zero, mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf m_eq_zero n_eq_zero mCn, pow_add]

@[blueprint
  "two_pow_omega_isMultiplicative"
  (title := "two-pow-omega-isMultiplicative")
  (statement := /--
    The function $n\mapsto 2^{\omega(n)}$ is multiplicative.
  -/)
  (proof := /--
    This follows directly from Lemma \ref{powOfAdditive-isMultiplicative} and the fact that $\omega(mn)=\omega(m)+\omega(n)$.
  -/)]
lemma two_pow_omega_isMultiplicative :
    (toArithmeticFunction (fun n ↦ (2 : ℂ) ^ ω n)).IsMultiplicative := by
  exact powOfAdditive_isMultiplicative 2 (fun hm hn h => ArithmeticFunction.cardDistinctFactors_mul h)

@[blueprint
  "two_pow_omega_LSeries.term_isMultiplicative"
  (title := "two-pow-omega-LSeries.term-isMultiplicative")
  (statement := /--
    We have that $n\mapsto 2^{\omega(n)}/n^{s}$ is a multiplicative function.
  -/)
  (proof := /--
    Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{two-pow-omega-isMultiplicative}.
  -/)]
lemma two_pow_omega_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ 2 ^ (ω n)) s (m * n) =
  LSeries.term (fun n ↦ 2 ^ (ω n)) s m * LSeries.term (fun n ↦ 2 ^ (ω n)) s n := by
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative two_pow_omega_isMultiplicative s mCn

@[blueprint
  "sumOnPrimePows"
  (title := "sumOnPrimePows")
  (statement := /--
    Shorthand for the sum of a function $f:\mathbb{N}\to\mathbb{C}$ at prime powers for a prime $p$.
  -/)]
noncomputable def sumOnPrimePows (f : ℕ → ℂ) (p : Primes) : ℂ := ∑' e, f (p ^ e)

@[blueprint
  "sumOnPrimePows_apply"
  (title := "sumOnPrimePows-apply")
  (statement := /--
    Helper lemma for sumOnPrimePows that rewrites the shorthand as its sum.
  -/)]
lemma sumOnPrimePows_apply (f : ℕ → ℂ) (p : Primes) :
  sumOnPrimePows f p = ∑' e, f (p ^ e) := by rfl

@[blueprint
  "two_pow_omega_tsum_prime_pow"
  (title := "two-pow-omega-tsum-prime-pow")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=\frac{1+p^{-s}}{1-p^{-s}}.$$
  -/)
  (proof := /--
    Note that $\omega(p^0)=0$ and $\omega(p^k)=1$ whenever $0<k$. Thus,
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=1+2p^{-s}+2p^{-2s}+\ldots.$$
    Now apply a geometric sum to the non-constant terms and simplify. We have the necessary
    convergence as $1<\Re(s)$.
  -/)]
lemma two_pow_omega_tsum_prime_pow {s : ℂ} (hs : 1 < s.re)
    (p : Primes) : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  have h_rw : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = 1 + ∑' e : ℕ, LSeries.term (fun n : ℕ => 2 ^ (ω n)) s (p.val ^ (e + 1)) := by
    rw [sumOnPrimePows_apply, Summable.tsum_eq_zero_add];
    · unfold LSeries.term
      simp [Nat.Prime.ne_zero p.prop]
    · have := LSeriesSummable_two_pow_omega hs;
      convert! this.comp_injective (show Function.Injective (fun e : ℕ => p.val ^ e) from fun a b h => Nat.pow_right_injective p.prop.one_lt h) using 1
  have h_term_eval : ∀ e : ℕ, LSeries.term (fun n : ℕ => 2 ^ ω n) s (p.val ^ (e + 1)) = 2 * (p.val : ℂ) ^ (-(e + 1) * s) := by
    intro e
    simp only [neg_mul, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte]
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow p.prop, pow_one]
    · simp only [Complex.cpow_neg, div_eq_mul_inv, ← Complex.natCast_cpow_natCast_mul, cast_add, cast_one]
    · linarith
  have geo_series_rw : ∑' e : ℕ, (p.val : ℂ) ^ (-(e + 1) * s) = (p.val : ℂ) ^ (-s) / (1 - (p.val : ℂ) ^ (-s)) := by
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one]
    · rw [← tsum_mul_left]; congr; ext n; rw [← Complex.cpow_nat_mul]; ring_nf
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]; ring_nf
    · rw [Complex.norm_cpow_of_ne_zero] <;> norm_num [p.2.ne_zero]
      exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt (mod_cast p.2.one_lt) (neg_lt_zero.mpr (by linarith))) (by norm_num)
  simp only [h_rw, h_term_eval, geo_series_rw, tsum_mul_left]
  rw [eq_div_iff, add_mul, one_mul, ← mul_div_assoc, div_mul_cancel₀]
  · ring_nf
  all_goals (exact Complex.one_sub_prime_cpow_ne_zero p.2 hs)

@[blueprint
  "Complex.one_add_prime_cpow_ne_zero"
  (title := "Complex.one-add-prime-cpow-ne-zero")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that $1+p^{-s}\neq 0$. The naming convention is to mimic
    \begin{verbatim}
      Complex.one_sub_prime_cpow_ne_zero
    \end{verbatim}
  -/)
  (proof := /--
    Suppose for contradiction $1+p^{-s}=0$, then $|p^{-s}|=1$. However, this can not happen per
    \begin{verbatim}
      Complex.norm_prime_cpow_le_one_half
    \end{verbatim}
  -/)]
lemma Complex.one_add_prime_cpow_ne_zero {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    1 + (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have one_add_prime_cpow_h : ‖(p : ℂ) ^ (-s)‖ = 1 := by
    have := congr_arg norm (neg_eq_of_add_eq_zero_left h)
    simp only [norm_neg, one_mem, CStarRing.norm_of_mem_unitary] at this
    exact this
  linarith [Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs]

@[blueprint
  "two_pow_omega_LSeries_eulerProduct_tprod"
  (title := "two-pow-omega-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
lemma two_pow_omega_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ 2 ^ (ω n)) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  convert! HasProd.tprod_eq ( EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _ ) |> Eq.symm using 1
  · apply tprod_congr
    simp only [← two_pow_omega_tsum_prime_pow hs, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert! (LSeriesSummable_two_pow_omega hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

@[blueprint
  "two_pow_omega_LSeries_eulerProduct_hasProd"
  (title := "two-pow-omega-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
lemma two_pow_omega_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s)) / (1 - ↑↑p ^ (-s))) (L (fun n ↦ (2 ^ ω n)) s) := by
  convert! EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (2 ^ ω n)) s) using 1;
  · funext p; exact Eq.symm (two_pow_omega_tsum_prime_pow hs p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert! (LSeriesSummable_two_pow_omega hs).norm using 1

/--
Zeta squared:
`ζ(s)^2 = ζ(2*s) * ∑_n (2^omega(n)) n^(-s)`,
where omega is the number of distinct prime factors.
-/
@[blueprint
  "zeta_pow_two"
  (title := "zeta pow two")
  (statement := /--
  $$\zeta(s)^2 =\zeta(2s) \sum_{n=1}^{\infty} 2^{\omega(n)} n^{-s}$$ for $\Re(s) > 1$.
  \begin{verbatim}
    An expression for `ζ^2`, in IK (1.31).
  \end{verbatim}
  -/)
  (proof := /--
    Note that
    $$\zeta(s)^2=\prod_p\frac{1}{(1-p^{-s})^2}.$$
    Similarly
    $$\zeta(2s)=\prod_p\frac{1}{(1-p^{-2s})}.$$
    Applying Theorems \ref{two-pow-omega-LSeries-eulerProduct-tprod} and \ref{two-pow-omega-LSeries-eulerProduct-hasProd} we have
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    Thus
    $$\zeta(2s)\left(\sum_{1\leq n}2^{\omega(n)}n^{-s}\right)=\prod_p\frac{1+p^{-s}}{(1-p^{-s})(1-p^{-2s})}=\prod_p\frac{1}{(1-p^{-s})^2}$$
    by the difference of squares. This is exactly the Euler product for $\zeta(s)^2$ mentioned earlier.
  -/)]
lemma zeta_pow_two (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
    riemannZeta (2 * s) * LSeries (fun n ↦ 2 ^ (ω n)) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [sq, ← riemannZeta_eulerProduct_tprod hs, ← Multipliable.tprod_mul mulable mulable,
    mul_comm, ← riemannZeta_eulerProduct_tprod hs',
    two_pow_omega_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨LSeries (fun n ↦ 2 ^ (ω n)) s, two_pow_omega_LSeries_eulerProduct_hasProd s hs⟩
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩

@[blueprint
  "LSeriesSummable_moebius_sq"
  (title := "LSeriesSummable-moebius-sq")
  (statement := /--
    The $L$-series with coefficients given by $\mu^2(n)$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the Riemann zeta function.
  -/)]
lemma LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (μ n) ^ 2) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ (μ n) ^ 2) s n‖ ≤ ‖LSeries.term (fun n ↦ 1) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Complex.norm_intCast, sq_abs, one_mem, CStarRing.norm_of_mem_unitary,
        sq_le_one_iff_abs_le_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have zetaSummable : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  rw [LSeriesSummable, ← summable_norm_iff] at zetaSummable;
  apply LSeriesSummable.of_norm_le_norm hgf zetaSummable

@[blueprint
  "powOfMultiplicative_isMultiplicative"
  (title := "powOfMultiplicative-isMultiplicative")
  (statement := /--
    If $f$ is a multiplicative function, then so to is $n\mapsto f(n)^k$ for any $k\in\mathbb{N}$.
  -/)
  (proof := /--
    Note that $f(mn)^k=(f(m)f(n))^k=(f(m)^k)(f(n)^k)$.
  -/)]
lemma powOfMultiplicative_isMultiplicative {R : Type u_1} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (k : ℕ) :
    (toArithmeticFunction (fun n ↦ (f n) ^ k)).IsMultiplicative := by
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, _root_.mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, hf.1, one_pow, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf.2 mCn, mul_pow]

@[blueprint
  "moebius_sq_LSeries.term_isMultiplicative"
  (title := "moebius-sq-LSeries.term-isMultiplicative")
  (statement := /--
    We have that $n\mapsto \mu^2(n)/n^{s}$ is a multiplicative function.
  -/)
  (proof := /--
    Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{moebius-sq-isMultiplicative}.
  -/)]
lemma moebius_sq_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ (μ n) ^ 2) s (m * n) =
  LSeries.term (fun n ↦ (μ n) ^ 2) s m * LSeries.term (fun n ↦ (μ n) ^ 2) s n := by
  simp only [← intCoe_apply]
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative (powOfMultiplicative_isMultiplicative (ArithmeticFunction.IsMultiplicative.intCast isMultiplicative_moebius) 2) s mCn

@[blueprint
  "moebius_sq_tsum_prime_pow"
  (title := "moebius-sq-tsum-prime-pow")
  (statement := /--
    For $p$ prime, we have that
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)
  (proof := /--
    Note that $\mu^2(p^0)=1$ and $\mu^2(p^1)=1$ but $\mu^2(p^k)=0$ whenever $1<k$. Thus,
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)]
lemma moebius_sq_tsum_prime_pow {s : ℂ} (p : Nat.Primes) :
    sumOnPrimePows (LSeries.term (fun n ↦ (μ n) ^ 2) s) p = (1 + (p : ℂ) ^ (-s)) := by
  have h_rw : 1 + ↑↑p ^ (-s) = ∑' (e : ℕ), (if e ≤ 1 then 1 else 0) / ((p : ℂ) ^ e) ^ s := by
    rw [tsum_eq_sum (s := {0, 1})]
    · simp only [mem_singleton, zero_ne_one, not_false_eq_true, sum_insert, _root_.zero_le,
        ↓reduceIte, pow_zero, Complex.one_cpow, ne_eq, one_ne_zero, div_self, sum_singleton,
        le_refl, pow_one, one_div, Complex.cpow_neg]
    · intro e he; simp at he
      simp [show ¬e ≤ 1 by omega]
  simp only [sumOnPrimePows_apply, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte, ← Int.cast_pow, moebius_sq, h_rw]
  apply tsum_congr
  intro e
  congr 1
  by_cases h : (e ≤ 1) <;> simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, h, ↓reduceIte, ite_eq_left_iff,
    zero_ne_one, imp_false, Decidable.not_not, ite_eq_right_iff, one_ne_zero, imp_false]
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    interval_cases e
    · simp only [zero_mul, zero_le, implies_true]
    · simp only [one_mul, ← Nat.squarefree_iff_factorization_le_one (Nat.Prime.ne_zero p.prop)]
      exact (Nat.squarefree_and_prime_pow_iff_prime.mpr p.prop).1
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, not_forall, not_le]
    use p
    simp only [Nat.Prime.factorization_self p.prop, mul_one]
    exact Nat.lt_of_not_le h

@[blueprint
  "moebius_sq_LSeries_eulerProduct_tprod"
  (title := "moebius-sq-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
lemma moebius_sq_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ (μ n) ^ 2) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) := by
  convert! (EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _).tprod_eq.symm using 1
  · apply tprod_congr
    simp only [← moebius_sq_tsum_prime_pow, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert! (LSeriesSummable_moebius_sq hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

@[blueprint
  "moebius_sq_LSeries_eulerProduct_hasProd"
  (title := "moebius-sq-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
lemma moebius_sq_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s))) (L (fun n ↦ (μ n) ^ 2) s) := by
  convert! EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (μ n) ^ 2) s) using 1;
  · funext p; exact Eq.symm (moebius_sq_tsum_prime_pow p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert! (LSeriesSummable_moebius_sq hs).norm using 1

-- **Zulip question** Do we want `|μ n| = μ^2 (n)` to be a standalone function? It is the indicator
-- of `n` being squarefree.

/--
Zeta alt:
`ζ(s) = ζ(2*s) * ∑_n (|μ(n)|) n^(-s)`,
where omega is the number of distinct prime factors. -/
@[blueprint
  "zeta_alt"
  (title := "zeta alt")
  (statement := /--
  $$\zeta(s) =\zeta(2s) \sum_{n=1}^{\infty}\mu^2(n)n^{-s}.$$
  \begin{verbatim}
    An expression for `ζ`, in IK (1.32).
  \end{verbatim}
  -/)
  (proof := /--
  The series $\sum_{n=1}^{\infty}\mu^2(n)n^{-s}$ has Euler product $\prod_{p} (1 + p^{-s})$. On the other hand, $\zeta(2s)=\prod_p (1 - p^{-2s})^{-1}$. The product of these two Euler products is $\prod_p (1 - p^{-s})^{-1} = \zeta(s)$, which gives the desired formula.
  -/)]
lemma zeta_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
    riemannZeta (2 * s) * LSeries (fun (n : ℕ) ↦ (μ n : ℂ) ^ 2) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [← riemannZeta_eulerProduct_tprod hs, ← riemannZeta_eulerProduct_tprod hs',
    moebius_sq_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩
  · exact ⟨LSeries (fun n ↦ (μ n) ^ 2) s, moebius_sq_LSeries_eulerProduct_hasProd s hs⟩

@[blueprint
  "pow_divisors_mul"
  (title := "pow-divisors-mul")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers and let $k$ be fixed. The divisors $x$ of $mn$ with
    $x^k \mid mn$ are exactly the products $ab$ where $a \mid m$, $a^k \mid m$, $b \mid n$, and
    $b^k \mid n$.
  -/)
  (proof := /--
    Since $m$ and $n$ are coprime, every divisor of $mn$ factors uniquely as $ab$ with $a \mid m$
    and $b \mid n$. For such a factorization, $x^k \mid mn$ is equivalent to $a^k \mid m$ and
    $b^k \mid n$, again by coprimality.
  -/)]
lemma pow_divisors_mul {m n k : ℕ} (hmn : Nat.Coprime m n) :
    (m * n).divisors.filter (fun x => x ^ k ∣ m * n) =
    (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)).image
      (fun p => p.1 * p.2) := by
  ext x
  simp only [mem_image, mem_product, mem_filter, mem_divisors, ne_eq, Prod.exists]
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = x := Nat.dvd_mul.mp hx.1.1
    simp only [mul_eq_zero, not_or, ← hab, mul_pow] at hx
    exact ⟨a, b, ⟨⟨⟨⟨ha, hx.1.2.1⟩, (hmn.coprime_dvd_left ha).pow_left k |>.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx.2)⟩,
      ⟨⟨hb, hx.1.2.2⟩, (hmn.symm.coprime_dvd_left hb).pow_left k |>.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx.2)⟩⟩, hab⟩⟩
  · intro ⟨a, b, hab⟩
    rw[← hab.2, mul_pow]
    exact ⟨⟨Nat.mul_dvd_mul hab.1.1.1.1 hab.1.2.1.1, Nat.mul_ne_zero_iff.mpr ⟨hab.1.1.1.2, hab.1.2.1.2⟩⟩, mul_dvd_mul hab.1.1.2 hab.1.2.2⟩

@[blueprint
  "sum_moebius_sq_divisors"
  (title := "sum-moebius-sq-divisors")
  (statement := /-- The function $n \mapsto \sum_{d^2|n} \mu(d)$. -/)]
noncomputable def sum_moebius_sq_divisors : ArithmeticFunction ℤ where
  toFun := fun n ↦ ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d
  map_zero' := by simp

@[blueprint
  "sum_moebius_sq_divisors_apply"
  (title := "sum-moebius-sq-divisors-apply")
  (statement := /-- A simple helper lemma for the above definition. -/)]
lemma sum_moebius_sq_divisors_apply (n : ℕ) :
  sum_moebius_sq_divisors n = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by rfl

@[blueprint
  "sum_moebius_sq_divisors_apply_prime_pow"
  (title := "sum-moebius-sq-divisors-apply-prime-pow")
  (statement := /-- Applied at prime powers, sum-moebius-sq-divisors coincides with $\mu^2$. -/)
  (proof := /--
    For a prime power $p^k$, note that if $k\leq 1$ then the only square divisor is $1$, so the sum
    evaluates as $\mu(1)=1$. If $k\geq 2$, then $1$ and $p^2$ are square divisors of $p^k$. Thus,
    the sum evaluates as $\mu(1)+\mu(p)+\ldots$ where the remaining terms are moebius of higher
    powers (if necessary). Since $\mu(p)=-1$ and $\mu$ of higher powers of $p$ is zero, this is
    $0$. This agrees with $\mu(p^k)^2$, which is simply an indicator function for $k\leq 1$ (i.e.
    $p^k$ is squarefree).
  -/)]
lemma sum_moebius_sq_divisors_apply_prime_pow {p k : ℕ} (hp : Nat.Prime p) :
  sum_moebius_sq_divisors (p ^ k) = (μ (p ^ k)) ^ 2 := by
  have h_filter : ((Nat.divisors (p ^ k)).filter (fun x => x ^ 2 ∣ p ^ k)) = Finset.image (fun j => p ^ j) (Finset.range (k / 2 + 1)) := by
    ext; simp only [Nat.divisors_prime_pow hp, mem_filter, mem_map, mem_range, Order.lt_add_one_iff, Function.Embedding.coeFn_mk, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨a, Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by
        rw [← pow_mul] at h
        exact Nat.le_of_not_lt fun ha' => absurd (Nat.le_of_dvd (pow_pos hp.pos _) h)
          (not_le_of_gt (pow_lt_pow_right₀ hp.one_lt ha')), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by omega, rfl⟩, by rw [← pow_mul]; exact pow_dvd_pow _ (by omega)⟩
  simp only [moebius_sq, sum_moebius_sq_divisors_apply, h_filter]
  rw [Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective hp.two_le hab, Finset.sum_range_succ']
  split_ifs with h
  · have hk : k / 2 = 0 := by
      rw [Nat.div_eq_zero_iff, or_iff_right (two_ne_zero)]
      by_contra hk
      exact absurd h (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; exact not_and_of_not_right _ (by linarith))
    simp [hk]
  · simp only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one]
    rcases k with _ | _ | _
    · simp at ⊢ h
    · simp [hp.squarefree] at ⊢ h
    · simp_all +decide [ArithmeticFunction.moebius_apply_prime_pow]

/--
Liouville function:
`λ(n) = (-1)^Ω(n)`. -/
@[blueprint
  "liouville"
  (title := "liouville")
  (statement := /-- Liouville function: $\lambda(n) = (-1)^{\Omega(n)}$. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ is the total number of prime factors of $n$ counted with multiplicity. This means that for each prime factor of $n$, we contribute a factor of $-1$ to the product, and the overall sign of $\lambda(n)$ depends on whether the total number of prime factors is even or odd. Thus, we have $\lambda(n) = (-1)^{\Omega(n)}$ by definition.
  -/)]
def liouville : ArithmeticFunction ℤ :=
  toArithmeticFunction (fun n => (-1 : ℤ) ^ Ω n)

-- **NOTE:** `def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
--  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b` exists in the `SelbergBound` file.

/--
Define Complete Multiplicativity for an arithmetic function. -/
@[blueprint
  "IsCompletelyMultiplicative"
  (title := "IsCompletelyMultiplicative")
  (statement := /-- Define Complete Multiplicativity for an arithmetic function. -/)]
def IsCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

/-- A function that is completely multiplicative is also multiplicative. -/
@[blueprint
  "IsCompletelyMultiplicative.isMultiplicative"
  (title := "IsCompletelyMultiplicative.isMultiplicative")
  (statement := /-- A function that is completely multiplicative is also multiplicative. -/)
  (proof := /--
  Let $f$ be a completely multiplicative function. To show that $f$ is multiplicative, we need to verify that $f(1) = 1$ and that $f(ab) = f(a)f(b)$ for all coprime natural numbers $a$ and $b$. Since $f$ is completely multiplicative, we have $f(1) = 1$ by definition. For coprime $a$ and $b$, we can write $ab$ as a product of prime factors, and since $f$ is completely multiplicative, it will factor as the product of the values of $f$ at those prime factors. This means that $f(ab) = f(a)f(b)$ for coprime $a$ and $b$, which shows that $f$ is multiplicative.
  -/)]
lemma IsCompletelyMultiplicative.isMultiplicative {f : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative := by
  exact ⟨hf.1, fun {m n} _ => hf.2 m n⟩

end ArithmeticFunction
