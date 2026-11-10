module

public import Mathlib

/-!
# Congruences are decided at the primes

A Hecke eigenform's Fourier coefficients `c(n)` are multiplicative, and at each prime `p` they
obey the two-term recursion

  `c(p^{r+2}) = c(p) · c(p^{r+1}) − w(p) · c(p^r)`,

with `w(p) = χ(p) p^{k−1}` at a good prime and `w(p) = 0` at a prime dividing the level. So the
values at the primes decide everything. This file proves the consequence for congruences: if two
such sequences, with weights `w` that agree modulo an ideal `I`, agree modulo `I` at every
prime, then they agree modulo `I` at every `n`. A congruence is born at the primes and the
recursion carries it everywhere.

For example, Ramanujan's `τ(n) ≡ σ₁₁(n) (mod 691)` has this shape, with `w(p) = p¹¹` on both
sides.

The Eisenstein side fits the pattern: `σ_k` is multiplicative and obeys the recursion with
eigenvalue `σ_k(p) = 1 + p^k` and `w(p) = p^k` (`sigma_recursion`).

## Main results

* `MorleySmithFormal.HeckePropagation.congr_of_prime`: agreement modulo `I` at the primes implies
  agreement modulo `I` everywhere.
* `MorleySmithFormal.HeckePropagation.sigma_recursion`: the Hecke recursion for the divisor sums `σ_k`.

## References

* J.-P. Serre, *A Course in Arithmetic*, VII §5.3 (the recursion for Hecke eigenvalues).
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.3 and Proposition 5.8.5.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace MorleySmithFormal.HeckePropagation

variable {R : Type*} [CommRing R]

/-- Two sequences obeying Hecke recursions with congruent weights, starting from `1` and
congruent at `p`, are congruent at every power of `p`. -/
theorem congr_prime_pow (I : Ideal R) (a b : ℕ → R) (p : ℕ) (wa wb : R)
    (ha1 : a 1 = 1) (hb1 : b 1 = 1)
    (hra : ∀ r, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - wa * a (p ^ r))
    (hrb : ∀ r, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - wb * b (p ^ r))
    (hw : Ideal.Quotient.mk I wa = Ideal.Quotient.mk I wb)
    (hp : Ideal.Quotient.mk I (a p) = Ideal.Quotient.mk I (b p)) :
    ∀ r, Ideal.Quotient.mk I (a (p ^ r)) = Ideal.Quotient.mk I (b (p ^ r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [ha1, hb1]
    | 1 => simpa using hp
    | r + 2 =>
      rw [hra, hrb, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, hp, hw,
        ih (r + 1) (by omega), ih r (by omega)]

theorem congr_of_prime (I : Ideal R) (a b : ArithmeticFunction R)
    (ha : a.IsMultiplicative) (hb : b.IsMultiplicative) (wa wb : ℕ → R)
    (hra : ∀ p r, p.Prime → a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - wa p * a (p ^ r))
    (hrb : ∀ p r, p.Prime → b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - wb p * b (p ^ r))
    (hw : ∀ p, p.Prime → wa p - wb p ∈ I)
    (hp : ∀ p, p.Prime → a p - b p ∈ I) (n : ℕ) : a n - b n ∈ I := by
  rw [← Ideal.Quotient.eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpow : ∀ p ∈ n.primeFactors, ∀ r,
      Ideal.Quotient.mk I (a (p ^ r)) = Ideal.Quotient.mk I (b (p ^ r)) := fun p hpn =>
    have hpp := Nat.prime_of_mem_primeFactors hpn
    congr_prime_pow I a b p (wa p) (wb p) ha.map_one hb.map_one (hra p · hpp) (hrb p · hpp)
      (Ideal.Quotient.eq.mpr (hw p hpp)) (Ideal.Quotient.eq.mpr (hp p hpp))
  rw [ha.multiplicative_factorization a hn, hb.multiplicative_factorization b hn,
    map_finsuppProd, map_finsuppProd]
  exact Finset.prod_congr rfl fun p hpn => hpow p (by simpa using hpn) _

/-- The Hecke recursion for the divisor sums: `σ_k(p^{r+2}) = σ_k(p) σ_k(p^{r+1}) − p^k σ_k(p^r)`,
the coefficient recursion of the Eisenstein series `E_{k+1}` at the prime `p`. -/
theorem sigma_recursion (k p r : ℕ) (hp : p.Prime) :
    (σ k (p ^ (r + 2)) : ℤ) = σ k p * σ k (p ^ (r + 1)) - (p : ℤ) ^ k * σ k (p ^ r) := by
  have h1 : σ k p = 1 + p ^ k := by
    simpa [Finset.sum_range_succ] using sigma_apply_prime_pow (k := k) hp (i := 1)
  rw [h1, sigma_apply_prime_pow hp, sigma_apply_prime_pow hp, sigma_apply_prime_pow hp,
    Finset.sum_range_succ _ (r + 2), Finset.sum_range_succ _ (r + 1)]
  push_cast
  ring

end MorleySmithFormal.HeckePropagation
