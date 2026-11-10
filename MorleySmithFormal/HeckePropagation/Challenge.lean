module

public import Mathlib

/-!
# Challenge: congruences are decided at the primes

Let `a` and `b` be multiplicative arithmetic functions with values in a commutative ring `R`,
each obeying a Hecke recursion at every prime `p`,

  `c(p^{r+2}) = c(p) · c(p^{r+1}) − w(p) · c(p^r)`,

with weights `wa` and `wb` congruent modulo an ideal `I` at every prime. (For a Hecke eigenform
of weight `k`, `w(p) = χ(p) p^{k−1}` at a good prime and `w(p) = 0` at a prime dividing the
level.) If `a(p) ≡ b(p) (mod I)` at every prime, then `a(n) ≡ b(n) (mod I)` for every `n`.

The second statement checks that the Eisenstein side fits: the divisor sums `σ_k` obey the
recursion with `w(p) = p^k`. (They are multiplicative: Mathlib's `isMultiplicative_sigma`.)

This file states the results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace HeckePropagation

theorem congr_of_prime {R : Type*} [CommRing R] (I : Ideal R) (a b : ArithmeticFunction R)
    (ha : a.IsMultiplicative) (hb : b.IsMultiplicative) (wa wb : ℕ → R)
    (hra : ∀ p r, p.Prime → a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - wa p * a (p ^ r))
    (hrb : ∀ p r, p.Prime → b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - wb p * b (p ^ r))
    (hw : ∀ p, p.Prime → wa p - wb p ∈ I)
    (hp : ∀ p, p.Prime → a p - b p ∈ I) (n : ℕ) : a n - b n ∈ I := by
  sorry

theorem sigma_recursion (k p r : ℕ) (hp : p.Prime) :
    (σ k (p ^ (r + 2)) : ℤ) = σ k p * σ k (p ^ (r + 1)) - (p : ℤ) ^ k * σ k (p ^ r) := by
  sorry

end HeckePropagation
