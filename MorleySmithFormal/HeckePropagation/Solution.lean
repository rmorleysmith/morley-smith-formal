module

public import Mathlib
public import MorleySmithFormal.HeckePropagation.Basic

/-!
# Solution: congruences are decided at the primes

Restates `Challenge.lean` verbatim and proves it from `MorleySmithFormal.HeckePropagation.Basic`.
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
    (hp : ∀ p, p.Prime → a p - b p ∈ I) (n : ℕ) : a n - b n ∈ I :=
  MorleySmithFormal.HeckePropagation.congr_of_prime I a b ha hb wa wb hra hrb hw hp n

theorem sigma_recursion (k p r : ℕ) (hp : p.Prime) :
    (σ k (p ^ (r + 2)) : ℤ) = σ k p * σ k (p ^ (r + 1)) - (p : ℤ) ^ k * σ k (p ^ r) :=
  MorleySmithFormal.HeckePropagation.sigma_recursion k p r hp

end HeckePropagation
