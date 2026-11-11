module

public import Mathlib

/-!
# Challenge: Ramanujan's tau function is an integer-valued multiplicative function

The modular discriminant is `Δ(z) = q ∏ (1 − qⁿ)²⁴ = ∑ τ(n) qⁿ` with `q = e^{2πiz}`
(Mathlib's `ModularForm.discriminant`). The statement says that its coefficients are the values
of one arithmetic function `τ : ℕ → ℤ` with these properties:

1. `τ` is multiplicative: `τ(1) = 1` and `τ(mn) = τ(m) τ(n)` for coprime `m`, `n`;
2. `τ(p^(r+2)) = τ(p) τ(p^(r+1)) − p¹¹ τ(p^r)` for every prime `p`;
3. `τ(m) τ(n) = ∑_{d ∣ (m, n)} d¹¹ τ(mn/d²)` for all `m`, `n`;
4. `τ(n) ≡ σ₁₁(n) (mod 691)`.

Properties 1 and 2 were conjectured by Ramanujan (1916) and proved by Mordell (1917); 3 is
equivalent to them; 4 is Ramanujan's congruence. Only Mathlib definitions are used. This file
states the result only; the proof is in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace RamanujanTau

theorem exists_tau : ∃ τ : ArithmeticFunction ℤ,
    (∀ n : ℕ, (qExpansion 1 ModularForm.discriminant).coeff n = (τ n : ℂ)) ∧
    τ.IsMultiplicative ∧
    (∀ p r : ℕ, p.Prime → τ (p ^ (r + 2)) = τ p * τ (p ^ (r + 1)) - (p : ℤ) ^ 11 * τ (p ^ r)) ∧
    (∀ m n : ℕ, τ m * τ n = ∑ d ∈ (m.gcd n).divisors, (d : ℤ) ^ 11 * τ (m * n / d ^ 2)) ∧
    ∀ n : ℕ, τ n ≡ σ 11 n [ZMOD 691] := by
  sorry

end RamanujanTau
