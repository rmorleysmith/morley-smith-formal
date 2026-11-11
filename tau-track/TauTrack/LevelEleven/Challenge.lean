module

public import Mathlib

/-!
# Challenge: the newform of weight 2 and level 11

Let `f(z) = η(z)² η(11z)² = q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²` with `q = e^{2πiz}`, where `η` is the
Dedekind eta function (Mathlib's `ModularForm.eta`). This is the newform with LMFDB label
11.2.a.a. The statement says:

1. `f` is a cusp form of weight 2 for `Γ₀(11)`, with integer `q`-expansion coefficients `a(n)`,
   `a(1) = 1` and `a(2) = −2`;
2. `f` spans the cusp forms of weight 2 for `Γ₀(11)`: every such cusp form `g` is `a₁(g) · f`;
3. a modular form of weight 2 for `Γ₀(11)` whose `q`-expansion agrees with that of `f` up to
   `q²` (the Sturm bound) is equal to `f`;
4. `a(m) a(n) = ∑_{d ∣ (m, n), 11 ∤ d} d · a(mn/d²)` for all `m` and all `n ≠ 0`;
5. `a(mn) = a(m) a(n)` for coprime `m`, `n`;
6. `a(p^(r+2)) = a(p) a(p^(r+1)) − p · a(p^r)` for every prime `p ≠ 11`;
7. `a(11^(r+1)) = a(11) a(11^r)`.

Properties 4 to 7 say that `f` is an eigenform of the Hecke operators; they are stated on the
coefficients because Mathlib has no Hecke operators at level 11. Only Mathlib definitions are
used. This file states the result only; the proof is in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace LevelEleven

theorem exists_newform :
    ∃ (f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2) (a : ℕ → ℤ),
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n = (a n : ℂ)) ∧
      a 1 = 1 ∧ a 2 = -2 ∧
      (∀ g : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2, g = (qExpansion 1 g).coeff 1 • f) ∧
      (∀ g : ModularForm ((Gamma0 11).map (mapGL ℝ)) 2,
        (∀ i ≤ 2, (qExpansion 1 g).coeff i = (a i : ℂ)) → ∀ z : ℍ, g z = f z) ∧
      (∀ m n : ℕ, n ≠ 0 → a m * a n = ∑ d ∈ (m.gcd n).divisors,
        (if 11 ∣ d then 0 else (d : ℤ)) * a (m * n / d ^ 2)) ∧
      (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧
      (∀ p r : ℕ, p.Prime → p ≠ 11 →
        a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℤ) * a (p ^ r)) ∧
      ∀ r : ℕ, a (11 ^ (r + 1)) = a 11 * a (11 ^ r) := by
  sorry

end LevelEleven
