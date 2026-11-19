module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Int.ModEq

/-!
# Challenge: the Eisenstein congruence modulo 5 at level 11

Let `f(z) = η(z)² η(11z)² = q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)² = ∑ a(n) qⁿ` with `q = e^{2πiz}`, where
`η` is the Dedekind eta function (Mathlib's `ModularForm.eta`): the newform of weight 2 and
level 11 (LMFDB 11.2.a.a), whose L-function is that of the elliptic curves of conductor 11.
The statement says that `f` is a cusp form of weight 2 for `Γ₀(11)` with integer
`q`-expansion coefficients `a(n)`, and

1. `a(n) ≡ ∑_{d ∣ n, 11 ∤ d} d (mod 5)` for every `n ≥ 1`;
2. `a(p) ≡ 1 + p (mod 5)` for every prime `p ≠ 11`.

This is the weight-2, level-11 analogue of Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)`:
the cusp form is congruent to the Eisenstein series `E₂(z) − 11 E₂(11z)` modulo the numerator
`5` of `(11 − 1)/12`. Only Mathlib definitions are used. This file states the result only; the
proof is in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ElevenFive

theorem eisenstein_congruence_mod_five :
    ∃ (f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2) (a : ℕ → ℤ),
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n = (a n : ℂ)) ∧
      (∀ n : ℕ, n ≠ 0 →
        a n ≡ ∑ d ∈ n.divisors.filter (fun d ↦ ¬ 11 ∣ d), (d : ℤ) [ZMOD 5]) ∧
      ∀ p : ℕ, p.Prime → p ≠ 11 → a p ≡ 1 + p [ZMOD 5] := by
  sorry

end ElevenFive
