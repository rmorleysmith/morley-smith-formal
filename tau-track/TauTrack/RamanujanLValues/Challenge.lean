module

public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Challenge: rational ratios of critical values of Ramanujan's `L`-function

Let `Δ = q ∏ (1 − qⁿ)²⁴ = ∑ τ(n) qⁿ` be the modular discriminant (Mathlib's
`CuspForm.discriminant`, a cusp form of weight 12 for `SL(2, ℤ)`), and let `L(Δ, s)` be its
`L`-function (Mathlib's `ModularForm.L`): the entire function equal to `∑ τ(n) n^{−s}` for
`Re s > 7` (Mathlib's `CuspForm.hasSum_L`). The statements say:

1. `L_four`: `L(Δ, 4) = (25 π² / 72) · L(Δ, 2)`;
2. `L_six`: `L(Δ, 6) = (π⁴ / 18) · L(Δ, 2)`;
3. `L_five`: `L(Δ, 5) = (3 π² / 14) · L(Δ, 3)`.

These are instances of Manin's theorem on the periods of `Δ`: the values of `L(Δ, s)` at the
integers `2, 4, 6, 8, 10` are rational multiples of one another up to powers of `π`, and likewise
at `3, 5, 7, 9`. Only Mathlib definitions are used. This file states the results only; the proofs
are in `Solution.lean`.
-/

@[expose] public section

namespace RamanujanLValues

theorem L_four (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 4 =
      25 * (Real.pi : ℂ) ^ 2 / 72 * ModularForm.L hk CuspForm.discriminant 2 := by
  sorry

theorem L_six (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 6 =
      (Real.pi : ℂ) ^ 4 / 18 * ModularForm.L hk CuspForm.discriminant 2 := by
  sorry

theorem L_five (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 5 =
      3 * (Real.pi : ℂ) ^ 2 / 14 * ModularForm.L hk CuspForm.discriminant 3 := by
  sorry

end RamanujanLValues
