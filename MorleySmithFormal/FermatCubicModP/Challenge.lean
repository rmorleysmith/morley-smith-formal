module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Challenge: the Fermat cubic modulo a prime `p ≡ 2 (mod 3)`

For a prime `p ≡ 2 (mod 3)`:

1. `cube_bijective`: cubing is a bijection of `ℤ/p`;
2. `card_solutions`: the congruence `x³ + y³ ≡ z³ (mod p)` has exactly `p²` solutions
   `(x, y, z)`, as many as the linear congruence `x + y ≡ z`.

Equivalently the projective cubic `X³ + Y³ = Z³` has `p + 1` points modulo `p`: the coefficient
`a(p) = p + 1 − #points` of its `L`-function is zero at these primes, which are the primes that
stay prime in the Eisenstein integers `ℤ[ω]` (the curve has complex multiplication by `ℤ[ω]`).

The cubic arises in physics: for one generation of the Standard Model with rational
hypercharges, the gauge anomaly conditions reduce to `e³ + (u − 2q)³ = (u + 4q)³` (Lohitsiri and
Tong, 2020; see `Hypercharge` in this repository).

The primes `p ≡ 1 (mod 3)`, where the count is `p² + (p − 1)A` with `4p = A² + 27B²`,
`A ≡ 1 (mod 3)` (Gauss), are not part of this file. The file imports only Mathlib and states the
results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

namespace FermatCubicModP

/-- For a prime `p ≡ 2 (mod 3)`, cubing is a bijection of `ℤ/p`. -/
theorem cube_bijective (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  sorry

/-- For a prime `p ≡ 2 (mod 3)`, the congruence `x³ + y³ ≡ z³ (mod p)` has `p²` solutions. -/
theorem card_solutions (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Nat.card {t : ZMod p × ZMod p × ZMod p // t.1 ^ 3 + t.2.1 ^ 3 = t.2.2 ^ 3} = p ^ 2 := by
  sorry

end FermatCubicModP
