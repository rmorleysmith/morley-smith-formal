module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Solution: the Fermat cubic modulo a prime `p ≡ 2 (mod 3)`

Write `p = 3m + 2`. Then `3(2m + 1) = 2(p − 1) + 1`, so by Fermat's little theorem
`(x³)^(2m+1) = x` for every `x` in `ℤ/p`: the map `y ↦ y^(2m+1)` inverts cubing. The solutions
of `x³ + y³ = z³` are then the triples `(x, y, (x³ + y³)^(2m+1))`, one for each pair `(x, y)`.
-/

@[expose] public section

namespace FermatCubicModP

private lemma cube_pow (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (x : ZMod p) :
    (x ^ 3) ^ (2 * (p / 3) + 1) = x := by
  have hexp : 3 * (2 * (p / 3) + 1) = (p - 1) * 2 + 1 := by omega
  rw [← pow_mul, hexp]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

private lemma pow_cube (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (x : ZMod p) :
    (x ^ (2 * (p / 3) + 1)) ^ 3 = x := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact cube_pow p hp x

/-- For a prime `p ≡ 2 (mod 3)`, cubing is a bijection of `ℤ/p`. -/
theorem cube_bijective (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) :=
  ⟨Function.LeftInverse.injective (g := fun y : ZMod p => y ^ (2 * (p / 3) + 1)) (cube_pow p hp),
    Function.RightInverse.surjective (g := fun y : ZMod p => y ^ (2 * (p / 3) + 1)) (pow_cube p hp)⟩

/-- For a prime `p ≡ 2 (mod 3)`, the congruence `x³ + y³ ≡ z³ (mod p)` has `p²` solutions. -/
theorem card_solutions (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Nat.card {t : ZMod p × ZMod p × ZMod p // t.1 ^ 3 + t.2.1 ^ 3 = t.2.2 ^ 3} = p ^ 2 := by
  let e : {t : ZMod p × ZMod p × ZMod p // t.1 ^ 3 + t.2.1 ^ 3 = t.2.2 ^ 3} ≃ ZMod p × ZMod p :=
    { toFun := fun t => (t.1.1, t.1.2.1)
      invFun := fun xy => ⟨(xy.1, xy.2, (xy.1 ^ 3 + xy.2 ^ 3) ^ (2 * (p / 3) + 1)),
        (pow_cube p hp _).symm⟩
      left_inv := by
        rintro ⟨⟨x, y, z⟩, h⟩
        simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        change x ^ 3 + y ^ 3 = z ^ 3 at h
        rw [h]
        exact cube_pow p hp z
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod, sq]

end FermatCubicModP
