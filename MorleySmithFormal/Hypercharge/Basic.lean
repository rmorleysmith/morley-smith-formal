module

public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-!
# The hypercharges of a generation, from Fermat's theorem for cubes

One generation of the Standard Model consists of five left-handed Weyl fermions, with
representations under `SU(3) × SU(2)` and hypercharges

`Q : (3, 2)_q`, `uᶜ : (3̄, 1)_u`, `dᶜ : (3̄, 1)_d`, `L : (1, 2)_l`, `eᶜ : (1, 1)_e`.

The gauge anomalies cancel exactly when

* `2q + u + d = 0`   (`SU(3)² U(1)`),
* `3q + l = 0`   (`SU(2)² U(1)`),
* `6q³ + 3u³ + 3d³ + 2l³ + e³ = 0`   (`U(1)³`),

and the mixed gravitational anomaly cancels when `6q + 3u + 3d + 2l + e = 0`.

Following Lohitsiri and Tong, substitute `l = −3q` and `d = −2q − u` in the cubic condition: it
becomes `e³ + (u − 2q)³ = (u + 4q)³` (`cubic_eq`), Fermat's equation of degree 3. By Fermat's
theorem for cubes (Euler; Mathlib's `fermatLastTheoremThree`), one of the three cubes is zero:

* `e = 0`: then `u − 2q = u + 4q`, so `q = 0`, `l = 0` and `d = −u`;
* `u = 2q`: then `e = 6q`, `d = −4q`, `l = −3q`;
* `u = −4q`: then `e = 6q`, `d = 2q`, `l = −3q`.

The last two are the hypercharges of the Standard Model, `(q, u, d, l, e) = (1, −4, 2, −3, 6)·q`,
up to exchanging `uᶜ` and `dᶜ`. In all three cases the gravitational condition holds
(`gravitational`).

## Reference

* N. Lohitsiri and D. Tong, *Hypercharge quantisation and Fermat's last theorem*,
  SciPost Phys. 8 (2020), 009.
-/

@[expose] public section

namespace MorleySmithFormal.Hypercharge

/-- With the two linear gauge conditions, the cubic condition is Fermat's cubic. -/
theorem cubic_eq (q u e : ℚ) :
    6 * q ^ 3 + 3 * u ^ 3 + 3 * (-2 * q - u) ^ 3 + 2 * (-3 * q) ^ 3 + e ^ 3 =
      e ^ 3 + (u - 2 * q) ^ 3 - (u + 4 * q) ^ 3 := by
  ring

theorem cube_injective {x y : ℚ} (h : x ^ 3 = y ^ 3) : x = y :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective h

/-- Fermat's theorem for cubes over `ℚ`: in `x³ + y³ = z³` one of `x`, `y`, `z` is zero. -/
theorem fermat_cubic {x y z : ℚ} (h : x ^ 3 + y ^ 3 = z ^ 3) : x = 0 ∨ y = 0 ∨ z = 0 := by
  by_contra hne
  push Not at hne
  exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree) x y z hne.1 hne.2.1 hne.2.2 h

/-- **The solutions of the gauge anomaly conditions of one generation.** -/
theorem solutions {q u d l e : ℚ} (h3 : 2 * q + u + d = 0) (h2 : 3 * q + l = 0)
    (hc : 6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) :
    (q = 0 ∧ l = 0 ∧ e = 0 ∧ d = -u) ∨
      (u = 2 * q ∧ d = -4 * q ∧ l = -3 * q ∧ e = 6 * q) ∨
      (u = -4 * q ∧ d = 2 * q ∧ l = -3 * q ∧ e = 6 * q) := by
  have hd : d = -2 * q - u := by linarith
  have hl : l = -3 * q := by linarith
  subst hd hl
  rw [cubic_eq] at hc
  have hF : e ^ 3 + (u - 2 * q) ^ 3 = (u + 4 * q) ^ 3 := by linarith
  rcases fermat_cubic hF with he | hu | hu
  · -- `e = 0`
    left
    rw [he] at hF
    have h := cube_injective (by simpa using hF : (u - 2 * q) ^ 3 = (u + 4 * q) ^ 3)
    have hq : q = 0 := by linarith
    subst hq
    exact ⟨rfl, by ring, he, by ring⟩
  · -- `u = 2q`
    right; left
    have hu' : u = 2 * q := by linarith
    subst hu'
    have h := cube_injective (by simpa using hF : e ^ 3 = (2 * q + 4 * q) ^ 3)
    exact ⟨rfl, by ring, rfl, by rw [h]; ring⟩
  · -- `u = −4q`
    right; right
    have hu' : u = -4 * q := by linarith
    subst hu'
    have h : e ^ 3 = (6 * q) ^ 3 := by
      have : (-4 * q + 4 * q : ℚ) = 0 := by ring
      rw [this] at hF
      linear_combination hF
    exact ⟨rfl, by ring, rfl, cube_injective h⟩

/-- Conversely, each of the three families satisfies the gauge conditions. -/
theorem solutions_iff (q u d l e : ℚ) :
    (2 * q + u + d = 0 ∧ 3 * q + l = 0 ∧
        6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) ↔
      (q = 0 ∧ l = 0 ∧ e = 0 ∧ d = -u) ∨
        (u = 2 * q ∧ d = -4 * q ∧ l = -3 * q ∧ e = 6 * q) ∨
        (u = -4 * q ∧ d = 2 * q ∧ l = -3 * q ∧ e = 6 * q) := by
  constructor
  · rintro ⟨h3, h2, hc⟩
    exact solutions h3 h2 hc
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
      refine ⟨by ring, by ring, by ring⟩

/-- **The gauge conditions imply the gravitational condition.** -/
theorem gravitational {q u d l e : ℚ} (h3 : 2 * q + u + d = 0) (h2 : 3 * q + l = 0)
    (hc : 6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) :
    6 * q + 3 * u + 3 * d + 2 * l + e = 0 := by
  rcases solutions h3 h2 hc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    ring

end MorleySmithFormal.Hypercharge
