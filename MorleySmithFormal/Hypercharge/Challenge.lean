module

public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Ring

/-!
# Challenge: the hypercharges of a generation of the Standard Model

One generation of the Standard Model consists of five left-handed Weyl fermions, with
representations under `SU(3) × SU(2)` and rational hypercharges

`Q : (3, 2)_q`, `uᶜ : (3̄, 1)_u`, `dᶜ : (3̄, 1)_d`, `L : (1, 2)_l`, `eᶜ : (1, 1)_e`.

The gauge anomalies cancel exactly when `2q + u + d = 0` (`SU(3)² U(1)`), `3q + l = 0`
(`SU(2)² U(1)`) and `6q³ + 3u³ + 3d³ + 2l³ + e³ = 0` (`U(1)³`). The statements say:

1. `gauge_anomaly_iff`: these three conditions hold exactly when
   * `q = 0`, `l = 0`, `e = 0` and `d = −u`, or
   * `(u, d, l, e) = (2q, −4q, −3q, 6q)`, or
   * `(u, d, l, e) = (−4q, 2q, −3q, 6q)`.

   The last two are the hypercharges of the Standard Model, `6Y = (1, −4, 2, −3, 6)` for
   `(Q, uᶜ, dᶜ, L, eᶜ)`, up to scale and the exchange of `uᶜ` and `dᶜ`.
2. `gravitational_anomaly`: the three conditions imply the mixed gravitational condition
   `6q + 3u + 3d + 2l + e = 0`.
3. `fermat_form`: with `l = −3q` and `d = −2q − u`, the cubic condition is
   `e³ + (u − 2q)³ = (u + 4q)³`, Fermat's equation of degree 3.

Statements 1 and 2 are the theorem of Lohitsiri and Tong (2020); the proof is Fermat's theorem for
cubes. Only Mathlib definitions are used. This file states the results only; the proofs are in
`Solution.lean`.
-/

@[expose] public section

namespace Hypercharge

theorem gauge_anomaly_iff (q u d l e : ℚ) :
    (2 * q + u + d = 0 ∧ 3 * q + l = 0 ∧
        6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) ↔
      (q = 0 ∧ l = 0 ∧ e = 0 ∧ d = -u) ∨
        (u = 2 * q ∧ d = -4 * q ∧ l = -3 * q ∧ e = 6 * q) ∨
        (u = -4 * q ∧ d = 2 * q ∧ l = -3 * q ∧ e = 6 * q) := by
  sorry

theorem gravitational_anomaly (q u d l e : ℚ) (h3 : 2 * q + u + d = 0) (h2 : 3 * q + l = 0)
    (hc : 6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) :
    6 * q + 3 * u + 3 * d + 2 * l + e = 0 := by
  sorry

theorem fermat_form (q u e : ℚ) :
    6 * q ^ 3 + 3 * u ^ 3 + 3 * (-2 * q - u) ^ 3 + 2 * (-3 * q) ^ 3 + e ^ 3 = 0 ↔
      e ^ 3 + (u - 2 * q) ^ 3 = (u + 4 * q) ^ 3 := by
  sorry

end Hypercharge
