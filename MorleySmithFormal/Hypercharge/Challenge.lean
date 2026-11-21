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

4. `gauge_anomaly_iff_colours`, `gravitational_anomaly_colours`: the same two statements with `N ≥ 1`
   colours in place of three, `Q : (N, 2)_q`, `uᶜ, dᶜ : (N̄, 1)`. The conditions are
   `2q + u + d = 0`, `Nq + l = 0`, `2Nq³ + Nu³ + Nd³ + 2l³ + e³ = 0`, and the solutions with
   `q ≠ 0` are `{u, d} = {(N − 1)q, −(N + 1)q}`, `l = −Nq`, `e = 2Nq`. The cubic condition is
   `e³ + (u + (1 − N)q)³ = (u + (N + 1)q)³`, Fermat's cubic for every `N`.

The hypercharges are rational: this is the hypothesis that hypercharge is quantised. The
statements concern one generation without a right-handed neutrino.

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

theorem gauge_anomaly_iff_colours (N : ℕ) (hN : N ≠ 0) (q u d l e : ℚ) :
    (2 * q + u + d = 0 ∧ (N : ℚ) * q + l = 0 ∧
        2 * (N : ℚ) * q ^ 3 + (N : ℚ) * u ^ 3 + (N : ℚ) * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) ↔
      (q = 0 ∧ l = 0 ∧ e = 0 ∧ d = -u) ∨
        (u = ((N : ℚ) - 1) * q ∧ d = -((N : ℚ) + 1) * q ∧ l = -(N : ℚ) * q ∧ e = 2 * (N : ℚ) * q) ∨
        (u = -((N : ℚ) + 1) * q ∧ d = ((N : ℚ) - 1) * q ∧ l = -(N : ℚ) * q ∧
          e = 2 * (N : ℚ) * q) := by
  sorry

theorem gravitational_anomaly_colours (N : ℕ) (hN : N ≠ 0) (q u d l e : ℚ)
    (h3 : 2 * q + u + d = 0) (h2 : (N : ℚ) * q + l = 0)
    (hc : 2 * (N : ℚ) * q ^ 3 + (N : ℚ) * u ^ 3 + (N : ℚ) * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) :
    2 * (N : ℚ) * q + (N : ℚ) * u + (N : ℚ) * d + 2 * l + e = 0 := by
  sorry

end Hypercharge
