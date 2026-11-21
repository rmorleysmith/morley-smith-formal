module

public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Ring
public import MorleySmithFormal.Hypercharge.Basic
import Mathlib.Tactic

/-!
# Solution: the hypercharges of a generation of the Standard Model

The statements of `Challenge.lean`, proved from `MorleySmithFormal.Hypercharge.Basic`.
-/

@[expose] public section

namespace Hypercharge

theorem gauge_anomaly_iff (q u d l e : ℚ) :
    (2 * q + u + d = 0 ∧ 3 * q + l = 0 ∧
        6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) ↔
      (q = 0 ∧ l = 0 ∧ e = 0 ∧ d = -u) ∨
        (u = 2 * q ∧ d = -4 * q ∧ l = -3 * q ∧ e = 6 * q) ∨
        (u = -4 * q ∧ d = 2 * q ∧ l = -3 * q ∧ e = 6 * q) :=
  MorleySmithFormal.Hypercharge.solutions_iff q u d l e

theorem gravitational_anomaly (q u d l e : ℚ) (h3 : 2 * q + u + d = 0) (h2 : 3 * q + l = 0)
    (hc : 6 * q ^ 3 + 3 * u ^ 3 + 3 * d ^ 3 + 2 * l ^ 3 + e ^ 3 = 0) :
    6 * q + 3 * u + 3 * d + 2 * l + e = 0 :=
  MorleySmithFormal.Hypercharge.gravitational h3 h2 hc

theorem fermat_form (q u e : ℚ) :
    6 * q ^ 3 + 3 * u ^ 3 + 3 * (-2 * q - u) ^ 3 + 2 * (-3 * q) ^ 3 + e ^ 3 = 0 ↔
      e ^ 3 + (u - 2 * q) ^ 3 = (u + 4 * q) ^ 3 := by
  rw [MorleySmithFormal.Hypercharge.cubic_eq]
  constructor <;> intro h <;> linarith

end Hypercharge
