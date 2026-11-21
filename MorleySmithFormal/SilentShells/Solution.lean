module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Solution: the silent shells of the cubic lattice

Squares are `0`, `1` or `4` modulo `8`, so three of them never sum to `7` modulo `8`. If
`x² + y² + z²` is divisible by `4` then `x`, `y`, `z` are even (squares are `0` or `1`
modulo `4`), and dividing by `4` lowers the exponent `a`.
-/

@[expose] public section

namespace SilentShells

private lemma mod_eight (x y z : ZMod 8) : x ^ 2 + y ^ 2 + z ^ 2 ≠ 7 := by
  revert x y z; decide

private lemma even_of_mod_four (x y z : ZMod 4) (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    2 * x = 0 ∧ 2 * y = 0 ∧ 2 * z = 0 := by
  revert x y z; decide

private lemma two_dvd_of_cast (x : ℤ) (h : 2 * (x : ZMod 4) = 0) : 2 ∣ x := by
  have h' : ((2 * x : ℤ) : ZMod 4) = 0 := by push_cast; exact h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * x) 4).mp h'
  omega

/-- No integer `4 ^ a * (8 * b + 7)` is a sum of three squares. -/
theorem sum_three_sq_ne (a b : ℕ) (x y z : ℤ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ a * (8 * b + 7) := by
  induction a generalizing x y z with
  | zero =>
    intro h
    have h8 := congrArg (Int.cast : ℤ → ZMod 8) h
    push_cast at h8
    have e8 : (8 : ZMod 8) = 0 := by decide
    rw [e8] at h8
    simp only [zero_mul, zero_add, one_mul] at h8
    exact mod_eight _ _ _ h8
  | succ a ih =>
    intro h
    have h4 : ((x : ZMod 4)) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod 4) h
      have e4 : (4 : ZMod 4) = 0 := by decide
      push_cast at this
      rw [this, pow_succ (4 : ZMod 4) a, e4]; ring
    obtain ⟨hx, hy, hz⟩ := even_of_mod_four _ _ _ h4
    obtain ⟨x', rfl⟩ := two_dvd_of_cast x hx
    obtain ⟨y', rfl⟩ := two_dvd_of_cast y hy
    obtain ⟨z', rfl⟩ := two_dvd_of_cast z hz
    refine ih x' y' z' ?_
    have : (4 : ℤ) * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * (4 ^ a * (8 * b + 7)) := by
      rw [pow_succ (4 : ℤ) a] at h; linarith
    exact mul_left_cancel₀ (by norm_num) this

/-- The shell of squared radius `4 ^ a * (8 * b + 7)` of the cubic lattice is empty. -/
theorem shell_eq_empty (a b : ℕ) :
    {v : Fin 3 → ℤ | ∑ i, v i ^ 2 = 4 ^ a * (8 * b + 7)} = ∅ := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, Fin.sum_univ_three]
  exact sum_three_sq_ne a b _ _ _

end SilentShells
