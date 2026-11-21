module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Challenge: the silent shells of the cubic lattice

An integer of the form `4 ^ a * (8 * b + 7)` is not a sum of three squares of integers
(the direction of Legendre's three-square theorem that needs no theory of quadratic forms).
Equivalently, the sphere of squared radius `4 ^ a * (8 * b + 7)` about a point of `ℤ³` contains
no point of `ℤ³`.

In the model of a cubic lattice of impulses observed from one of its sites, the echo at time
`√N` comes from the lattice points at distance `√N`; for `N = 7, 15, 23, 28, …` there is none.

The converse (every other positive integer is a sum of three squares) is the theorem of
Legendre and Gauss; it is not part of this file.
-/

@[expose] public section

namespace SilentShells

/-- No integer `4 ^ a * (8 * b + 7)` is a sum of three squares. -/
theorem sum_three_sq_ne (a b : ℕ) (x y z : ℤ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ a * (8 * b + 7) := by
  sorry

/-- The shell of squared radius `4 ^ a * (8 * b + 7)` of the cubic lattice is empty. -/
theorem shell_eq_empty (a b : ℕ) :
    {v : Fin 3 → ℤ | ∑ i, v i ^ 2 = 4 ^ a * (8 * b + 7)} = ∅ := by
  sorry

end SilentShells
