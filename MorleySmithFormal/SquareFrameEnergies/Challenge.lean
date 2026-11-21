module

public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Challenge: the energies of the square frame

For an integer matrix `(a b; c d)` of determinant one,
`a² + b² + c² + d² - 2 = (a - d)² + (b + c)²` and `(a - d)² + (b + c)² + 4 = (a + d)² + (b - c)²`.
An integer `n` is of the form `(a - d)² + (b + c)²` for such a matrix exactly when `n` and `n + 4`
are both sums of two squares.

In the notes (note 13), `a² + b² + c² + d² = tr(γ γᵀ)` is twice the Lorentz factor of the square
lattice frame `M(i) = 1` seen from the frame `M(γ i) = γ γᵀ`, and `(a - d)² + (b + c)²` is
twice the kinetic energy in units of the rest energy.
-/

@[expose] public section

namespace SquareFrameEnergies

/-- The two identities for an integer matrix of determinant one. -/
theorem identities (a b c d : ℤ) (h : a * d - b * c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 = (a - d) ^ 2 + (b + c) ^ 2 ∧
      (a - d) ^ 2 + (b + c) ^ 2 + 4 = (a + d) ^ 2 + (b - c) ^ 2 := by
  sorry

/-- `n = (a - d)² + (b + c)²` for some integer matrix `(a b; c d)` of determinant one if and only if
`n` and `n + 4` are both sums of two squares. -/
theorem exists_iff (n : ℤ) :
    (∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a - d) ^ 2 + (b + c) ^ 2 = n) ↔
      (∃ p q : ℤ, p ^ 2 + q ^ 2 = n) ∧ (∃ r s : ℤ, r ^ 2 + s ^ 2 = n + 4) := by
  sorry

end SquareFrameEnergies
