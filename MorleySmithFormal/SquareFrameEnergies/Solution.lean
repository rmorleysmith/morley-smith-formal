module

public import Mathlib.Algebra.Ring.Int.Defs
import MorleySmithFormal.SquareFrameEnergies.Basic

/-!
# Solution: the energies of the square frame

Restates `Challenge.lean` and proves it from `MorleySmithFormal.SquareFrameEnergies.Basic`.
-/

@[expose] public section

namespace SquareFrameEnergies

theorem identities (a b c d : ℤ) (h : a * d - b * c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 = (a - d) ^ 2 + (b + c) ^ 2 ∧
      (a - d) ^ 2 + (b + c) ^ 2 + 4 = (a + d) ^ 2 + (b - c) ^ 2 :=
  MorleySmithFormal.SquareFrameEnergies.identities a b c d h

theorem exists_iff (n : ℤ) :
    (∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a - d) ^ 2 + (b + c) ^ 2 = n) ↔
      (∃ p q : ℤ, p ^ 2 + q ^ 2 = n) ∧ (∃ r s : ℤ, r ^ 2 + s ^ 2 = n + 4) :=
  MorleySmithFormal.SquareFrameEnergies.exists_iff n

end SquareFrameEnergies
