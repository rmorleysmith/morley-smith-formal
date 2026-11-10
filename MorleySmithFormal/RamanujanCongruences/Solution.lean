module

public import Mathlib
public import MorleySmithFormal.RamanujanCongruences.Basic

/-!
# Solution: Ramanujan's congruences for the one-dimensional cusp spaces

Restates `Challenge.lean` verbatim and proves it from `MorleySmithFormal.RamanujanCongruences.Basic`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane PowerSeries
open scoped ArithmeticFunction.sigma

namespace RamanujanCongruences

/-- The `q`-expansion of `Δ · E₄^a · E₆^b`. -/
noncomputable def form (a b : ℕ) : PowerSeries ℂ :=
  qExpansion 1 ⇑CuspForm.discriminant * qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b

theorem congr_12 (n : ℕ) : ∃ c : ℤ, (form 0 0).coeff n = c ∧ c ≡ σ 11 n [ZMOD 691] :=
  MorleySmithFormal.RamanujanCongruences.congr_12 n

theorem congr_16 (n : ℕ) : ∃ c : ℤ, (form 1 0).coeff n = c ∧ c ≡ σ 15 n [ZMOD 3617] :=
  MorleySmithFormal.RamanujanCongruences.congr_16 n

theorem congr_18 (n : ℕ) : ∃ c : ℤ, (form 0 1).coeff n = c ∧ c ≡ σ 17 n [ZMOD 43867] :=
  MorleySmithFormal.RamanujanCongruences.congr_18 n

theorem congr_20 (n : ℕ) : ∃ c : ℤ, (form 2 0).coeff n = c ∧ c ≡ σ 19 n [ZMOD 174611] :=
  MorleySmithFormal.RamanujanCongruences.congr_20 n

theorem congr_22 (n : ℕ) : ∃ c : ℤ, (form 1 1).coeff n = c ∧ c ≡ σ 21 n [ZMOD 77683] :=
  MorleySmithFormal.RamanujanCongruences.congr_22 n

theorem congr_26 (n : ℕ) : ∃ c : ℤ, (form 2 1).coeff n = c ∧ c ≡ σ 25 n [ZMOD 657931] :=
  MorleySmithFormal.RamanujanCongruences.congr_26 n

end RamanujanCongruences
