module

public import Mathlib

/-!
# Challenge: Ramanujan's congruences for the one-dimensional cusp spaces

For `k = 12, 16, 18, 20, 22, 26` the space of level-one cusp forms of weight `k` is spanned by
a single normalised form, `Δ · E₄^a · E₆^b` with `4a + 6b = k − 12`. Its `q`-expansion
coefficients are integers congruent to `σ_{k−1}(n)` modulo the numerator of `B_k / 2k`:

| `k` | form | modulus |
|---|---|---|
| 12 | `Δ` | 691 |
| 16 | `Δ E₄` | 3617 |
| 18 | `Δ E₆` | 43867 |
| 20 | `Δ E₄²` | 174611 = 283 · 617 |
| 22 | `Δ E₄ E₆` | 77683 = 131 · 593 |
| 26 | `Δ E₄² E₆` | 657931 |

The forms are written as products of Mathlib's `q`-expansions, so the statement uses only
Mathlib definitions. This file states the results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane PowerSeries
open scoped ArithmeticFunction.sigma

namespace RamanujanCongruences

/-- The `q`-expansion of `Δ · E₄^a · E₆^b`. -/
noncomputable def form (a b : ℕ) : PowerSeries ℂ :=
  qExpansion 1 ⇑CuspForm.discriminant * qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b

theorem congr_12 (n : ℕ) : ∃ c : ℤ, (form 0 0).coeff n = c ∧ c ≡ σ 11 n [ZMOD 691] := by
  sorry

theorem congr_16 (n : ℕ) : ∃ c : ℤ, (form 1 0).coeff n = c ∧ c ≡ σ 15 n [ZMOD 3617] := by
  sorry

theorem congr_18 (n : ℕ) : ∃ c : ℤ, (form 0 1).coeff n = c ∧ c ≡ σ 17 n [ZMOD 43867] := by
  sorry

theorem congr_20 (n : ℕ) : ∃ c : ℤ, (form 2 0).coeff n = c ∧ c ≡ σ 19 n [ZMOD 174611] := by
  sorry

theorem congr_22 (n : ℕ) : ∃ c : ℤ, (form 1 1).coeff n = c ∧ c ≡ σ 21 n [ZMOD 77683] := by
  sorry

theorem congr_26 (n : ℕ) : ∃ c : ℤ, (form 2 1).coeff n = c ∧ c ≡ σ 25 n [ZMOD 657931] := by
  sorry

end RamanujanCongruences
