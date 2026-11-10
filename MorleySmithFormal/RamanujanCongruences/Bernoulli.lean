module

public import Mathlib

/-!
# Bernoulli numbers `B₁₂, …, B₂₆`

The Eisenstein series `E_k` has `q`-expansion `1 − (2k / B_k) ∑ σ_{k−1}(n) qⁿ`, so the
congruences in `MorleySmithFormal.RamanujanCongruences.Basic` need the values of `B_k` for
`k = 12, 16, 18, 20, 22, 26`:

| `k` | `B_k` | `2k / B_k` |
|---|---|---|
| 12 | `−691/2730` | `−65520/691` |
| 16 | `−3617/510` | `−16320/3617` |
| 18 | `43867/798` | `28728/43867` |
| 20 | `−174611/330` | `−13200/174611` |
| 22 | `854513/138` | `552/77683` |
| 26 | `8553103/6` | `24/657931` |

Mathlib defines `bernoulli'` by the recursion `B'ₙ = 1 − ∑_{k<n} C(n,k) B'ₖ / (n − k + 1)`.
Evaluating it in the kernel (`decide +kernel`) recomputes the earlier values without
memoisation, so the cost grows exponentially in `n`; `B₁₂` and `B₁₆` together already take
minutes. Here the values are computed one step at a time instead, each from the earlier ones
by `norm_num`; the odd indices `n > 1` give `0` (`bernoulli'_eq_zero_of_odd`). For `n ≠ 1`,
`bernoulli n = bernoulli' n`.
-/

@[expose] public section

set_option autoImplicit false

namespace MorleySmithFormal.RamanujanCongruences

theorem bernoulli'_5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5]

theorem bernoulli'_7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7]

theorem bernoulli'_9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_10 : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9]

theorem bernoulli'_11 : bernoulli' 11 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_12 : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11]

theorem bernoulli'_13 : bernoulli' 13 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_14 : bernoulli' 14 = 7 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13]

theorem bernoulli'_15 : bernoulli' 15 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_16 : bernoulli' 16 = -3617 / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15]

theorem bernoulli'_17 : bernoulli' 17 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_18 : bernoulli' 18 = 43867 / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15, bernoulli'_16, bernoulli'_17]

theorem bernoulli'_19 : bernoulli' 19 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_20 : bernoulli' 20 = -174611 / 330 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15, bernoulli'_16, bernoulli'_17, bernoulli'_18, bernoulli'_19]

theorem bernoulli'_21 : bernoulli' 21 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_22 : bernoulli' 22 = 854513 / 138 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15, bernoulli'_16, bernoulli'_17, bernoulli'_18, bernoulli'_19,
    bernoulli'_20, bernoulli'_21]

theorem bernoulli'_23 : bernoulli' 23 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_24 : bernoulli' 24 = -236364091 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15, bernoulli'_16, bernoulli'_17, bernoulli'_18, bernoulli'_19,
    bernoulli'_20, bernoulli'_21, bernoulli'_22, bernoulli'_23]

theorem bernoulli'_25 : bernoulli' 25 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_26 : bernoulli' 26 = 8553103 / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.cast_choose ℚ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_5, bernoulli'_6, bernoulli'_7,
    bernoulli'_8, bernoulli'_9, bernoulli'_10, bernoulli'_11, bernoulli'_12, bernoulli'_13,
    bernoulli'_14, bernoulli'_15, bernoulli'_16, bernoulli'_17, bernoulli'_18, bernoulli'_19,
    bernoulli'_20, bernoulli'_21, bernoulli'_22, bernoulli'_23, bernoulli'_24, bernoulli'_25]

theorem bernoulli_eq' {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n :=
  bernoulli_eq_bernoulli'_of_ne_one hn

theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_four]

theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_6]

theorem bernoulli_12 : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_12]

theorem bernoulli_16 : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_16]

theorem bernoulli_18 : bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_18]

theorem bernoulli_20 : bernoulli 20 = -174611 / 330 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_20]

theorem bernoulli_22 : bernoulli 22 = 854513 / 138 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_22]

theorem bernoulli_26 : bernoulli 26 = 8553103 / 6 := by
  rw [bernoulli_eq' (by norm_num), bernoulli'_26]

end MorleySmithFormal.RamanujanCongruences
