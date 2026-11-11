module

public import TauTrack.LevelEleven.Hecke
public import TauTrack.LevelEleven.Integral

/-!
# The newform of weight 2 and level 11

`f(z) = η(z)² η(11z)²` (LMFDB label 11.2.a.a), with its integer coefficients `a(n)`.

* `eta11Form`: `f` as a cusp form of weight 2 for `Γ₀(11)` (`CuspForm.lean`). The invariance uses
  the multiplier of `η²` on `SL(2, ℤ)` (`EtaSq.lean`, `Invariance.lean`).
* `cuspForm_eq_coeff_one_smul`: `f` spans `S₂(Γ₀(11))` (`Dimension.lean`).
* `eq_eta11Form_of_coeff`: a form of weight 2 and level 11 agreeing with `f` up to `q²` is `f`.
* `hecke11_eta11Form`: `f` is an eigenform of every Hecke operator (`Hecke.lean`).
* `newform11`: the integer coefficients, with `newform11_mul`, `newform11_mul_coprime`,
  `newform11_prime_pow` and `newform11_eleven_pow`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm
open scoped MatrixGroups

namespace TauTrack

/-- The integer coefficients `a(n)` of `q ∏ (1 - qⁿ)² (1 - q¹¹ⁿ)²`. -/
noncomputable def newform11 (n : ℕ) : ℤ := eta11Series.coeff n

theorem newform11_spec (n : ℕ) : (qExpansion 1 eta11Form).coeff n = (newform11 n : ℂ) :=
  eta11Form_coeff n

theorem newform11_zero : newform11 0 = 0 := by
  have h := CuspFormClass.qExpansion_coeff_zero eta11Form zero_lt_one one_mem_strictPeriods_Γ₁₁
  rw [newform11_spec] at h
  exact_mod_cast h

theorem newform11_one : newform11 1 = 1 := by
  have h := eta11Form_coeff_one
  rw [newform11_spec] at h
  exact_mod_cast h

/-- `a(m) a(n) = ∑_{d ∣ (m, n), 11 ∤ d} d · a(mn/d²)`. -/
theorem newform11_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    newform11 m * newform11 n = ∑ d ∈ (Nat.gcd m n).divisors,
      (if 11 ∣ d then 0 else (d : ℤ)) * newform11 (m * n / d ^ 2) := by
  have h := coeff11_mul m hn
  simp only [coeff11, newform11_spec] at h
  have : ((newform11 m * newform11 n : ℤ) : ℂ) = ((∑ d ∈ (Nat.gcd m n).divisors,
      (if 11 ∣ d then 0 else (d : ℤ)) * newform11 (m * n / d ^ 2) : ℤ) : ℂ) := by
    push_cast
    rw [h]
  exact_mod_cast this

theorem newform11_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    newform11 (m * n) = newform11 m * newform11 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [newform11_zero]
  · rw [newform11_mul m hn, h.gcd_eq_one]
    simp

theorem newform11_prime_pow {p : ℕ} (hp : p.Prime) (hp11 : p ≠ 11) (r : ℕ) :
    newform11 (p ^ (r + 2)) = newform11 p * newform11 (p ^ (r + 1)) - p * newform11 (p ^ r) := by
  have h := newform11_mul (p ^ (r + 1)) hp.ne_zero
  have hg : Nat.gcd (p ^ (r + 1)) p = p := Nat.gcd_eq_right (dvd_pow_self p (by omega))
  have h11 : ¬ 11 ∣ p := fun hd ↦ hp11 ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp hd).symm
  have hdiv : p ^ (r + 1) * p / p ^ 2 = p ^ r :=
    Nat.div_eq_of_eq_mul_left (pow_pos hp.pos 2) (by ring)
  rw [hg, hp.divisors, Finset.sum_pair hp.one_lt.ne] at h
  simp only [Nat.dvd_one, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, one_pow, Nat.div_one,
    one_mul, h11, hdiv] at h
  rw [show p ^ (r + 2) = p ^ (r + 1) * p by ring]
  linear_combination -h

theorem newform11_eleven_pow (r : ℕ) :
    newform11 (11 ^ (r + 1)) = newform11 11 * newform11 (11 ^ r) := by
  have h := newform11_mul (11 ^ r) (n := 11) (by norm_num)
  rcases r with _ | r
  · simp [newform11_one]
  · have hg : Nat.gcd (11 ^ (r + 1)) 11 = 11 := Nat.gcd_eq_right (dvd_pow_self 11 (by omega))
    rw [hg, (by decide : Nat.Prime 11).divisors, Finset.sum_pair (by norm_num)] at h
    simp only [Nat.dvd_one, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, one_pow, Nat.div_one,
      one_mul, dvd_refl, zero_mul, add_zero] at h
    rw [show 11 ^ (r + 1 + 1) = 11 ^ (r + 1) * 11 by ring]
    linear_combination -h

theorem pentagonalSeries_coeff_zero : (PowerSeries.pentagonalSeries ℤ).coeff 0 = 1 := by
  have h : pentagonal 0 = 0 := by simp [pentagonal_def]
  have := PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0
  rw [h] at this
  simpa using this

theorem pentagonalSeries_coeff_one : (PowerSeries.pentagonalSeries ℤ).coeff 1 = -1 := by
  have h : pentagonal 1 = 1 := by simp [pentagonal_def]
  have := PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 1
  rw [h] at this
  simpa using this

/-- `a(2) = -2`. -/
theorem newform11_two : newform11 2 = -2 := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [newform11, eta11Series, h2, PowerSeries.coeff_succ_X_mul]
  simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, PowerSeries.coeff_expand,
    pentagonalSeries_coeff_zero, pentagonalSeries_coeff_one]

end TauTrack
