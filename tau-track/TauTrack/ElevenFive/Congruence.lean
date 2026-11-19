module

public import TauTrack.ElevenFive.Theta
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Prime
import Mathlib.Tactic

/-!
# The Eisenstein congruence modulo 5 for the newform of level 11

For `f = q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)² = ∑ a(n) qⁿ` (`newform11`, LMFDB 11.2.a.a, the modular form
of the elliptic curve 11a1),

**`a(n) ≡ σ*(n) (mod 5)`** for every `n ≥ 1`,   `σ*(n) = σ(n) − 11 σ(n/11) = ∑_{d ∣ n, 11 ∤ d} d`

(`newform11_modEq_sigmaStar`), and in particular **`a(p) ≡ 1 + p (mod 5)`** for every prime
`p ≠ 11` (`newform11_prime_modEq`). This is the level-11, weight-2 analogue of Ramanujan's
`τ(n) ≡ σ₁₁(n) (mod 691)`: `5` is the numerator of `(11 − 1)/12`.

## The proof

The same argument as for 691 (`Workshop/RamanujanCongruences`). The Eisenstein series
`E = E₂(z) − 11 E₂(11z) = −10 − 24 ∑ σ*(n) qⁿ` (TauCeti's `correctedE2 11`) has the prime 5 in
the denominator of its normalisation `Ẽ = E/(−10) = 1 + (12/5) ∑ σ*(n) qⁿ`. The theta series
`θ` of the lattice `(2 1; 1 6) ⊕ (2 1; 1 6)` (`theta11`) is a form on `Γ₀(11)` with integer
coefficients `r(n)` and constant term `1`. At prime level, subtracting the Eisenstein multiple
with the same constant term leaves a cusp form (TauCeti's
`sub_smul_correctedE2_mem_cuspFormSubmodule_iff`), and the cusp forms are the multiples of `f`
(`cuspForm_eq_coeff_one_smul`):

`θ = Ẽ + c f`,   so   `5 r(n) = 12 σ*(n) + (5 r(1) − 12) a(n)`,

and modulo 5: `12 σ*(n) ≡ 12 a(n)`. (The value of `r(1)` is not
needed; numerically `r(1) = 4` and `5θ = 5Ẽ + 8f`.)
-/

@[expose] public section

open UpperHalfPlane ModularForm TauCeti.EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace TauTrack.ElevenFive

instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `σ*(n) = σ(n) − 11 σ(n/11)` (the second term only when `11 ∣ n`): the sum of the divisors
of `n` prime to 11. -/
def sigmaStar (n : ℕ) : ℤ := σ 1 n - if 11 ∣ n then 11 * σ 1 (n / 11) else 0

/-- The coefficient functional `f ↦ a_n(f)` on `M₂(Γ₀(11))`. -/
noncomputable def coeffₗ (n : ℕ) : ModularForm Γ₁₁ 2 →ₗ[ℂ] ℂ :=
  (PowerSeries.coeff n).comp (qExpansionAt 1)

theorem coeffₗ_apply (n : ℕ) (f : ModularForm Γ₁₁ 2) :
    coeffₗ n f = (qExpansion 1 f).coeff n := by
  rw [coeffₗ, LinearMap.comp_apply, qExpansionAt_one, CongruenceSubgroup.strictWidthInfty_Gamma0]

theorem coeff_correctedE2 {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (correctedE2 11)).coeff n = -24 * (sigmaStar n : ℂ) := by
  rw [qExpansion_coeff_correctedE2, ite_eq_right hn, sigmaStar]
  split_ifs <;> push_cast <;> ring

theorem coeff_zero_correctedE2 : (qExpansion 1 (correctedE2 11)).coeff 0 = -10 := by
  rw [qExpansion_coeff_correctedE2, ite_eq_left rfl]
  norm_num

/-- **`θ = Ẽ + c f`** in `M₂(Γ₀(11))`. -/
theorem theta11_eq : ∃ c : ℂ,
    theta11 = (-(1 : ℂ) / 10) • correctedE2 11 + c • CuspForm.toModularFormₗ eta11Form := by
  have hmem : theta11 - (-(1 : ℂ) / 10) • correctedE2 11 ∈ cuspFormSubmodule Γ₁₁ 2 := by
    rw [sub_smul_correctedE2_mem_cuspFormSubmodule_iff, constantTermAt_eq_coeff_zero_qExpansionAt,
      qExpansionAt_one, CongruenceSubgroup.strictWidthInfty_Gamma0, qExpansion_theta11_coeff_zero]
    norm_num
  obtain ⟨g, hg⟩ := hmem
  refine ⟨(qExpansion 1 g).coeff 1, ?_⟩
  rw [← map_smul, ← cuspForm_eq_coeff_one_smul g, hg]
  abel

/-- The coefficient identity `r(n) = (12/5) σ*(n) + c a(n)` for `n ≥ 1`. -/
theorem coeff_theta11 (c : ℂ)
    (hc : theta11 = (-(1 : ℂ) / 10) • correctedE2 11 + c • CuspForm.toModularFormₗ eta11Form)
    {n : ℕ} (hn : n ≠ 0) :
    (ZLattice.representationNumber L11 (2 * n) : ℂ) =
      12 / 5 * (sigmaStar n : ℂ) + c * (newform11 n : ℂ) := by
  have h := congrArg (coeffₗ n) hc
  rw [map_add, map_smul, map_smul, coeffₗ_apply, coeffₗ_apply, coeffₗ_apply,
    qExpansion_theta11_coeff, coeff_correctedE2 hn] at h
  rw [h, smul_eq_mul, smul_eq_mul]
  have hf : (qExpansion 1 (CuspForm.toModularFormₗ eta11Form)).coeff n = (newform11 n : ℂ) :=
    newform11_spec n
  rw [hf]
  ring

/-- **The Eisenstein congruence for the newform of level 11**: `a(n) ≡ σ*(n) (mod 5)`. -/
theorem newform11_modEq_sigmaStar {n : ℕ} (hn : n ≠ 0) : newform11 n ≡ sigmaStar n [ZMOD 5] := by
  obtain ⟨c, hc⟩ := theta11_eq
  have h1 := coeff_theta11 c hc one_ne_zero
  have hn' := coeff_theta11 c hc hn
  have hs1 : sigmaStar 1 = 1 := by decide
  rw [hs1, newform11_one] at h1
  -- `c = r(1) − 12/5`
  set r1 := ZLattice.representationNumber L11 (2 * (1 : ℕ))
  set rn := ZLattice.representationNumber L11 (2 * n)
  have hc' : c = (r1 : ℂ) - 12 / 5 := by
    rw [h1]
    push_cast
    ring
  rw [hc'] at hn'
  have hZ : ((5 * rn : ℤ) : ℂ) = ((12 * sigmaStar n + (5 * r1 - 12) * newform11 n : ℤ) : ℂ) := by
    push_cast
    rw [hn']
    ring
  have hZ' := Int.cast_injective hZ
  have hd : (5 : ℤ) ∣ 12 * (sigmaStar n - newform11 n) :=
    ⟨rn - r1 * newform11 n, by linear_combination -hZ'⟩
  have hcop : IsCoprime (5 : ℤ) 12 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
  exact Int.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left hd)

/-! ## The divisor sum and the primes -/

/-- The divisors of `n` divisible by 11 sum to `11 σ(n/11)`, or to `0` if `11 ∤ n`. -/
theorem sum_divisors_filter_dvd_eleven (n : ℕ) :
    ∑ d ∈ n.divisors.filter (11 ∣ ·), d = if 11 ∣ n then 11 * σ 1 (n / 11) else 0 := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m (by norm_num), ArithmeticFunction.sigma_one_apply,
      Finset.mul_sum]
    have hset : (11 * m).divisors.filter (11 ∣ ·) = m.divisors.image (11 * ·) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨hd, hm0⟩, e, rfl⟩
        exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd, by omega⟩, rfl⟩
      · rintro ⟨e, ⟨he, hm0⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left 11 he, by omega⟩, dvd_mul_right 11 e⟩
    rw [hset, Finset.sum_image fun x _ y _ hxy ↦ by omega]
  · refine Finset.sum_eq_zero fun d hd ↦ ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) h

/-- **`σ*(n)` is the sum of the divisors of `n` prime to 11.** -/
theorem sigmaStar_eq_sum (n : ℕ) :
    sigmaStar n = ∑ d ∈ n.divisors.filter (fun d ↦ ¬ 11 ∣ d), (d : ℤ) := by
  have h := Finset.sum_filter_add_sum_filter_not n.divisors (11 ∣ ·) (fun d ↦ d)
  rw [← ArithmeticFunction.sigma_one_apply, sum_divisors_filter_dvd_eleven] at h
  have h' : ((σ 1 n : ℕ) : ℤ) = ((if 11 ∣ n then 11 * σ 1 (n / 11) else 0 : ℕ) : ℤ) +
      ∑ d ∈ n.divisors.filter (fun d ↦ ¬ 11 ∣ d), (d : ℤ) := by
    rw [← h]
    push_cast
    rfl
  rw [sigmaStar, h']
  split_ifs <;> push_cast <;> ring

theorem sigmaStar_prime {p : ℕ} (hp : p.Prime) (h11 : p ≠ 11) : sigmaStar p = 1 + p := by
  have hn : ¬ 11 ∣ p := fun h ↦ h11 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
  rw [sigmaStar, ite_eq_right hn, Nat.cast_zero, sub_zero]
  conv_lhs => rw [← pow_one p, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- **`a(p) ≡ 1 + p (mod 5)`** for every prime `p ≠ 11`. -/
theorem newform11_prime_modEq {p : ℕ} (hp : p.Prime) (h11 : p ≠ 11) :
    newform11 p ≡ 1 + p [ZMOD 5] := by
  rw [← sigmaStar_prime hp h11]
  exact newform11_modEq_sigmaStar hp.ne_zero

end TauTrack.ElevenFive
