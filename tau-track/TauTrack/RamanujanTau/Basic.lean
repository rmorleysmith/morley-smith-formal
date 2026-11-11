module

public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
public import TauCeti.NumberTheory.ModularForms.LevelOne.Hecke

/-!
# Ramanujan's tau function as an integer-valued multiplicative function

`τ(n)` is the `n`-th `q`-expansion coefficient of the modular discriminant `Δ`. Mathlib and
TauCeti state its properties for the complex coefficients. This file bundles `τ` as an
`ArithmeticFunction ℤ` and transfers the properties to the integers:

* `ramanujanTau`: the function, with `ramanujanTau_spec` tying it to the coefficients of `Δ`.
* `ramanujanTau_isMultiplicative`: `τ(mn) = τ(m) τ(n)` for coprime `m`, `n`.
* `ramanujanTau_prime_pow`: `τ(p^(r+2)) = τ(p) τ(p^(r+1)) − p¹¹ τ(p^r)`.
* `ramanujanTau_mul`: `τ(m) τ(n) = ∑_{d ∣ (m, n)} d¹¹ τ(mn/d²)`.
* `ramanujanTau_congr`: `τ(n) ≡ σ₁₁(n) (mod 691)`.

Integrality, multiplicativity and the recursion are TauCeti's
(`exists_discriminant_qExpansion_coeff_eq_intCast`, `discriminant_qExpansion_coeff_mul`,
`discriminant_qExpansion_coeff_prime_pow_add_two`). The product formula uses TauCeti's coefficient
formula for the Hecke operators `Tₙ` at level one and the fact that `S₁₂` is spanned by `Δ`. The
congruence uses the identity `E₄³ = E₁₂ + (720 − 65520/691) Δ`, proved with the Sturm bound.
-/

@[expose] public section

open UpperHalfPlane ModularForm ArithmeticFunction EisensteinSeries
open scoped MatrixGroups CongruenceSubgroup
open scoped ArithmeticFunction.sigma

namespace TauTrack

/-- The integer equal to the `n`-th coefficient of `Δ`. -/
noncomputable def tauAux (n : ℕ) : ℤ :=
  (TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n).choose

theorem tauAux_spec (n : ℕ) : (qExpansion 1 discriminant).coeff n = (tauAux n : ℂ) :=
  (TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n).choose_spec

/-- **Ramanujan's tau function**, as an arithmetic function with integer values. -/
noncomputable def ramanujanTau : ArithmeticFunction ℤ where
  toFun := tauAux
  map_zero' := by
    have h := tauAux_spec 0
    rw [TauCeti.ModularForm.discriminant_qExpansion_coeff_zero] at h
    exact_mod_cast h.symm

theorem ramanujanTau_spec (n : ℕ) :
    (qExpansion 1 discriminant).coeff n = (ramanujanTau n : ℂ) := tauAux_spec n

theorem ramanujanTau_one : ramanujanTau 1 = 1 := by
  have h := ramanujanTau_spec 1
  rw [discriminant_qExpansion_coeff_one] at h
  exact_mod_cast h.symm

theorem ramanujanTau_isMultiplicative : ramanujanTau.IsMultiplicative := by
  refine ⟨ramanujanTau_one, fun {m n} hmn => ?_⟩
  have h := TauCeti.ModularForm.discriminant_qExpansion_coeff_mul hmn
  simp only [ramanujanTau_spec] at h
  exact_mod_cast h

theorem ramanujanTau_prime_pow {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ramanujanTau (p ^ (r + 2)) =
      ramanujanTau p * ramanujanTau (p ^ (r + 1)) - (p : ℤ) ^ 11 * ramanujanTau (p ^ r) := by
  have h := TauCeti.ModularForm.discriminant_qExpansion_coeff_prime_pow_add_two hp r
  simp only [ramanujanTau_spec] at h
  exact_mod_cast h

/-- `Δ` as a modular form of weight `12`. -/
noncomputable abbrev Δ₁₂ : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant

theorem coe_Δ₁₂ : ⇑Δ₁₂ = discriminant :=
  (funext (CuspForm.toModularFormₗ_apply _)).trans CuspForm.coe_discriminant

/-- `Δ` is an eigenvector of every Hecke operator `Tₙ`, with eigenvalue its `n`-th coefficient.
The difference has vanishing coefficients of `1` and `q`, so it is zero by the Sturm bound. -/
theorem heckeTLevelOne_Δ₁₂ (n : ℕ) [NeZero n] :
    TauCeti.heckeTLevelOne 12 n Δ₁₂ = (ramanujanTau n : ℂ) • Δ₁₂ := by
  have hq : qExpansion 1 (TauCeti.heckeTLevelOne 12 n Δ₁₂ - (ramanujanTau n : ℂ) • Δ₁₂ :
      ModularForm 𝒮ℒ 12) =
      qExpansion 1 (TauCeti.heckeTLevelOne 12 n Δ₁₂) -
        (ramanujanTau n : ℂ) • qExpansion 1 discriminant := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, coe_Δ₁₂]
  apply sub_eq_zero.mp
  apply ModularForm.sturm_bound_levelOne (k := 12)
  refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 2 ?_)
  intro i hi
  rw [hq]
  interval_cases i
  · rw [map_sub, PowerSeries.coeff_smul, TauCeti.qExpansion_coeff_zero_heckeTLevelOne, coe_Δ₁₂,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_zero]
    simp
  · rw [map_sub, PowerSeries.coeff_smul, TauCeti.qExpansion_coeff_one_heckeTLevelOne, coe_Δ₁₂,
      discriminant_qExpansion_coeff_one, ramanujanTau_spec]
    simp

/-- **The product formula**: `τ(m) τ(n) = ∑_{d ∣ (m, n)} d¹¹ τ(mn/d²)`. -/
theorem ramanujanTau_mul (m n : ℕ) :
    ramanujanTau m * ramanujanTau n =
      ∑ d ∈ (m.gcd n).divisors, (d : ℤ) ^ 11 * ramanujanTau (m * n / d ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : NeZero n := ⟨hn.ne'⟩
  have h := TauCeti.qExpansion_coeff_heckeTLevelOne (k := 12) (n := n) Δ₁₂ m
  rw [heckeTLevelOne_Δ₁₂, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
    coe_Δ₁₂] at h
  simp only [ramanujanTau_spec, smul_eq_mul] at h
  have h' : (∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ 11 * (ramanujanTau (m * n / d ^ 2) : ℂ)) =
      (ramanujanTau n : ℂ) * ramanujanTau m := by
    rw [h]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show ((12 : ℤ) - 1) = ((11 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [mul_comm]
  exact_mod_cast h'.symm

/-- `E₄³ = E₁₂ + (720 − 65520/691) Δ`, by the Sturm bound. -/
theorem E₄_cube_eq :
    (ModularForm.mcast (by norm_num) (E₄.pow 3) +
      (-(720 - 65520 / 691 : ℂ)) • Δ₁₂ : ModularForm 𝒮ℒ 12) = E (by norm_num : 3 ≤ 12) := by
  apply sub_eq_zero.mp
  apply ModularForm.sturm_bound_levelOne (k := 12)
  refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 2 ?_)
  intro i hi
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    TauCeti.ModularForm.qExpansion_E₄_cube_add_smul_discriminant]
  interval_cases i
  · rw [map_sub, map_add, PowerSeries.coeff_smul,
      TauCeti.ModularForm.E₄_cube_qExpansion_coeff_zero,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_zero,
      TauCeti.ModularForm.E_twelve_qExpansion_coeff]
    simp
  · rw [map_sub, map_add, PowerSeries.coeff_smul,
      TauCeti.ModularForm.E₄_cube_qExpansion_coeff_one, discriminant_qExpansion_coeff_one,
      TauCeti.ModularForm.E_twelve_qExpansion_coeff]
    simp

/-- **Ramanujan's congruence**: `τ(n) ≡ σ₁₁(n) (mod 691)`. -/
theorem ramanujanTau_congr (n : ℕ) : ramanujanTau n ≡ σ 11 n [ZMOD 691] := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- the coefficients of `E₄³` are integers
  obtain ⟨e, he⟩ : ∃ e : ℤ, (qExpansion 1 E₄ ^ 3).coeff n = e := by
    rw [TauCeti.ModularForm.qExpansion_E₄_eq, ← map_pow, PowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  have h := congrArg (fun f : ModularForm 𝒮ℒ 12 ↦ (qExpansion 1 f).coeff n) E₄_cube_eq
  beta_reduce at h
  rw [TauCeti.ModularForm.qExpansion_E₄_cube_add_smul_discriminant, map_add,
    PowerSeries.coeff_smul, TauCeti.ModularForm.E_twelve_qExpansion_coeff, ite_eq_right hn.ne',
    ramanujanTau_spec, he, smul_eq_mul] at h
  have hZ : (65520 : ℤ) * ((σ 11 n : ℤ) - ramanujanTau n) = 691 * (e - 720 * ramanujanTau n) := by
    have : ((65520 : ℂ) * ((σ 11 n : ℂ) - ramanujanTau n)) =
        691 * ((e : ℂ) - 720 * ramanujanTau n) := by
      linear_combination (-691 : ℂ) * h
    exact_mod_cast this
  refine (Int.modEq_iff_dvd).2 ?_
  have hc : IsCoprime (691 : ℤ) 65520 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; decide
  exact hc.dvd_of_dvd_mul_left (Dvd.intro _ hZ.symm)

end TauTrack
