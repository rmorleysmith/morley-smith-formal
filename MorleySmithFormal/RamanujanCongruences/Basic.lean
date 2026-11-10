module

public import Mathlib
public import MorleySmithFormal.RamanujanCongruences.Bernoulli

/-!
# Ramanujan's congruences for the one-dimensional cusp spaces

For `k = 12, 16, 18, 20, 22, 26` the space `S_k` of level-one cusp forms of weight `k` is
one-dimensional, spanned by `Δ · E₄^a · E₆^b` with `4a + 6b = k − 12`. Its `q`-expansion
coefficients `dₙ` are integers, and `dₙ ≡ σ_{k−1}(n) (mod ℓ)`, where `ℓ` is the numerator of
`B_k / 2k`: `691`, `3617`, `43867`, `174611 = 283 · 617`, `77683 = 131 · 593`, `657931`.
For `k = 12` this is Ramanujan's `τ(n) ≡ σ₁₁(n) (mod 691)` (1916).

## The picture

The normalised Eisenstein series is `E_k = 1 − (2k / B_k) ∑ σ_{k−1}(n) qⁿ`, and
`2k / B_k = D / ℓ` with `D` prime to `ℓ`. So `ℓ` sits in the *denominators* of the Eisenstein
coefficients. Take `P = E₄^{a+3} E₆^b`: a weight-`k` form with integer coefficients `pₙ` and
constant term `1`, like `E_k`. The difference `P − E_k` vanishes at the cusp, so it is a
multiple of the cusp form `Δ E₄^a E₆^b`:

  `P − E_k = c · Δ E₄^a E₆^b`,  `c = 240(a + 3) − 504b + D/ℓ`

(`c` is read off from the `q¹`-coefficients). Multiply by `ℓ`: every term becomes integral, and
modulo `ℓ` the identity says `D ∑ σ_{k−1}(n) qⁿ ≡ D · Δ E₄^a E₆^b`. Since `D` is a unit
mod `ℓ`, `∑ σ_{k−1}(n) qⁿ ≡ Δ E₄^a E₆^b (mod ℓ)` coefficient by coefficient: the Eisenstein
series, rescaled to clear `ℓ`, is congruent to the cusp form.

## Main results

* `qExpansion_discriminant_eq` : the `q`-expansion of `Δ` is the image of the integer series
  `DeltaZ = X · (∏ (1 − X^{n+1}))²⁴`, expanded by the pentagonal number theorem (as in
  `Fugue/Tau691.lean`). With `qExpansion_E₄_eq` and `qExpansion_E₆_eq` (coefficients
  `240 σ₃(n)`, `−504 σ₅(n)`), `form a b` is the image of `formZ a b ∈ ℤ⟦X⟧` (`form_eq_map`).
* `exists_qExpansion_G` : if `M_{k−12}` has rank one, `E₄^{a+3} E₆^b − E_k = c · Δ E₄^a E₆^b`
  for some `c ∈ ℂ`. The left side has constant term `1 − 1 = 0`, so it is a cusp form; dividing
  by `Δ` (`CuspForm.discriminantEquiv`) gives a form in `M_{k−12}`, which is spanned by the
  nonzero form `E₄^a E₆^b`.
* `congr_of` : the generic statement. If also `2k / B_k = D / ℓ` with `ℓ`, `D` coprime
  integers, then comparing `qⁿ`-coefficients gives
  `ℓ pₙ + D σ_{k−1}(n) = (ℓ (240(a + 3) − 504b) + D) dₙ` in `ℤ`, so `ℓ ∣ D (σ_{k−1}(n) − dₙ)`
  and hence `ℓ ∣ σ_{k−1}(n) − dₙ`. `ℓ` need not be prime.
* `congr_12`, `congr_16`, `congr_18`, `congr_20`, `congr_22`, `congr_26` : the six cases.
  `M_w` has rank one for `w = k − 12 = 0, 4, 6, 8, 10, 14` (`rank_eq_one`, from Mathlib's
  `dimension_level_one`); the Bernoulli numbers are computed in
  `MorleySmithFormal.RamanujanCongruences.Bernoulli`.

This generalises `Fugue/Tau691.lean` in
[fugue-formal](https://github.com/rmorleysmith/fugue-formal) (the case `k = 12`), ported to
Lean v4.35.0 and the module system.

All results depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`.

## References

* S. Ramanujan, *On certain arithmetical functions*, Trans. Cambridge Philos. Soc. 22 (1916).
* H. P. F. Swinnerton-Dyer, *On ℓ-adic representations and congruences for coefficients of
  modular forms*, Modular Functions of One Variable III, Lecture Notes in Math. 350 (1973).
-/

@[expose] public section

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex ModularForm EisensteinSeries PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace MorleySmithFormal.RamanujanCongruences

/-! ## Evaluating absolutely convergent power series -/

/-- `∑ aₙ qⁿ` converges absolutely. -/
def AbsConv (f : PowerSeries ℂ) (q : ℂ) : Prop := Summable fun n => ‖coeff n f * q ^ n‖

/-- The value `∑ aₙ qⁿ`. -/
noncomputable def ev (f : PowerSeries ℂ) (q : ℂ) : ℂ := ∑' n, coeff n f * q ^ n

theorem coeff_mul_pow (f g : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    coeff n (f * g) * q ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2) := by
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

theorem AbsConv.mul {f g : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (hg : AbsConv g q) :
    AbsConv (f * g) q := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  unfold AbsConv
  refine h.congr fun n => ?_
  rw [coeff_mul_pow]

theorem ev_mul {f g : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (hg : AbsConv g q) :
    ev (f * g) q = ev f q * ev g q := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  simp_rw [coeff_mul_pow]

theorem AbsConv.pow {f : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (n : ℕ) :
    AbsConv (f ^ n) q ∧ ev (f ^ n) q = ev f q ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold AbsConv
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      simp at hn; simp [coeff_one, hn]
    · unfold ev
      rw [tsum_eq_single 0 (fun n hn => by simp [coeff_one, hn])]
      simp
  | succ n ih =>
    refine ⟨ih.1.mul hf, ?_⟩
    rw [pow_succ, ev_mul ih.1 hf, ih.2, pow_succ]

theorem absConv_X (q : ℂ) : AbsConv X q := by
  unfold AbsConv
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp at hn; simp [coeff_X, hn]

theorem ev_X (q : ℂ) : ev X q = q := by
  unfold ev
  rw [tsum_eq_single 1 (fun n hn => by simp [coeff_X, hn])]
  simp

theorem AbsConv.hasSum {f : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) :
    HasSum (fun n => coeff n f * q ^ n) (ev f q) :=
  hf.of_norm.hasSum

/-! ## The pentagonal series at `‖q‖ < 1` -/

theorem absConv_pentagonal {q : ℂ} (hq : ‖q‖ < 1) : AbsConv (pentagonalSeries ℂ) q := by
  refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow, norm_mul, norm_pow, norm_pow]
    simp
  · simp [coeff_pentagonalSeries_eq_zero ℂ hn]

theorem ev_pentagonal {q : ℂ} (hq : ‖q‖ < 1) :
    ev (pentagonalSeries ℂ) q = ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  rw [← eulerFunction_eq_tprod hq, eulerFunction_def]
  rfl

theorem map_pentagonalSeries :
    PowerSeries.map (Int.castRingHom ℂ) (pentagonalSeries ℤ) = pentagonalSeries ℂ := by
  ext n
  rw [coeff_map]
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp only [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    simp
  · simp [coeff_pentagonalSeries_eq_zero _ hn]

/-! ## Integrality -/

local notation "𝕢" => Function.Periodic.qParam

theorem hasSum_discriminant (z : ℍ) :
    HasSum (fun m => coeff m (X * pentagonalSeries ℂ ^ 24) • 𝕢 1 (z : ℂ) ^ m)
      (ModularForm.discriminant z) := by
  have hq : ‖𝕢 1 (z : ℂ)‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hP := absConv_pentagonal hq
  have hP24 := hP.pow 24
  have hc := (absConv_X _).mul hP24.1
  convert hc.hasSum using 1
  rw [ev_mul (absConv_X _) hP24.1, ev_X, hP24.2, ev_pentagonal hq, discriminant_eq_q_prod,
    ← (multipliable_one_sub_pow hq).tprod_pow]

/-- `X · (∏ (1 - X^{n+1}))²⁴ ∈ ℤ⟦X⟧`, with the product expanded by the pentagonal series. -/
noncomputable def DeltaZ : PowerSeries ℤ := X * pentagonalSeries ℤ ^ 24

/-- The `q`-expansion of `Δ` is the image of the integer series `DeltaZ`. -/
theorem qExpansion_discriminant_eq :
    qExpansion 1 ⇑CuspForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) DeltaZ := by
  ext m
  rw [DeltaZ, map_mul, map_pow, map_X, map_pentagonalSeries]
  exact (ModularFormClass.qExpansion_coeff_unique (f := CuspForm.discriminant) one_pos
    one_mem_strictPeriods_SL hasSum_discriminant m).symm

/-- `1 + 240 ∑ σ₃(n) qⁿ ∈ ℤ⟦X⟧`. -/
noncomputable def E4Z : PowerSeries ℤ := PowerSeries.mk fun m => if m = 0 then 1 else 240 * σ 3 m

/-- `1 - 504 ∑ σ₅(n) qⁿ ∈ ℤ⟦X⟧`. -/
noncomputable def E6Z : PowerSeries ℤ := PowerSeries.mk fun m => if m = 0 then 1 else -504 * σ 5 m

theorem qExpansion_E₄_eq : qExpansion 1 ⇑E₄ = PowerSeries.map (Int.castRingHom ℂ) E4Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, coeff_map, E4Z, coeff_mk]
  split_ifs <;> simp [bernoulli_four']
  norm_num

theorem qExpansion_E₆_eq : qExpansion 1 ⇑E₆ = PowerSeries.map (Int.castRingHom ℂ) E6Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, coeff_map, E6Z, coeff_mk]
  split_ifs <;> simp [bernoulli_six']
  norm_num

/-- The `q`-expansion of `Δ · E₄^a · E₆^b`, exactly as in `Challenge.lean`. -/
noncomputable def form (a b : ℕ) : PowerSeries ℂ :=
  qExpansion 1 ⇑CuspForm.discriminant * qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b

/-- The integer series of `Δ · E₄^a · E₆^b`. -/
noncomputable def formZ (a b : ℕ) : PowerSeries ℤ := DeltaZ * E4Z ^ a * E6Z ^ b

theorem form_eq_map (a b : ℕ) : form a b = PowerSeries.map (Int.castRingHom ℂ) (formZ a b) := by
  rw [form, formZ, map_mul, map_mul, map_pow, map_pow, qExpansion_discriminant_eq,
    qExpansion_E₄_eq, qExpansion_E₆_eq]

/-! ## The coefficients of `q⁰` and `q¹` -/

section Coeff

variable {R : Type*} [CommRing R]

theorem coeff1_mul (p r : PowerSeries R) :
    coeff 1 (p * r) = coeff 0 p * coeff 1 r + coeff 1 p * coeff 0 r := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff0_pow {p : PowerSeries R} (h0 : coeff 0 p = 1) (n : ℕ) : coeff 0 (p ^ n) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, h0,
    one_pow]

theorem coeff1_pow {p : PowerSeries R} (h0 : coeff 0 p = 1) (n : ℕ) :
    coeff 1 (p ^ n) = n * coeff 1 p := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, coeff1_mul, ih, coeff0_pow h0, h0]
    push_cast
    ring

end Coeff

theorem coeff_E4Z_zero : coeff 0 E4Z = 1 := by simp [E4Z]

theorem coeff_E4Z_one : coeff 1 E4Z = 240 := by simp [E4Z]

theorem coeff_E6Z_zero : coeff 0 E6Z = 1 := by simp [E6Z]

theorem coeff_E6Z_one : coeff 1 E6Z = -504 := by simp [E6Z]

theorem coeff_DeltaZ_zero : coeff 0 DeltaZ = 0 := by simp [DeltaZ]

theorem coeff_DeltaZ_one : coeff 1 DeltaZ = 1 := by
  have h := discriminant_qExpansion_coeff_one
  rw [← CuspForm.coe_discriminant, qExpansion_discriminant_eq, coeff_map, eq_intCast] at h
  exact_mod_cast h

theorem coeff_PZ_zero (a b : ℕ) : coeff 0 (E4Z ^ (a + 3) * E6Z ^ b) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
    ← coeff_zero_eq_constantCoeff_apply, coeff0_pow coeff_E4Z_zero, coeff0_pow coeff_E6Z_zero,
    one_mul]

theorem coeff_PZ_one (a b : ℕ) :
    coeff 1 (E4Z ^ (a + 3) * E6Z ^ b) = 240 * (a + 3) - 504 * b := by
  rw [coeff1_mul, coeff0_pow coeff_E4Z_zero, coeff0_pow coeff_E6Z_zero,
    coeff1_pow coeff_E4Z_zero, coeff1_pow coeff_E6Z_zero, coeff_E4Z_one, coeff_E6Z_one]
  push_cast
  ring

theorem coeff_formZ_zero (a b : ℕ) : coeff 0 (formZ a b) = 0 := by
  simp [formZ, DeltaZ]

theorem coeff_formZ_one (a b : ℕ) : coeff 1 (formZ a b) = 1 := by
  rw [formZ, coeff1_mul, coeff1_mul, coeff_DeltaZ_zero, coeff_DeltaZ_one,
    coeff0_pow coeff_E4Z_zero, coeff0_pow coeff_E6Z_zero, coeff_zero_eq_constantCoeff_apply,
    map_mul, ← coeff_zero_eq_constantCoeff_apply, coeff_DeltaZ_zero]
  ring

/-! ## The exact identity `E₄^(a+3) E₆^b - E_k = c · Δ E₄^a E₆^b` -/

/-- `E₄^(a+3) E₆^b`, a modular form of weight `k = 12 + 4a + 6b` with constant term `1`. -/
noncomputable def P (a b : ℕ) : ModularForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ) :=
  ModularForm.mcast (by push_cast; ring) ((E₄.pow (a + 3)).mul (E₆.pow b))

/-- The normalised Eisenstein series `E_k`, `k = 12 + 4a + 6b`. -/
noncomputable def Ek (a b : ℕ) : ModularForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ) :=
  E (by omega : 3 ≤ 12 + 4 * a + 6 * b)

/-- `E₄^a E₆^b`, as a modular form of weight `k - 12`. -/
noncomputable def Q (a b : ℕ) : ModularForm 𝒮ℒ (((12 + 4 * a + 6 * b : ℕ) : ℤ) - 12) :=
  ModularForm.mcast (by push_cast; ring) ((E₄.pow a).mul (E₆.pow b))

/-- `E₄^(a+3) E₆^b - E_k`, a cusp form of weight `k`. -/
noncomputable def G (a b : ℕ) : ModularForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ) := P a b - Ek a b

theorem qExpansion_P (a b : ℕ) :
    qExpansion 1 (P a b) = PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ (a + 3) * E6Z ^ b) := by
  rw [P, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]

theorem qExpansion_Q (a b : ℕ) :
    qExpansion 1 (Q a b) = qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b := by
  rw [Q, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem coeff_Ek (a b m : ℕ) : (qExpansion 1 (Ek a b)).coeff m = if m = 0 then 1 else
    -(2 * ((12 + 4 * a + 6 * b : ℕ) : ℂ) / bernoulli (12 + 4 * a + 6 * b)) *
      (σ (12 + 4 * a + 6 * b - 1) m) :=
  E_qExpansion_coeff _ ⟨6 + 2 * a + 3 * b, by ring⟩ m

theorem qExpansion_G (a b : ℕ) :
    qExpansion 1 (G a b) = qExpansion 1 (P a b) - qExpansion 1 (Ek a b) := by
  rw [G, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]

theorem coeff_G_zero (a b : ℕ) : (qExpansion 1 (G a b)).coeff 0 = 0 := by
  rw [qExpansion_G, map_sub, qExpansion_P, coeff_map, coeff_PZ_zero, coeff_Ek]
  simp

theorem Q_ne_zero (a b : ℕ) : Q a b ≠ 0 := by
  rw [ne_eq, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL, qExpansion_Q,
    qExpansion_E₄_eq, qExpansion_E₆_eq, ← map_pow, ← map_pow, ← map_mul]
  intro h
  have h0 := congrArg (coeff 0) h
  rw [coeff_map, map_zero, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow,
    ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_E4Z_zero,
    coeff_E6Z_zero] at h0
  simp at h0

/-- **The identity in `M_k`.** If `M_{k-12}` has rank one, then
`E₄^(a+3) E₆^b - E_k = c · Δ E₄^a E₆^b` for some `c ∈ ℂ`: the left side is a cusp form, and its
quotient by `Δ` lies in `M_{k-12}`, which is spanned by `E₄^a E₆^b`. -/
theorem exists_qExpansion_G (a b : ℕ)
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ ((4 * a + 6 * b : ℕ) : ℤ)) = 1) :
    ∃ c : ℂ, qExpansion 1 (G a b) = c • form a b := by
  have h0 := coeff_G_zero a b
  have hr : Module.finrank ℂ (ModularForm 𝒮ℒ (((12 + 4 * a + 6 * b : ℕ) : ℤ) - 12)) = 1 := by
    rw [show (((12 + 4 * a + 6 * b : ℕ) : ℤ) - 12) = ((4 * a + 6 * b : ℕ) : ℤ) by
      push_cast; ring]
    exact Module.rank_eq_one_iff_finrank_eq_one.mp hrank
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (Q a b) (Q_ne_zero a b)).mp hr
    (CuspForm.discriminantEquiv (toCuspForm (G a b) h0))
  refine ⟨c, ?_⟩
  rw [qExpansion_eq_qExpansion_discriminant_mul (G a b) h0, ← hc, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, qExpansion_Q, form,
    mul_smul_comm, mul_assoc]
  rfl

/-! ## Clearing denominators -/

/-- **The congruence, generically.** Let `k = 12 + 4a + 6b`. If `M_{k-12}` has rank one and
`2k / B_k = D / ℓ` with `ℓ`, `D` coprime integers, then the `qⁿ`-coefficient of
`Δ E₄^a E₆^b` is an integer congruent to `σ_{k-1}(n)` modulo `ℓ`. -/
theorem congr_of (a b : ℕ) (ℓ D : ℤ)
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ ((4 * a + 6 * b : ℕ) : ℤ)) = 1)
    (hB : 2 * ((12 + 4 * a + 6 * b : ℕ) : ℚ) / bernoulli (12 + 4 * a + 6 * b) = D / ℓ)
    (hℓ : ℓ ≠ 0) (hcop : IsCoprime ℓ D) (n : ℕ) :
    ∃ c : ℤ, (form a b).coeff n = c ∧ c ≡ σ (12 + 4 * a + 6 * b - 1) n [ZMOD ℓ] := by
  refine ⟨coeff n (formZ a b), by rw [form_eq_map, coeff_map]; rfl, ?_⟩
  rw [Int.modEq_iff_dvd]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_formZ_zero]
  obtain ⟨c, hc⟩ := exists_qExpansion_G a b hrank
  have hB' : 2 * ((12 + 4 * a + 6 * b : ℕ) : ℂ) / (bernoulli (12 + 4 * a + 6 * b) : ℂ) =
      (D : ℂ) / ℓ := by
    exact_mod_cast hB
  -- compare the coefficients of `q¹` (which determines `c`) and of `qⁿ`
  have h1 := congrArg (coeff 1) hc
  have h2 := congrArg (coeff n) hc
  rw [qExpansion_G, map_sub, qExpansion_P, coeff_map, coeff_Ek, coeff_smul, form_eq_map,
    coeff_map, hB'] at h1 h2
  rw [coeff_PZ_one, coeff_formZ_one] at h1
  simp only [one_ne_zero, ite_false, ArithmeticFunction.sigma_one, smul_eq_mul,
    eq_intCast, Int.cast_one, Nat.cast_one, mul_one] at h1
  simp only [hn, ite_false, smul_eq_mul, eq_intCast] at h2
  set pn := coeff n (E4Z ^ (a + 3) * E6Z ^ b)
  set dn := coeff n (formZ a b)
  set sn := σ (12 + 4 * a + 6 * b - 1) n
  have hℓ' : (ℓ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hℓ
  -- `ℓ pₙ + D σ(n) = (ℓ c₁ + D) dₙ`, an identity in `ℤ`
  have key : ((ℓ * pn + D * sn : ℤ) : ℂ) =
      (((ℓ * (240 * (a + 3) - 504 * b) + D) * dn : ℤ) : ℂ) := by
    push_cast at h1 h2 ⊢
    rw [← h1] at h2
    field_simp at h2
    linear_combination h2
  have key' := Int.cast_injective key
  refine hcop.dvd_of_dvd_mul_left ⟨dn * (240 * (a + 3) - 504 * b) - pn, ?_⟩
  linear_combination key'

/-! ## The six cases -/

/-- `M_w` has rank one for `w = 0, 4, 6, 8, 10, 14`. -/
theorem rank_eq_one (w : ℕ) (hw : w = 0 ∨ w = 4 ∨ w = 6 ∨ w = 8 ∨ w = 10 ∨ w = 14) :
    Module.rank ℂ (ModularForm 𝒮ℒ (w : ℤ)) = 1 := by
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [dimension_level_one _ (by decide)] <;> norm_num [Nat.ModEq]

/-- **Ramanujan's congruence** `τ(n) ≡ σ₁₁(n) (mod 691)`; `2·12 / B₁₂ = −65520/691`. -/
theorem congr_12 (n : ℕ) : ∃ c : ℤ, (form 0 0).coeff n = c ∧ c ≡ σ 11 n [ZMOD 691] :=
  congr_of 0 0 691 (-65520) (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_12])
    (by norm_num) (by norm_num) n

/-- `Δ E₄`: `2·16 / B₁₆ = −16320/3617`. -/
theorem congr_16 (n : ℕ) : ∃ c : ℤ, (form 1 0).coeff n = c ∧ c ≡ σ 15 n [ZMOD 3617] :=
  congr_of 1 0 3617 (-16320) (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_16])
    (by norm_num) (by norm_num) n

/-- `Δ E₆`: `2·18 / B₁₈ = 28728/43867`. -/
theorem congr_18 (n : ℕ) : ∃ c : ℤ, (form 0 1).coeff n = c ∧ c ≡ σ 17 n [ZMOD 43867] :=
  congr_of 0 1 43867 28728 (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_18])
    (by norm_num) (by norm_num) n

/-- `Δ E₄²`: `2·20 / B₂₀ = −13200/174611`, `174611 = 283 · 617`. -/
theorem congr_20 (n : ℕ) : ∃ c : ℤ, (form 2 0).coeff n = c ∧ c ≡ σ 19 n [ZMOD 174611] :=
  congr_of 2 0 174611 (-13200) (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_20])
    (by norm_num) (by norm_num) n

/-- `Δ E₄ E₆`: `2·22 / B₂₂ = 552/77683`, `77683 = 131 · 593`. -/
theorem congr_22 (n : ℕ) : ∃ c : ℤ, (form 1 1).coeff n = c ∧ c ≡ σ 21 n [ZMOD 77683] :=
  congr_of 1 1 77683 552 (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_22])
    (by norm_num) (by norm_num) n

/-- `Δ E₄² E₆`: `2·26 / B₂₆ = 24/657931`. -/
theorem congr_26 (n : ℕ) : ∃ c : ℤ, (form 2 1).coeff n = c ∧ c ≡ σ 25 n [ZMOD 657931] :=
  congr_of 2 1 657931 24 (rank_eq_one _ (by norm_num)) (by norm_num [bernoulli_26])
    (by norm_num) (by norm_num) n

end MorleySmithFormal.RamanujanCongruences
