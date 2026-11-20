module

public import TauTrack.ElevenFunctionalEquation.Fricke
import Mathlib.Tactic

/-!
# The central value and the critical line at level 11

Let `f(z) = η(z)² η(11z)²` (`eta11Form`) and let `Λ(s) = (2π)^{−s} Γ(s) L(f, s)` be Mathlib's
completed `L`-function, the Mellin transform of `t ↦ f(it)`.

**`f` is positive on the imaginary axis** (`resToImagAxis_eta11Form_pos`). For `y > 0`,
`η(iy) = e^{−2πy/24} ∏ (1 − e^{−2πny})` is real (`eta_I_mul_re`) and nonzero, so
`f(iy) = η(iy)² η(11iy)² > 0`.

**The central value is positive** (`L_one_eq_two_pi_integral`, `L_one_pos`):
`L(f, 1) = 2π ∫₀^∞ f(iy) dy > 0`. With the root number `+1` of `Fricke.lean`, the order of
vanishing at the centre is `0`.

**Reflection** (`Λ_eta11Form_conj`). The Mellin transform of a real function commutes with
complex conjugation: `Λ(s̄) = conj Λ(s)`.

**The critical line** (`im_cpow_mul_Λ_eta11Form`). For real `t`, the functional equation
`Λ(2 − s) = 11^{s−1} Λ(s)` at `s = 1 + it`, where `2 − s = s̄`, gives
`conj Λ(s) = 11^{s−1} Λ(s)`, so

`11^{s/2} Λ(s)` is real for `s = 1 + it`.

This real function of `t` is the analogue for `L(f, s)` of Hardy's function `Z(t)` for `ζ`: the
zeros of `L(f, s)` on the line `Re s = 1` are its real zeros.
-/

@[expose] public section

open Complex MeasureTheory Set
open UpperHalfPlane hiding I
open TauCeti
open scoped MatrixGroups ModularForm Real ComplexConjugate

namespace TauTrack

/-! ## `f` on the imaginary axis -/

open ModularForm in
/-- `η(iy)` is real for `y > 0`: every factor of `q^{1/24} ∏ (1 − qⁿ)` is real when
`q = e^{−2πy}`. -/
theorem eta_I_mul_re {y : ℝ} (hy : 0 < y) : ((η (I * y)).re : ℂ) = η (I * y) := by
  rw [← conj_eq_iff_re]
  set r : ℝ := Real.exp (-2 * π * y) with hr
  have hq : cexp (2 * π * I * (I * y)) = (r : ℂ) := by
    rw [hr, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hr1 : ‖(r : ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h : Real.exp (-2 * π * y) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    simpa using h
  have h24 : Function.Periodic.qParam 24 (I * y) = ((Real.exp (-2 * π * y / 24) : ℝ) : ℂ) := by
    rw [Function.Periodic.qParam, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp only [ModularForm.eta, eta_q_eq_pow, hq, map_mul]
  rw [(multipliable_one_sub_pow hr1).map_tprod (starRingEnd ℂ) continuous_conj, h24,
    conj_ofReal]
  congr 1
  refine tprod_congr fun n ↦ ?_
  rw [map_sub, map_one, map_pow, conj_ofReal]

open ModularForm in
theorem eta11Form_apply (z : ℍ) : eta11Form z = η z ^ 2 * η (11 * z) ^ 2 := by
  show eta11 z = _
  simp [eta11, etaSq, coe_scaleGL_smul]

/-- **`f(iy) > 0`** for `y > 0`: `f(iy) = η(iy)² η(11iy)²` is the product of squares of nonzero
reals. -/
theorem resToImagAxis_eta11Form_pos {t : ℝ} (ht : 0 < t) :
    ((resToImagAxis eta11Form t).re : ℂ) = resToImagAxis eta11Form t ∧
      0 < (resToImagAxis eta11Form t).re := by
  have h11 : (0 : ℝ) < 11 * t := by positivity
  have e1 := eta_I_mul_re ht
  have e2 := eta_I_mul_re h11
  have n1 : ModularForm.eta (I * t) ≠ 0 := ModularForm.eta_ne_zero (by simpa using ht)
  have n2 : ModularForm.eta (I * ((11 * t : ℝ) : ℂ)) ≠ 0 :=
    ModularForm.eta_ne_zero (by simpa using h11)
  have hval : resToImagAxis eta11Form t =
      (((ModularForm.eta (I * t)).re ^ 2 * (ModularForm.eta (I * ((11 * t : ℝ) : ℂ))).re ^ 2 :
        ℝ) : ℂ) := by
    rw [resToImagAxis_of_pos _ ht, eta11Form_apply, ofReal_mul, ofReal_pow, ofReal_pow, e1, e2]
    show ModularForm.eta (I * t) ^ 2 * ModularForm.eta (11 * (I * t)) ^ 2 = _
    rw [show (11 : ℂ) * (I * t) = I * ((11 * t : ℝ) : ℂ) by push_cast; ring]
  have r1 : (ModularForm.eta (I * t)).re ≠ 0 := fun h ↦ n1 (by rw [← e1, h, ofReal_zero])
  have r2 : (ModularForm.eta (I * ((11 * t : ℝ) : ℂ))).re ≠ 0 :=
    fun h ↦ n2 (by rw [← e2, h, ofReal_zero])
  rw [hval, ofReal_re]
  exact ⟨rfl, by positivity⟩

/-- On the positive imaginary axis, the function whose Mellin transform is `Λ` is the
restriction of `f`, a positive real. -/
theorem eta11Form_ofComplex_I_mul {t : ℝ} (ht : 0 < t) :
    eta11Form (ofComplex (I * t)) = (((resToImagAxis eta11Form t).re : ℝ) : ℂ) := by
  rw [(resToImagAxis_eta11Form_pos ht).1, resToImagAxis_of_pos _ ht,
    ofComplex_apply_of_im_pos (by simpa using ht)]

/-! ## The central value -/

/-- **The central value is a positive real**:
`L(f, 1) = 2π ∫₀^∞ f(iy) dy`, and the integrand is positive. -/
theorem L_one_eq_two_pi_integral :
    ModularForm.L (by norm_num : (0 : ℤ) < 2) eta11Form 1 =
      ((2 * π * ∫ t in Ioi (0 : ℝ), (resToImagAxis eta11Form t).re : ℝ) : ℂ) := by
  rw [ModularForm.L_apply_of_ne_zero _ _ one_ne_zero, CuspForm.Λ_eq_mellin, Gammaℂ_one, mellin,
    sub_self]
  have hcongr : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (0 : ℂ) • eta11Form (ofComplex (I * t)) =
      ∫ t in Ioi (0 : ℝ), (((resToImagAxis eta11Form t).re : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    rw [cpow_zero, one_smul, eta11Form_ofComplex_I_mul ht]
  rw [hcongr, integral_complex_ofReal]
  push_cast
  field_simp

/-- `t ↦ f(it)` is integrable on `(0, ∞)`: the Mellin transform of `Λ` converges at `s = 1`. -/
theorem integrableOn_resToImagAxis_eta11Form : IntegrableOn (resToImagAxis eta11Form) (Ioi 0) := by
  have h := ((CuspForm.isStrongFEPair (by norm_num : (0 : ℤ) < 2) eta11Form).hasMellin 1).1
  rw [MellinConvergent] at h
  refine h.congr_fun (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
  simp only [ModularForm.weakFEPair_f, sub_self, cpow_zero, one_smul]
  rw [resToImagAxis_of_pos _ ht, ofComplex_apply_of_im_pos (by simpa using ht)]

theorem L_one_pos : 0 < 2 * π * ∫ t in Ioi (0 : ℝ), (resToImagAxis eta11Form t).re := by
  have hint : IntegrableOn (resToImagAxis eta11Form) (Ioi 0) :=
    integrableOn_resToImagAxis_eta11Form
  have hpos : 0 < ∫ t in Ioi (0 : ℝ), (resToImagAxis eta11Form t).re := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦
        (resToImagAxis_eta11Form_pos ht).2.le) hint.re]
    refine lt_of_lt_of_le (by simp) (measure_mono (s := Ioi (0 : ℝ)) fun t (ht : 0 < t) ↦
      ⟨(resToImagAxis_eta11Form_pos ht).2.ne', ht⟩)
  positivity

/-! ## Reflection and the critical line -/

/-- **Reflection**: `Λ(s̄) = conj Λ(s)`, because `f` is real on the imaginary axis. -/
theorem Λ_eta11Form_conj (s : ℂ) :
    ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form (conj s) =
      conj (ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form s) := by
  rw [CuspForm.Λ_eq_mellin, mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  have harg : (t : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [eta11Form_ofComplex_I_mul ht, smul_eq_mul, smul_eq_mul, map_mul, conj_ofReal]
  congr 1
  have h := Complex.cpow_conj (t : ℂ) (s - 1) harg
  rw [conj_ofReal, map_sub, map_one] at h
  exact h

/-- **The critical line**: for real `t` and `s = 1 + it`, the number `11^{s/2} Λ(s)` is real. -/
theorem im_cpow_mul_Λ_eta11Form (t : ℝ) :
    ((11 : ℂ) ^ ((1 + t * I) / 2) *
      ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form (1 + t * I)).im = 0 := by
  set s : ℂ := 1 + t * I with hs
  have hconj : conj s = 2 - s := by
    rw [hs, map_add, map_one, map_mul, conj_ofReal, conj_I]
    ring
  have hΛ : conj (ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form s) =
      (11 : ℂ) ^ (s - 1) * ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form s := by
    rw [← Λ_eta11Form_conj, hconj, Λ_eta11Form_two_sub]
  have harg : ((11 : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  have h11 : (11 : ℂ) ≠ 0 := by norm_num
  have hpow : conj ((11 : ℂ) ^ (s / 2)) = (11 : ℂ) ^ ((2 - s) / 2) := by
    have e11 : ((11 : ℝ) : ℂ) = 11 := by norm_num
    have h := Complex.cpow_conj ((11 : ℝ) : ℂ) (s / 2) harg
    have h2 : conj (s / 2) = (2 - s) / 2 := by
      rw [map_div₀, hconj, map_ofNat]
    rw [conj_ofReal, h2, e11] at h
    rw [h]
  rw [← conj_eq_iff_im, map_mul, hpow, hΛ, ← mul_assoc, ← Complex.cpow_add _ _ h11]
  congr 2
  ring

end TauTrack
