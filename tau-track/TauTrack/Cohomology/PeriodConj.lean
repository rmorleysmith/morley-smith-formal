module

public import TauCeti.NumberTheory.ModularForms.Conjugate
public import TauCeti.NumberTheory.ModularForms.LFunction.Period
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.CuspForm
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral
import Mathlib.Tactic

/-!
# Complex conjugation and the periods of a level-one cusp form

For a cusp form `f` of level one, `f^c(τ) = conj f(−conj τ)` is again a cusp form (TauCeti's
`CuspForm.conj`; its `q`-coefficients are the conjugates of those of `f`). On the imaginary axis
`f^c(it) = conj f(it)`, so conjugation acts on everything that is an integral along that axis:

* `conj_Λ_natCast_add_one`: `conj Λ(f, n + 1) = Λ(f^c, n + 1)`.
* `conj_cuspIntegral_mul_pow`: the periods `ρ_n(f) = ∫₀^{i∞} f(τ) τⁿ dτ` satisfy
  `conj ρ_n(f) = (−1)^{n+1} ρ_n(f^c)`.
* `conj_eval_periodPolynomial`: **for `w` even and `x` real,
  `conj r_f(x, 1) = −r_{f^c}(−x, 1)`**, where `r_f(X, Y) = ∫₀^{i∞} f(τ)(X − τY)^w dτ` is the
  period polynomial.

Consequently conjugation of coefficients sends the even part `r_f⁺` to `−r_{f^c}⁺` and the odd
part `r_f⁻` to `r_{f^c}⁻`. This is the input for the Hodge decomposition of the parabolic
cohomology `H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex MeasureTheory Set OnePoint MvPolynomial
open scoped ModularForm MatrixGroups Pointwise
open TauCeti TauCeti.UpperHalfPlane TauCeti.ModularSymbols

namespace TauTrack.Cohomology

/-- The level-one group is stable under conjugation by `J = diag(−1, 1)`. -/
theorem levelOne_le_conjAct_inv_J :
    (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ≤ ConjAct.toConjAct UpperHalfPlane.J⁻¹ • 𝒮ℒ := by
  rintro _ ⟨γ, rfl⟩
  rw [mem_conjAct_inv_J_iff, Matrix.SpecialLinearGroup.J_mul_mapGL_mul_J]
  exact ⟨_, rfl⟩

variable {k : ℤ}

/-- The conjugate cusp form `f^c(τ) = conj f(−conj τ)` at level one. -/
noncomputable abbrev conjForm (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k :=
  CuspForm.conj levelOne_le_conjAct_inv_J f

/-- `conj Λ(f, n + 1) = Λ(f^c, n + 1)`. -/
theorem conj_Λ_natCast_add_one (hk : 0 < k) (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    starRingEnd ℂ (ModularForm.Λ hk f (n + 1)) = ModularForm.Λ hk (conjForm f) (n + 1) := by
  rw [CuspForm.Λ_eq_mellin, CuspForm.Λ_eq_mellin, mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  have hJ : UpperHalfPlane.J • ofComplex (I * t) = ofComplex (I * t) := by
    apply UpperHalfPlane.ext
    rw [coe_J_smul, ofComplex_apply_of_im_pos (by simpa using ht)]
    simp
  simp only [smul_eq_mul, map_mul, add_sub_cancel_right, Complex.cpow_natCast, map_pow,
    Complex.conj_ofReal, CuspForm.conj_apply, hJ]

/-- `conj ρ_n(f) = (−1)^{n+1} ρ_n(f^c)` for the periods `ρ_n(f) = ∫₀^{i∞} f(τ) τⁿ dτ`. -/
theorem conj_cuspIntegral_mul_pow (hk : 0 < k) (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    starRingEnd ℂ (TauCeti.cuspIntegral (fun τ => f τ * (τ : ℂ) ^ n) ((0 : ℚ) : OnePoint ℚ) ∞) =
      (-1) ^ (n + 1) *
        TauCeti.cuspIntegral (fun τ => conjForm f τ * (τ : ℂ) ^ n) ((0 : ℚ) : OnePoint ℚ) ∞ := by
  rw [TauCeti.cuspIntegral_mul_pow_zero_infty hk, TauCeti.cuspIntegral_mul_pow_zero_infty hk,
    map_mul, map_pow, Complex.conj_I, conj_Λ_natCast_add_one, neg_pow]
  ring

/-- `r_f(x, 1) = ∑_j (w choose j) (−x)^{w−j} ρ_j(f)` for `w` even. -/
theorem eval_periodPolynomial_one {w : ℕ} (hk : k = w + 2) (hw : Even w) (f : CuspForm 𝒮ℒ k)
    (x : ℂ) :
    eval ![x, 1] ((TauCeti.periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) :
        MvPolynomial (Fin 2) ℂ) =
      ∑ j ∈ Finset.range (w + 1), (w.choose j : ℂ) * (-x) ^ (w - j) *
        TauCeti.cuspIntegral (fun τ => f τ * (τ : ℂ) ^ j) ((0 : ℚ) : OnePoint ℚ) ∞ := by
  rw [TauCeti.eval_periodPolynomial, ← cuspIntegral_mul_sub_pow f hk]
  congr 1
  funext τ
  rw [mul_one, ← hw.neg_pow, neg_sub]

/-- **Conjugation of the period polynomial**: for `w` even and `x` real,
`conj r_f(x, 1) = −r_{f^c}(−x, 1)`. -/
theorem conj_eval_periodPolynomial {w : ℕ} (hk : k = w + 2) (hw : Even w) (f : CuspForm 𝒮ℒ k)
    (x : ℝ) :
    starRingEnd ℂ (eval ![(x : ℂ), 1]
        ((TauCeti.periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) :
          MvPolynomial (Fin 2) ℂ)) =
      -eval ![-(x : ℂ), 1]
        ((TauCeti.periodPolynomial hk (conjForm f) : homogeneousSubmodule (Fin 2) ℂ w) :
          MvPolynomial (Fin 2) ℂ) := by
  have hk0 : 0 < k := by omega
  rw [eval_periodPolynomial_one hk hw, eval_periodPolynomial_one hk hw, map_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsign : (-1 : ℂ) ^ (w - j) * (-1) ^ (j + 1) = -1 := by
    rw [← pow_add, show w - j + (j + 1) = w + 1 by omega, pow_succ, hw.neg_one_pow]
    ring
  rw [map_mul, map_mul, map_pow, map_neg, Complex.conj_ofReal, map_natCast,
    conj_cuspIntegral_mul_pow hk0, neg_neg]
  have e : (-(x : ℂ)) ^ (w - j) = (-1) ^ (w - j) * (x : ℂ) ^ (w - j) := by
    rw [neg_pow]
  rw [e]
  linear_combination ((w.choose j : ℂ) * (x : ℂ) ^ (w - j) *
    TauCeti.cuspIntegral (fun τ => conjForm f τ * (τ : ℂ) ^ j) ((0 : ℚ) : OnePoint ℚ) ∞) * hsign

end TauTrack.Cohomology
