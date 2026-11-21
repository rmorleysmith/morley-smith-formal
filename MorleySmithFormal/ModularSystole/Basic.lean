module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Displacements in the modular group: the shortest closed geodesic has length `4 log φ`

For `γ = (a b; c d) ∈ SL(2, ℤ)` with trace `t = a + d`, and `z = x + iy` in the upper half-plane,

`cosh d(z, γz) = t²/2 − 1 + (c(x² + y²) + (d − a)x − b)² / (2y²)`   (`cosh_dist_smul`).

The proof computes `γz − z = −(cz² + (d − a)z − b)/(cz + d)` and uses the identity

`|cz² + (d − a)z − b|² = (c|z|² + (d − a)x − b)² + (t² − 4)y²`,

which holds because `ad − bc = 1`. The second term vanishes exactly on the circle
`c|z|² + (d − a)x − b = 0`, the axis of `γ`.

Consequences. An element with `|t| > 2` (a hyperbolic element) moves every point at least
`arcosh(t²/2 − 1)`, and moves the points of its axis exactly that far (`exists_cosh_dist_smul_eq`):
this is its translation length, the length of the closed geodesic it defines on the modular
surface. Since `t` is an integer, `|t| ≥ 3` and `t²/2 − 1 ≥ 7/2 = cosh(4 log φ)`, where
`φ = (1 + √5)/2`: every hyperbolic element moves every point at least `4 log φ`
(`four_mul_log_goldenRatio_le_dist`), and `(2 1; 1 1)` moves `i` exactly that far
(`dist_I_smul_golden`). So the shortest closed geodesic of the modular surface has length
`4 log φ = 2 log φ²`, where `φ²` is an eigenvalue of `(2 1; 1 1)`.

Also: the two elliptic points `i` and `ρ = e^{2πi/3}` are at distance `(log 3)/2`, so that
`tanh d(i, ρ) = 1/2` (`dist_I_of_re_im`, `tanh_dist_I_of_re_im`).
-/

@[expose] public section

open UpperHalfPlane Complex Real
open scoped MatrixGroups

namespace MorleySmithFormal.ModularSystole

/-- The algebraic identity behind the displacement formula. -/
theorem normSq_identity (a b c d x y : ℝ) (h : a * d - b * c = 1) :
    (c * (x ^ 2 - y ^ 2) + (d - a) * x - b) ^ 2 + (y * (2 * c * x + (d - a))) ^ 2 =
      (c * (x ^ 2 + y ^ 2) + (d - a) * x - b) ^ 2 + ((a + d) ^ 2 - 4) * y ^ 2 := by
  linear_combination (-4 * y ^ 2) * h

theorem det_eq_one (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - ((γ 0 1 : ℤ) : ℝ) * (γ 1 0 : ℤ) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- **The displacement formula.** -/
theorem cosh_dist_smul (γ : SL(2, ℤ)) (z : ℍ) :
    Real.cosh (dist z (γ • z)) =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 / 2 - 1 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / (2 * z.im ^ 2) := by
  set a : ℝ := ((γ 0 0 : ℤ) : ℝ) with ha
  set b : ℝ := ((γ 0 1 : ℤ) : ℝ) with hb
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hc
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hd
  have hdet : a * d - b * c = 1 := det_eq_one γ
  have hy : 0 < z.im := z.im_pos
  set D : ℂ := (c : ℂ) * z + d with hD
  have hD0 : D ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
    have h2 : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z = D := by
      simp [UpperHalfPlane.denom, hD, hc, hd]
    rwa [h2] at h
  have hcoe : ((γ • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [ha, hb, hc, hd, hD]
  have him : (γ • z).im = z.im / Complex.normSq D := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, hD, hc, hd]
    push_cast
    rfl
  have hdiff : (z : ℂ) - ((γ • z : ℍ) : ℂ) = ((c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b) / D := by
    rw [hcoe]
    field_simp
    ring
  have hP : Complex.normSq ((c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b) =
      (c * (z.re ^ 2 + z.im ^ 2) + (d - a) * z.re - b) ^ 2 + ((a + d) ^ 2 - 4) * z.im ^ 2 := by
    rw [← normSq_identity a b c d z.re z.im hdet]
    have hz : (z : ℂ) = ⟨z.re, z.im⟩ := by
      apply Complex.ext <;> simp
    rw [hz]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    ring
  rw [UpperHalfPlane.cosh_dist, Complex.dist_eq, hdiff, norm_div, div_pow, Complex.sq_norm,
    Complex.sq_norm, him, hP]
  have hDpos : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD0
  have : ((γ 0 0 + γ 1 1 : ℤ) : ℝ) = a + d := by push_cast; rfl
  rw [this]
  field_simp
  ring

/-- `cosh(4 log φ) = 7/2`. -/
theorem cosh_four_mul_log_goldenRatio : Real.cosh (4 * Real.log goldenRatio) = 7 / 2 := by
  have hφ : 0 < goldenRatio := goldenRatio_pos
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
    have : goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
    rw [this, h2]
    linear_combination h2
  have hinv : (goldenRatio ^ 4)⁻¹ = 5 - 3 * goldenRatio := by
    apply inv_eq_of_mul_eq_one_right
    rw [h4]
    linear_combination (-9 : ℝ) * h2
  have hlog : 4 * Real.log goldenRatio = Real.log (goldenRatio ^ 4) := by
    rw [Real.log_pow]
    norm_num
  rw [hlog, Real.cosh_log (by positivity), hinv, h4]
  ring

theorem four_mul_log_goldenRatio_pos : 0 < 4 * Real.log goldenRatio := by
  have := Real.log_pos one_lt_goldenRatio
  positivity

/-- **Every hyperbolic element of the modular group moves every point at least `4 log φ`.** -/
theorem four_mul_log_goldenRatio_le_dist (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    4 * Real.log goldenRatio ≤ dist z (γ • z) := by
  have h3 : (3 : ℤ) ≤ |γ 0 0 + γ 1 1| := h
  have h9 : (9 : ℝ) ≤ ((γ 0 0 + γ 1 1 : ℤ) : ℝ) ^ 2 := by
    have : (9 : ℤ) ≤ (γ 0 0 + γ 1 1) ^ 2 := by
      rw [← sq_abs]
      nlinarith
    exact_mod_cast this
  have hcosh : Real.cosh (4 * Real.log goldenRatio) ≤ Real.cosh (dist z (γ • z)) := by
    rw [cosh_four_mul_log_goldenRatio, cosh_dist_smul]
    have hnn : 0 ≤ (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) +
        (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re - (γ 0 1 : ℤ)) ^ 2 / (2 * z.im ^ 2) := by
      positivity
    linarith
  rw [Real.cosh_le_cosh, abs_of_pos four_mul_log_goldenRatio_pos, abs_of_nonneg dist_nonneg] at hcosh
  exact hcosh

/-- The matrix `(2 1; 1 1)`. -/
def golden : SL(2, ℤ) := ⟨!![2, 1; 1, 1], by decide⟩

/-- **`(2 1; 1 1)` moves `i` exactly `4 log φ`.** -/
theorem dist_I_smul_golden : dist UpperHalfPlane.I (golden • UpperHalfPlane.I) =
    4 * Real.log goldenRatio := by
  have h : Real.cosh (dist UpperHalfPlane.I (golden • UpperHalfPlane.I)) =
      Real.cosh (4 * Real.log goldenRatio) := by
    rw [cosh_four_mul_log_goldenRatio, cosh_dist_smul]
    simp [golden, UpperHalfPlane.I_re, UpperHalfPlane.I_im]
    norm_num
  have h1 := (Real.cosh_le_cosh.mp h.le)
  have h2 := (Real.cosh_le_cosh.mp h.ge)
  rw [abs_of_pos four_mul_log_goldenRatio_pos, abs_of_nonneg dist_nonneg] at h1 h2
  exact le_antisymm h1 h2

/-- **The translation length.** A hyperbolic element moves the points of its axis exactly
`arcosh(t²/2 − 1)`. -/
theorem exists_cosh_dist_smul_eq (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) :
    ∃ z : ℍ, Real.cosh (dist z (γ • z)) = ((γ 0 0 + γ 1 1 : ℤ) : ℝ) ^ 2 / 2 - 1 := by
  have hc : γ 1 0 ≠ 0 := by
    intro hc0
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc0, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] at h <;> norm_num at h
  set a : ℝ := ((γ 0 0 : ℤ) : ℝ) with ha
  set b : ℝ := ((γ 0 1 : ℤ) : ℝ) with hb
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hcdef
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hd
  have hdet : a * d - b * c = 1 := det_eq_one γ
  have hc' : c ≠ 0 := by rw [hcdef]; exact_mod_cast hc
  have ht : (4 : ℝ) < (a + d) ^ 2 := by
    have h3 : (3 : ℤ) ≤ |γ 0 0 + γ 1 1| := h
    have : (9 : ℤ) ≤ (γ 0 0 + γ 1 1) ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h9 : (9 : ℝ) ≤ (a + d) ^ 2 := by
      rw [ha, hd]
      exact_mod_cast this
    linarith
  set y : ℝ := √((a + d) ^ 2 - 4) / (2 * |c|) with hy
  have hypos : 0 < y := by
    rw [hy]
    have : 0 < √((a + d) ^ 2 - 4) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hysq : y ^ 2 = ((a + d) ^ 2 - 4) / (4 * c ^ 2) := by
    rw [hy, div_pow, Real.sq_sqrt (by linarith), mul_pow, sq_abs]
    norm_num
  refine ⟨⟨⟨(a - d) / (2 * c), y⟩, hypos⟩, ?_⟩
  rw [cosh_dist_smul]
  have hre : (⟨⟨(a - d) / (2 * c), y⟩, hypos⟩ : ℍ).re = (a - d) / (2 * c) := rfl
  have him : (⟨⟨(a - d) / (2 * c), y⟩, hypos⟩ : ℍ).im = y := rfl
  rw [hre, him]
  have hA : c * (((a - d) / (2 * c)) ^ 2 + y ^ 2) + (d - a) * ((a - d) / (2 * c)) - b = 0 := by
    rw [hysq]
    field_simp
    linear_combination (16 : ℝ) * hdet
  have : ((γ 0 0 + γ 1 1 : ℤ) : ℝ) = a + d := by push_cast; rfl
  rw [this, hA]
  simp

/-- The distance from `i` to a point with real part `±1/2` and imaginary part `√3/2`. -/
theorem cosh_dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    Real.cosh (dist UpperHalfPlane.I z) = 2 / √3 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [UpperHalfPlane.cosh_dist, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  have hI : ((UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := rfl
  simp only [hI, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, UpperHalfPlane.I_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, him]
  field_simp
  nlinarith [hre, hsq]

theorem cosh_half_log_three : Real.cosh (Real.log 3 / 2) = 2 / √3 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← Real.log_sqrt (by norm_num), Real.cosh_log h3]
  field_simp
  nlinarith [hsq]

/-- **The elliptic points `i` and `ρ` are at distance `(log 3)/2`.** -/
theorem dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    dist UpperHalfPlane.I z = Real.log 3 / 2 := by
  have h : Real.cosh (dist UpperHalfPlane.I z) = Real.cosh (Real.log 3 / 2) := by
    rw [cosh_dist_I_of_re_im z hre him, cosh_half_log_three]
  have hpos : 0 < Real.log 3 / 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    positivity
  have h1 := (Real.cosh_le_cosh.mp h.le)
  have h2 := (Real.cosh_le_cosh.mp h.ge)
  rw [abs_of_pos hpos, abs_of_nonneg dist_nonneg] at h1 h2
  exact le_antisymm h1 h2

/-- **`tanh d(i, ρ) = 1/2`**: as velocities, `i` and `ρ` differ by half the limiting speed. -/
theorem tanh_dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    Real.tanh (dist UpperHalfPlane.I z) = 1 / 2 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [dist_I_of_re_im z hre him, Real.tanh_eq_sinh_div_cosh, cosh_half_log_three,
    ← Real.log_sqrt (by norm_num), Real.sinh_log h3]
  field_simp
  nlinarith [hsq]

end MorleySmithFormal.ModularSystole
