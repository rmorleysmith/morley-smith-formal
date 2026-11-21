module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.NumberTheory.Modular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MorleySmithFormal.ModularSystole.Basic
import Mathlib.Tactic

/-!
# The log-determinant divergence of two lattice metrics

A point `z = x + iy` of the upper half-plane gives the lattice `ℤ + ℤz` with the oriented basis
`(z, 1)`. The Gram matrix of that basis divided by the covolume `y` is

`M(z) = (1/y) · [[x² + y², x], [x, 1]]`,

of determinant one. For two points `z`, `w` put `G = M(z) · M(w)⁻¹`. Then `det G = 1` and
`tr G = 2 cosh d(z, w)`, with `d` the hyperbolic distance, so the eigenvalues of `G` are `e^{±d}` and
the log-determinant divergence `tr G − 2 − log det G = tr(G − 1 − log G)` equals `2 cosh d − 2`.
For a change of basis `γ ∈ SL(2, ℤ)`, `w = γ z`, the displacement formula of
`MorleySmithFormal.ModularSystole` gives `t² − 4 + (c(x² + y²) + (d − a)x − b)² / y²`, `t = tr γ`.
-/

@[expose] public section

open UpperHalfPlane Matrix
open scoped MatrixGroups

namespace MorleySmithFormal.LatticeMetricDivergence

/-- The metric of the lattice `ℤ + ℤz`, normalised to determinant one. -/
noncomputable def latticeMetric (z : ℍ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(z.re ^ 2 + z.im ^ 2) / z.im, z.re / z.im; z.re / z.im, 1 / z.im]

theorem det_latticeMetric (z : ℍ) : (latticeMetric z).det = 1 := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  simp only [latticeMetric, Matrix.det_fin_two_of]
  field_simp
  ring

theorem inv_latticeMetric (z : ℍ) :
    (latticeMetric z)⁻¹ =
      !![1 / z.im, -(z.re / z.im); -(z.re / z.im), (z.re ^ 2 + z.im ^ 2) / z.im] := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [latticeMetric, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem det_mul_inv (z w : ℍ) : (latticeMetric z * (latticeMetric w)⁻¹).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_latticeMetric,
    det_latticeMetric]
  simp

theorem trace_mul_inv (z w : ℍ) :
    (latticeMetric z * (latticeMetric w)⁻¹).trace = 2 * Real.cosh (dist z w) := by
  have hz : z.im ≠ 0 := z.im_pos.ne'
  have hw : w.im ≠ 0 := w.im_pos.ne'
  rw [inv_latticeMetric, UpperHalfPlane.cosh_dist, Complex.dist_eq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  simp only [latticeMetric, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  simp
  field_simp
  ring

/-- The relative entropy `∑ (λ − 1 − log λ)` over the eigenvalues `e^{d}`, `e^{−d}`. -/
theorem entropy_eigenvalues (d : ℝ) :
    (Real.exp d - 1 - Real.log (Real.exp d)) + (Real.exp (-d) - 1 - Real.log (Real.exp (-d))) =
      2 * Real.cosh d - 2 := by
  rw [Real.log_exp, Real.log_exp, Real.cosh_eq]
  ring

/-- `e^{d}` and `e^{−d}`, `d = d(z, w)`, are the roots of `λ² − (tr G) λ + det G`. -/
theorem eigenvalue_equation (z w : ℍ) (s : ℝ) (hs : s = dist z w ∨ s = -dist z w) :
    Real.exp s ^ 2 - (latticeMetric z * (latticeMetric w)⁻¹).trace * Real.exp s +
      (latticeMetric z * (latticeMetric w)⁻¹).det = 0 := by
  rw [trace_mul_inv, det_mul_inv, Real.cosh_eq]
  have h1 : Real.exp (dist z w) * Real.exp (-dist z w) = 1 := by
    rw [← Real.exp_add]; simp
  rcases hs with rfl | rfl
  · linear_combination (-1 : ℝ) * h1
  · linear_combination (-1 : ℝ) * h1

/-- **Change of basis.** For `γ ∈ SL(2, ℤ)` with trace `t`, the relative entropy of the metrics of
`z` and `γ z` is `t² − 4` plus a square that vanishes on the axis of `γ`. -/
theorem entropy_smul (γ : SL(2, ℤ)) (z : ℍ) :
    2 * Real.cosh (dist z (γ • z)) - 2 =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / z.im ^ 2 := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  rw [MorleySmithFormal.ModularSystole.cosh_dist_smul]
  field_simp
  ring

/-- The relative entropy is at least the discriminant `t² − 4` of `γ`. -/
theorem discriminant_le_entropy (γ : SL(2, ℤ)) (z : ℍ) :
    (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 ≤ 2 * Real.cosh (dist z (γ • z)) - 2 := by
  rw [entropy_smul]
  have : (0 : ℝ) ≤ (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) +
      (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re - (γ 0 1 : ℤ)) ^ 2 / z.im ^ 2 := by positivity
  linarith

/-- For a hyperbolic `γ` the relative entropy is at least `5`. -/
theorem five_le_entropy (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    5 ≤ 2 * Real.cosh (dist z (γ • z)) - 2 := by
  have h3 : (3 : ℤ) ≤ |γ 0 0 + γ 1 1| := by omega
  have h9 : (9 : ℝ) ≤ (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 := by
    have : (3 : ℝ) ≤ |((γ 0 0 + γ 1 1 : ℤ) : ℝ)| := by exact_mod_cast h3
    nlinarith [sq_abs (((γ 0 0 + γ 1 1 : ℤ) : ℝ)), abs_nonneg (((γ 0 0 + γ 1 1 : ℤ) : ℝ))]
  linarith [discriminant_le_entropy γ z]

/-- Equality: `(2 1; 1 1)` and the square lattice. -/
theorem entropy_golden :
    2 * Real.cosh (dist UpperHalfPlane.I (MorleySmithFormal.ModularSystole.golden • UpperHalfPlane.I)) - 2 =
      5 := by
  rw [MorleySmithFormal.ModularSystole.dist_I_smul_golden, MorleySmithFormal.ModularSystole.cosh_four_mul_log_goldenRatio]
  norm_num

/-- The log-determinant divergence `tr(A B⁻¹) − 2 − log det(A B⁻¹)` of two `2 × 2` matrices. For
positive definite `A`, `B` it is `tr(G − 1 − log G)` with `G = A B⁻¹`, twice the Kullback–Leibler
divergence of the centred Gaussian distributions with covariances `A` and `B`. -/
noncomputable def divergence (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A * B⁻¹).trace - 2 - Real.log (A * B⁻¹).det

theorem divergence_latticeMetric (z w : ℍ) :
    divergence (latticeMetric z) (latticeMetric w) = 2 * Real.cosh (dist z w) - 2 := by
  rw [divergence, det_mul_inv, trace_mul_inv, Real.log_one, sub_zero]

theorem divergence_smul (γ : SL(2, ℤ)) (z : ℍ) :
    divergence (latticeMetric z) (latticeMetric (γ • z)) =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / z.im ^ 2 := by
  rw [divergence_latticeMetric, entropy_smul]

theorem discriminant_le_divergence (γ : SL(2, ℤ)) (z : ℍ) :
    (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 ≤ divergence (latticeMetric z) (latticeMetric (γ • z)) := by
  rw [divergence_latticeMetric]
  exact discriminant_le_entropy γ z

theorem divergence_eq_discriminant_iff (γ : SL(2, ℤ)) (z : ℍ) :
    divergence (latticeMetric z) (latticeMetric (γ • z)) = (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 ↔
      ((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
        (γ 0 1 : ℤ) = 0 := by
  have hy : z.im ^ 2 ≠ 0 := pow_ne_zero 2 z.im_pos.ne'
  rw [divergence_smul]
  constructor
  · intro h
    have h0 : (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
        (γ 0 1 : ℤ)) ^ 2 / z.im ^ 2 = 0 := by linarith
    rw [div_eq_zero_iff] at h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h0.resolve_right hy)
  · intro h
    rw [h]
    simp

theorem five_le_divergence (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    5 ≤ divergence (latticeMetric z) (latticeMetric (γ • z)) := by
  rw [divergence_latticeMetric]
  exact five_le_entropy γ h z

theorem divergence_golden :
    divergence (latticeMetric UpperHalfPlane.I)
      (latticeMetric (MorleySmithFormal.ModularSystole.golden • UpperHalfPlane.I)) = 5 := by
  rw [divergence_latticeMetric]
  exact entropy_golden

end MorleySmithFormal.LatticeMetricDivergence
