module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.NumberTheory.Modular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Challenge: the log-determinant divergence of two lattice metrics

A point `z = x + iy` of the upper half-plane gives the lattice `ℤ + ℤz` with the oriented basis
`(z, 1)`; every lattice in `ℂ` with an oriented basis is `c(ℤ + ℤz)` for a unique such `z` and some
`c ∈ ℂˣ`. The Gram matrix of the basis divided by the covolume `y` is
`M(z) = (1/y) · [[x² + y², x], [x, 1]]` (`latticeMetric`), of determinant one. For `2 × 2` matrices
`A`, `B` let `divergence A B = tr(A B⁻¹) − 2 − log det(A B⁻¹)`; for positive definite `A`, `B` this is
`tr(G − 1 − log G)` with `G = A B⁻¹`, twice the Kullback–Leibler divergence
`KL(N(0, A) ‖ N(0, B))` of the centred Gaussian distributions. The statements say, with `G = M(z) · M(w)⁻¹`:

1. `det_mul_inv`, `trace_mul_inv`: `det G = 1` and `tr G = 2 cosh d(z, w)`, `d` the hyperbolic
   distance;
2. `eigenvalue_equation`: `e^{d}` and `e^{−d}` are the roots of `λ² − (tr G) λ + det G`;
3. `sum_eigenvalues`: `(e^d − 1 − log e^d) + (e^{−d} − 1 − log e^{−d}) = 2 cosh d − 2`;
4. `divergence_latticeMetric`: `divergence (M z) (M w) = 2 cosh d(z, w) − 2`;
5. `divergence_smul`: for `γ = (a b; c d) ∈ SL(2, ℤ)` with trace `t`,
   `divergence (M z) (M (γ z)) = t² − 4 + (c(x² + y²) + (d − a)x − b)² / y²`;
6. `discriminant_le_divergence`, `divergence_eq_discriminant_iff`: this is at least `t² − 4`, with
   equality exactly when `c(x² + y²) + (d − a)x − b = 0` (for `|t| > 2`, the axis of `γ`);
7. `five_le_divergence`, `divergence_golden`: for `|t| > 2` it is at least `5`, and
   `golden = (2 1; 1 1)` attains `5` at `z = i`.

The expression `tr(G − 1 − log G)` has the form of the emergent cosmological term
`Λ_𝒢 = (1/6β) Tr_F(𝒢 − I − ln 𝒢)` of G. Bianconi's theory of gravity from entropy
(Phys. Lett. B 882 (2026) 141014, equation (19)); here it is evaluated on lattice metrics. The file
imports only Mathlib and states the results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane Matrix
open scoped MatrixGroups

namespace LatticeMetricDivergence

/-- The Gram matrix of the basis `(z, 1)` of the lattice `ℤ + ℤz`, divided by the covolume. -/
noncomputable def latticeMetric (z : ℍ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(z.re ^ 2 + z.im ^ 2) / z.im, z.re / z.im; z.re / z.im, 1 / z.im]

/-- The log-determinant divergence `tr(A B⁻¹) − 2 − log det(A B⁻¹)`. -/
noncomputable def divergence (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A * B⁻¹).trace - 2 - Real.log (A * B⁻¹).det

/-- The matrix `(2 1; 1 1)`, of trace 3. -/
def golden : SL(2, ℤ) := ⟨!![2, 1; 1, 1], by decide⟩

theorem det_mul_inv (z w : ℍ) : (latticeMetric z * (latticeMetric w)⁻¹).det = 1 := by
  sorry

theorem trace_mul_inv (z w : ℍ) :
    (latticeMetric z * (latticeMetric w)⁻¹).trace = 2 * Real.cosh (dist z w) := by
  sorry

theorem eigenvalue_equation (z w : ℍ) (s : ℝ) (hs : s = dist z w ∨ s = -dist z w) :
    Real.exp s ^ 2 - (latticeMetric z * (latticeMetric w)⁻¹).trace * Real.exp s +
      (latticeMetric z * (latticeMetric w)⁻¹).det = 0 := by
  sorry

theorem sum_eigenvalues (d : ℝ) :
    (Real.exp d - 1 - Real.log (Real.exp d)) + (Real.exp (-d) - 1 - Real.log (Real.exp (-d))) =
      2 * Real.cosh d - 2 := by
  sorry

theorem divergence_latticeMetric (z w : ℍ) :
    divergence (latticeMetric z) (latticeMetric w) = 2 * Real.cosh (dist z w) - 2 := by
  sorry

theorem divergence_smul (γ : SL(2, ℤ)) (z : ℍ) :
    divergence (latticeMetric z) (latticeMetric (γ • z)) =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / z.im ^ 2 := by
  sorry

theorem discriminant_le_divergence (γ : SL(2, ℤ)) (z : ℍ) :
    (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 ≤ divergence (latticeMetric z) (latticeMetric (γ • z)) := by
  sorry

theorem divergence_eq_discriminant_iff (γ : SL(2, ℤ)) (z : ℍ) :
    divergence (latticeMetric z) (latticeMetric (γ • z)) = (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 - 4 ↔
      ((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
        (γ 0 1 : ℤ) = 0 := by
  sorry

theorem five_le_divergence (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    5 ≤ divergence (latticeMetric z) (latticeMetric (γ • z)) := by
  sorry

theorem divergence_golden :
    divergence (latticeMetric UpperHalfPlane.I) (latticeMetric (golden • UpperHalfPlane.I)) = 5 := by
  sorry

end LatticeMetricDivergence
