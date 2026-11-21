module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Challenge: the shortest closed geodesic of the modular surface has length `4 log φ`

Let `SL(2, ℤ)` act on the upper half-plane `ℍ` with its hyperbolic distance `d` (Mathlib's
`dist`), let `φ = (1 + √5)/2` be the golden ratio, and for `γ = (a b; c d)` write `t = a + d`.
The statements say:

1. `cosh_dist_smul`: for every `γ` and every `z = x + iy` in `ℍ`,
   `cosh d(z, γz) = t²/2 − 1 + (c(x² + y²) + (d − a)x − b)² / (2y²)`.
2. `four_mul_log_goldenRatio_le_dist`: if `|t| > 2` (a hyperbolic element), then
   `d(z, γz) ≥ 4 log φ` for every `z`.
3. `exists_dist_eq_four_mul_log_goldenRatio`: the matrix `(2 1; 1 1)` moves the point `i`
   exactly `4 log φ`.
4. `exists_cosh_dist_smul_eq`: if `|t| > 2`, some point is moved exactly `arcosh(t²/2 − 1)`,
   which by statement 1 is the least displacement: the translation length of `γ`.
5. `dist_I_of_re_im` and `tanh_dist_I_of_re_im`: a point with real part `±1/2` and imaginary
   part `√3/2` (the elliptic point `ρ = e^{2πi/3}` or `e^{πi/3}`) is at distance `(log 3)/2`
   from `i`, so that `tanh d(i, ρ) = 1/2`.

A hyperbolic element translates along its axis, which projects to a closed geodesic of the
modular surface `SL(2, ℤ) \ ℍ` whose length is the translation length; so statements 2 to 4 say
that the closed geodesics have lengths `arcosh(t²/2 − 1) = 2 arcosh(|t|/2)`, `|t| ≥ 3`, the
shortest being `4 log φ`. Only Mathlib definitions are used. This file states the results only;
the proofs are in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularSystole

theorem cosh_dist_smul (γ : SL(2, ℤ)) (z : ℍ) :
    Real.cosh (dist z (γ • z)) =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 / 2 - 1 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / (2 * z.im ^ 2) := by
  sorry

theorem four_mul_log_goldenRatio_le_dist (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    4 * Real.log Real.goldenRatio ≤ dist z (γ • z) := by
  sorry

theorem exists_dist_eq_four_mul_log_goldenRatio :
    ∃ γ : SL(2, ℤ), γ 0 0 = 2 ∧ γ 0 1 = 1 ∧ γ 1 0 = 1 ∧ γ 1 1 = 1 ∧
      dist UpperHalfPlane.I (γ • UpperHalfPlane.I) = 4 * Real.log Real.goldenRatio := by
  sorry

theorem exists_cosh_dist_smul_eq (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) :
    ∃ z : ℍ, Real.cosh (dist z (γ • z)) = ((γ 0 0 + γ 1 1 : ℤ) : ℝ) ^ 2 / 2 - 1 := by
  sorry

theorem dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    dist UpperHalfPlane.I z = Real.log 3 / 2 := by
  sorry

theorem tanh_dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    Real.tanh (dist UpperHalfPlane.I z) = 1 / 2 := by
  sorry

end ModularSystole
