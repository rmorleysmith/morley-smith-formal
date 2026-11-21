module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MorleySmithFormal.ModularSystole.Basic

/-!
# Solution: the shortest closed geodesic of the modular surface has length `4 log φ`

The statements of `Challenge.lean`, proved from `MorleySmithFormal.ModularSystole.Basic`.
-/

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularSystole

theorem cosh_dist_smul (γ : SL(2, ℤ)) (z : ℍ) :
    Real.cosh (dist z (γ • z)) =
      (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 / 2 - 1 +
        (((γ 1 0 : ℤ) : ℝ) * (z.re ^ 2 + z.im ^ 2) + (((γ 1 1 : ℤ) : ℝ) - (γ 0 0 : ℤ)) * z.re -
          (γ 0 1 : ℤ)) ^ 2 / (2 * z.im ^ 2) :=
  MorleySmithFormal.ModularSystole.cosh_dist_smul γ z

theorem four_mul_log_goldenRatio_le_dist (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) (z : ℍ) :
    4 * Real.log Real.goldenRatio ≤ dist z (γ • z) :=
  MorleySmithFormal.ModularSystole.four_mul_log_goldenRatio_le_dist γ h z

theorem exists_dist_eq_four_mul_log_goldenRatio :
    ∃ γ : SL(2, ℤ), γ 0 0 = 2 ∧ γ 0 1 = 1 ∧ γ 1 0 = 1 ∧ γ 1 1 = 1 ∧
      dist UpperHalfPlane.I (γ • UpperHalfPlane.I) = 4 * Real.log Real.goldenRatio :=
  ⟨MorleySmithFormal.ModularSystole.golden, rfl, rfl, rfl, rfl, MorleySmithFormal.ModularSystole.dist_I_smul_golden⟩

theorem exists_cosh_dist_smul_eq (γ : SL(2, ℤ)) (h : 2 < |γ 0 0 + γ 1 1|) :
    ∃ z : ℍ, Real.cosh (dist z (γ • z)) = ((γ 0 0 + γ 1 1 : ℤ) : ℝ) ^ 2 / 2 - 1 :=
  MorleySmithFormal.ModularSystole.exists_cosh_dist_smul_eq γ h

theorem dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    dist UpperHalfPlane.I z = Real.log 3 / 2 :=
  MorleySmithFormal.ModularSystole.dist_I_of_re_im z hre him

theorem tanh_dist_I_of_re_im (z : ℍ) (hre : z.re ^ 2 = 1 / 4) (him : z.im = √3 / 2) :
    Real.tanh (dist UpperHalfPlane.I z) = 1 / 2 :=
  MorleySmithFormal.ModularSystole.tanh_dist_I_of_re_im z hre him

end ModularSystole
