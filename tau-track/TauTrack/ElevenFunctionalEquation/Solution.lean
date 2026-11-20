module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauTrack.ElevenFunctionalEquation.CentralValue

/-!
# Solution: the functional equation of the `L`-function of the newform of level 11

The statements of `Challenge.lean`, proved from `TauTrack.ElevenFunctionalEquation.Fricke` and
`TauTrack.ElevenFunctionalEquation.CentralValue`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ElevenFunctionalEquation

theorem fricke_relation (z : ℂ) (hz : 0 < z.im) :
    ModularForm.eta (-1 / (11 * z)) ^ 2 * ModularForm.eta (-1 / z) ^ 2 =
      -(11 * z ^ 2) * (ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) := by
  have h11 : 0 < (11 * z).im := by simpa using hz
  rw [TauCeti.ModularForm.eta_neg_one_div_sq h11, TauCeti.ModularForm.eta_neg_one_div_sq hz]
  linear_combination
    (11 * z ^ 2 * (ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2)) * Complex.I_sq

theorem exists_newform_functional_equation (hk : (0 : ℤ) < 2) :
    ∃ f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2,
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ s : ℂ, ModularForm.Λ hk f (2 - s) = (11 : ℂ) ^ (s - 1) * ModularForm.Λ hk f s) ∧
      (∃ r : ℝ, 0 < r ∧ ModularForm.L hk f 1 = r) ∧
      ∀ t : ℝ, ((11 : ℂ) ^ ((1 + t * Complex.I) / 2) *
        ModularForm.Λ hk f (1 + t * Complex.I)).im = 0 :=
  ⟨TauTrack.eta11Form, TauTrack.eta11Form_apply, TauTrack.Λ_eta11Form_two_sub,
    ⟨_, TauTrack.L_one_pos, TauTrack.L_one_eq_two_pi_integral⟩,
    TauTrack.im_cpow_mul_Λ_eta11Form⟩

end ElevenFunctionalEquation
