module

public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import TauTrack.Cohomology.DeltaLValues

/-!
# Solution: rational ratios of critical values of Ramanujan's `L`-function

The statements of `Challenge.lean`, proved from `TauTrack.Cohomology.DeltaLValues`.
-/

@[expose] public section

namespace RamanujanLValues

theorem L_four (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 4 =
      25 * (Real.pi : ℂ) ^ 2 / 72 * ModularForm.L hk CuspForm.discriminant 2 :=
  TauTrack.Cohomology.L_delta_four

theorem L_six (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 6 =
      (Real.pi : ℂ) ^ 4 / 18 * ModularForm.L hk CuspForm.discriminant 2 :=
  TauTrack.Cohomology.L_delta_six

theorem L_five (hk : (0 : ℤ) < 12) :
    ModularForm.L hk CuspForm.discriminant 5 =
      3 * (Real.pi : ℂ) ^ 2 / 14 * ModularForm.L hk CuspForm.discriminant 3 :=
  TauTrack.Cohomology.L_delta_five

end RamanujanLValues
