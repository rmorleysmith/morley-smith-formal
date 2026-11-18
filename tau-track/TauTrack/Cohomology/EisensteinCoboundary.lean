module

public import TauTrack.Cohomology.PeriodCocycle
import Mathlib.Tactic

/-!
# The Eisenstein period polynomial is a coboundary

The form `Y^w` is fixed by `T`, so its coboundary `γ ↦ Y^w ∣ γ − Y^w` is a parabolic cocycle. Its
value at `S` is `X^w − Y^w`, TauCeti's `eisensteinPeriodPolynomial`.

So under `φ ↦ φ(S)` the parabolic coboundaries go to the line spanned by `X^w − Y^w`, and the
parabolic cohomology is the quotient of the period polynomials by that line.

* `act_T_Y_pow`: `Y^w ∣ T = Y^w`.
* `act_S_Y_pow`: `Y^w ∣ S = X^w`.
* `eisensteinCocycle`, `isCocycle_eisensteinCocycle`, `eisensteinCocycle_T`,
  `eisensteinCocycle_S`: the coboundary of `Y^w` and its values.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

variable {R : Type*} [CommRing R] {w : ℕ}

variable (R w) in
/-- The binary form `Y^w`. -/
noncomputable def yPow : homogeneousSubmodule (Fin 2) R w :=
  ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩

/-- `Y^w ∣ T = Y^w`. -/
theorem act_T_Y_pow : act (yPow R w) T = yPow R w := by
  have h := TauCeti.binaryFormRep_upperTriangular_X_one_pow (R := R) (w := w)
    (M := (T : Matrix (Fin 2) (Fin 2) ℤ)) (by simp [ModularGroup.coe_T])
  rw [act, yPow, h]
  simp [ModularGroup.coe_T]

/-- `Y^w ∣ S = X^w`. -/
theorem act_S_Y_pow :
    (act (yPow R w) S : MvPolynomial (Fin 2) R) = X 0 ^ w := by
  rw [act, TauCeti.coe_binaryFormRep_apply, yPow]
  simp [Fin.sum_univ_two, ModularGroup.coe_S]

/-- The coboundary of `Y^w`. -/
noncomputable def eisensteinCocycle (γ : SL(2, ℤ)) : homogeneousSubmodule (Fin 2) R w :=
  act (yPow R w) γ - yPow R w

theorem isCocycle_eisensteinCocycle :
    IsCocycle (eisensteinCocycle : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w) :=
  IsCocycle.coboundary (yPow R w)

/-- The coboundary of `Y^w` is parabolic. -/
theorem eisensteinCocycle_T :
    (eisensteinCocycle T : homogeneousSubmodule (Fin 2) R w) = 0 := by
  rw [eisensteinCocycle, act_T_Y_pow, sub_self]

/-- **Its value at `S` is the Eisenstein period polynomial `X^w − Y^w`.** -/
theorem eisensteinCocycle_S :
    (eisensteinCocycle S : homogeneousSubmodule (Fin 2) R w) =
      TauCeti.eisensteinPeriodPolynomial R w := by
  apply Subtype.ext
  rw [eisensteinCocycle, TauCeti.coe_eisensteinPeriodPolynomial]
  change (act (yPow R w) S : MvPolynomial (Fin 2) R) - (yPow R w : MvPolynomial (Fin 2) R) = _
  rw [act_S_Y_pow]
  rfl

end TauTrack.Cohomology
