module

public import TauTrack.ElevenFive.Lattice
public import TauTrack.LevelEleven.Basic
public import TauCeti.Algebra.Module.ZLattice.SignedDiscriminant
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RealModel
import Mathlib.Tactic

/-!
# The theta series of the level-11 lattice, a modular form on `Γ₀(11)`

The real model `L11` of `lattice11` (Gram matrix `(2 1; 1 6) ⊕ (2 1; 1 6)`) is an even lattice of
rank 4, level dividing 11 and signed discriminant `121 = 11²`. By the Hecke–Schoeneberg theorem
(TauCeti's `ZLattice.IsEven.thetaSeries_slash_of_mem_Gamma0`) its theta series transforms under
`Γ₀(11)` by the Kronecker character of `121`, which is trivial. So

`θ(z) = ∑_{v ∈ L11} q^{|v|²/2} = ∑ q^{Q(x, y) + Q(z, w)}`,   `Q(x, y) = x² + xy + 3y²`,

is a modular form of weight 2 on `Γ₀(11)` (`theta11`), with integer coefficients, the
representation numbers, and constant term `1` (`qExpansion_theta11_coeff`,
`qExpansion_theta11_coeff_zero`).
-/

@[expose] public section

open Module UpperHalfPlane Matrix.SpecialLinearGroup
open TauCeti TauCeti.IntegralLattice
open scoped MatrixGroups ModularForm

namespace TauTrack.ElevenFive

/-- The real model of `lattice11`, an even lattice in a 4-dimensional Euclidean space. -/
noncomputable abbrev L11 : Submodule ℤ (lattice11.RealModelSpace isPosDef_lattice11) :=
  lattice11.realModel isPosDef_lattice11

theorem isEven_L11 : ZLattice.IsEven L11 :=
  (lattice11.isEven_realModel_iff isPosDef_lattice11).mpr isEven_lattice11

theorem finrank_lattice11 : finrank ℤ lattice11 = 4 := by
  rw [finrank_carrier]
  simp

theorem finrank_L11 : finrank ℝ (lattice11.RealModelSpace isPosDef_lattice11) = 2 * 2 := by
  rw [RealModelSpace.finrank_eq, finrank_lattice11]

theorem level_L11_dvd : (ZLattice.level L11 : ℤ) ∣ 11 := by
  rw [level_realModel]
  exact level_lattice11_dvd

theorem signedDiscr_L11 : ZLattice.signedDiscr L11 = 121 := by
  rw [signedDiscr_realModel, finrank_lattice11, determinant_lattice11]
  norm_num

/-- The theta character of `L11` is trivial: its signed discriminant `121` is a square. -/
theorem thetaCharacter_L11 (hE : Even (finrank ℝ (lattice11.RealModelSpace isPosDef_lattice11))) :
    isEven_L11.thetaCharacter hE = 1 :=
  ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare _ _ ⟨11, by rw [signedDiscr_L11]; norm_num⟩

/-- The lower-right entry of a matrix of `Γ₀(N)` is a unit modulo `N`. -/
theorem isUnit_of_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    IsUnit ((A 1 1 : ℤ) : ZMod N) := by
  have hc : ((A 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h := congrArg (fun x : ℤ ↦ (x : ZMod N)) hdet
  push_cast at h
  rw [hc, mul_zero, sub_zero, mul_comm] at h
  exact IsUnit.of_mul_eq_one _ h

/-- **The theta series of `L11` is a modular form of weight 2 on `Γ₀(11)`.** -/
noncomputable def theta11 : ModularForm Γ₁₁ 2 where
  toFun := ZLattice.thetaSeries L11
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    have hA' : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L11) := by
      rw [CongruenceSubgroup.mem_Gamma0_iff_dvd]
      exact level_L11_dvd.trans (CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA)
    have h := isEven_L11.thetaSeries_slash_of_mem_Gamma0 (k := 2) finrank_L11 hA'
    have hsq : IsSquare (ZLattice.signedDiscr L11) := ⟨11, by rw [signedDiscr_L11]; norm_num⟩
    have hχ := ZLattice.IsEven.thetaCharacter_eq_one_of_isSquare isEven_L11
      (by rw [finrank_L11]; decide) hsq
    simp only [hχ, MulChar.one_apply (isUnit_of_mem_Gamma0 hA'), one_smul, Nat.cast_ofNat] at h
    rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash, h]
  holo' := ZLattice.mdifferentiable_thetaSeries L11
  bdd_at_cusps' hc :=
    isEven_L11.isBoundedAt_thetaSeries (k := 2) finrank_L11 (hc.mono (Subgroup.map_le_range _ _))

theorem coe_theta11 : ⇑theta11 = ZLattice.thetaSeries L11 := by
  rfl

/-- The coefficients of `θ` are the representation numbers of `L11`. -/
theorem qExpansion_theta11_coeff (m : ℕ) :
    (qExpansion 1 theta11).coeff m = ZLattice.representationNumber L11 (2 * m) := by
  rw [coe_theta11, isEven_L11.qExpansion_thetaSeries_coeff]

theorem qExpansion_theta11_coeff_zero : (qExpansion 1 theta11).coeff 0 = 1 := by
  rw [qExpansion_theta11_coeff]
  simp

end TauTrack.ElevenFive
