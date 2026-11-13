module

public import TauTrack.Siegel.ThetaInversionGeneral
public import TauTrack.Siegel.Generators

/-!
# The theta series of an even unimodular lattice and the generators of `Sp(2n, ℤ)`

For an even unimodular lattice `L` of rank `2k`, the function `Z ↦ Θ_L(Z)` on `ℍ_n` is invariant
under the weight `k` slash action of the three standard kinds of integral symplectic matrix:

* `gJ = (0 −1; 1 0)` (`slash_gJ`, from the inversion);
* `gT S = (1 S; 0 1)`, `S` symmetric integral (`slash_gT`);
* `gU U V = (U 0; 0 Vᵀ)`, `U V = V U = 1` integral (`slash_gU`).

Hence it is invariant under the subgroup `standardSubgroup n` they generate
(`slash_thetaFun_of_mem`). That this subgroup is all of `Sp(2n, ℤ)` is proved in
`Generation.lean` (`standardSubgroup_eq_top`). Here `thetaForm` builds the Siegel modular form
`Θ_L` of weight `k` from the hypothesis `standardSubgroup n = ⊤`; `ThetaModular.lean` removes
the hypothesis (`thetaModularForm`).
-/

@[expose] public section

open Matrix Complex Module
open scoped Real RealInnerProductSpace ComplexOrder MatrixOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The three kinds of generator -/

/-- An integral matrix as a complex matrix. -/
def ci (A : Matrix n n ℤ) : Matrix n n ℂ := A.map (Int.cast : ℤ → ℂ)

theorem cx_map_castRingHom (A : Matrix n n ℤ) : cx (A.map (Int.castRingHom ℝ)) = ci A := by
  ext i j; simp [cx, ci]

@[simp] theorem ci_zero : ci (0 : Matrix n n ℤ) = 0 := by ext i j; simp [ci]

@[simp] theorem ci_one : ci (1 : Matrix n n ℤ) = 1 := by
  ext i j; simp [ci, Matrix.one_apply]

@[simp] theorem ci_neg (A : Matrix n n ℤ) : ci (-A) = -ci A := by ext i j; simp [ci]

theorem ci_mul (A B : Matrix n n ℤ) : ci (A * B) = ci A * ci B := by
  ext i j; simp [ci, Matrix.mul_apply]

theorem ci_transpose (A : Matrix n n ℤ) : ci Aᵀ = (ci A)ᵀ := rfl

theorem det_ci (A : Matrix n n ℤ) : (ci A).det = (A.det : ℂ) := by
  have h := (Int.castRingHom ℂ).map_det A
  simpa [ci, RingHom.mapMatrix_apply] using h.symm

theorem num_ofInt_fromBlocks (A B C D : Matrix n n ℤ)
    (h : fromBlocks A B C D ∈ symplecticGroup n ℤ) (Z : Matrix n n ℂ) :
    num (ofInt ⟨fromBlocks A B C D, h⟩).1 Z = ci A * Z + ci B := by
  simp only [num, ofInt, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply, fromBlocks_map,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, cx_map_castRingHom]

theorem den_ofInt_fromBlocks (A B C D : Matrix n n ℤ)
    (h : fromBlocks A B C D ∈ symplecticGroup n ℤ) (Z : Matrix n n ℂ) :
    den (ofInt ⟨fromBlocks A B C D, h⟩).1 Z = ci C * Z + ci D := by
  simp only [den, ofInt, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply, fromBlocks_map,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, cx_map_castRingHom]

/-! ## Invariance of the theta series -/

/-- The theta series as a function on the Siegel upper half-space. -/
noncomputable def thetaFun (L : Submodule ℤ E) : SiegelUpperHalfSpace n → ℂ :=
  fun Z => siegelTheta L Z.1

theorem slash_gJ {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L) {k : ℕ} (hk : finrank ℝ E = 2 * k) :
    slash (k : ℤ) (ofInt gJ) (thetaFun (n := n) L) = thetaFun L := by
  funext Z
  have hval : (ofInt (gJ (n := n))).1 = Matrix.J n ℝ :=
    Matrix.map_J (l := n) (R := ℤ) (Int.castRingHom ℝ)
  have hden : j (ofInt (gJ (n := n))).1 Z.1 = Z.1.det := by rw [j, hval, den_J]
  have hact : thetaFun L (ofInt (gJ (n := n)) • Z) = Z.1.det ^ k * siegelTheta L Z.1 := by
    change siegelTheta L (ofInt (gJ (n := n)) • Z).1 = _
    rw [smul_val, hval, siegelTheta_inversion_even hL hU hk Z.2]
  rw [slash_apply, hden, hact, _root_.zpow_neg, zpow_natCast, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero k (IsSiegel.det_ne_zero Z.2)), one_mul]
  rfl

theorem slash_gT {L : Submodule ℤ E} (hL : ZLattice.IsEven L) (k : ℤ) (S : Matrix n n ℤ)
    (hS : S.IsSymm) : slash k (ofInt (gT S hS)) (thetaFun (n := n) L) = thetaFun L := by
  funext Z
  have hden : den (ofInt (gT S hS)).1 Z.1 = 1 := by
    rw [gT, den_ofInt_fromBlocks]; simp
  have hnum : num (ofInt (gT S hS)).1 Z.1 = Z.1 + ci S := by
    rw [gT, num_ofInt_fromBlocks]; simp
  have hact : thetaFun L (ofInt (gT S hS) • Z) = siegelTheta L Z.1 := by
    change siegelTheta L (ofInt (gT S hS) • Z).1 = _
    rw [smul_val, act, hden, hnum, inv_one, Matrix.mul_one]
    exact siegelTheta_add_int hL Z.1 hS
  rw [slash_apply, j, hden, det_one, _root_.one_zpow, one_mul, hact]
  rfl

theorem slash_gU {L : Submodule ℤ E} {k : ℕ} (hk : Even k) (U V : Matrix n n ℤ)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    slash (k : ℤ) (ofInt (gU U V hVU)) (thetaFun (n := n) L) = thetaFun L := by
  funext Z
  have hden : den (ofInt (gU U V hVU)).1 Z.1 = (ci V)ᵀ := by
    rw [gU, den_ofInt_fromBlocks]; simp [ci_transpose]
  have hnum : num (ofInt (gU U V hVU)).1 Z.1 = ci U * Z.1 := by
    rw [gU, num_ofInt_fromBlocks]; simp
  have hinv : ((ci V)ᵀ)⁻¹ = (ci U)ᵀ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.transpose_mul, ← ci_mul, hVU, ci_one, transpose_one]
  have hact : thetaFun L (ofInt (gU U V hVU) • Z) = siegelTheta L Z.1 := by
    change siegelTheta L (ofInt (gU U V hVU) • Z).1 = _
    rw [smul_val, act, hden, hnum, hinv]
    exact siegelTheta_conj_int L hUV hVU Z.1
  have hj : j (ofInt (gU U V hVU)).1 Z.1 ^ k = 1 := by
    rw [j, hden, det_transpose, det_ci]
    have hunit : IsUnit V.det := IsUnit.of_mul_eq_one (b := U.det) (by rw [← det_mul, hVU, det_one])
    rcases Int.isUnit_iff.mp hunit with h | h
    · rw [h]; simp
    · rw [h]; simpa using hk.neg_one_pow
  rw [slash_apply, _root_.zpow_neg, zpow_natCast, hj, inv_one, one_mul, hact]
  rfl

/-- The theta series of an even unimodular lattice of rank `2k` is invariant under the weight
`k` slash action of every element of the subgroup generated by the standard generators. -/
theorem slash_thetaFun_of_mem {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L) {k : ℕ} (hk : finrank ℝ E = 2 * k)
    {γ : symplecticGroup n ℤ} (hγ : γ ∈ standardSubgroup n) :
    slash (k : ℤ) (ofInt γ) (thetaFun (n := n) L) = thetaFun L := by
  have heven : Even k := by
    obtain ⟨m, hm⟩ := hL.eight_dvd_finrank hU
    exact ⟨2 * m, by omega⟩
  induction hγ using Subgroup.closure_induction with
  | mem γ hγ =>
    rcases hγ with rfl | ⟨S, hS, rfl⟩ | ⟨U, V, hVU, hUV, rfl⟩
    · exact slash_gJ hL hU hk
    · exact slash_gT hL k S hS
    · exact slash_gU heven U V hUV hVU
  | one => rw [map_one, slash_one]
  | mul γ δ _ _ hγ hδ => rw [map_mul, slash_mul, hγ, hδ]
  | inv γ _ hγ =>
    have h : slash (k : ℤ) (ofInt γ⁻¹) (slash (k : ℤ) (ofInt γ) (thetaFun (n := n) L)) =
        thetaFun L := by
      rw [← slash_mul, ← map_mul, mul_inv_cancel, map_one, slash_one]
    rwa [hγ] at h

/-- **The theta series as a Siegel modular form**, conditional on the generation of
`Sp(2n, ℤ)` by the standard generators: for an even unimodular lattice `L` of rank `2k`,
`Z ↦ Θ_L(Z)` is a Siegel modular form of degree `n` and weight `k`. -/
noncomputable def thetaForm {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L) {k : ℕ} (hk : finrank ℝ E = 2 * k)
    (hgen : standardSubgroup n = ⊤) : SiegelModularForm n k where
  toFun := thetaFun L
  holo := isHolomorphic_siegelTheta L
  slash_eq γ := slash_thetaFun_of_mem hL hU hk (hgen ▸ Subgroup.mem_top γ)
  bdd := isBoundedAtInfinity_siegelTheta L

end TauTrack.Siegel
