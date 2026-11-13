module

public import TauTrack.Siegel.DegreeOne
public import TauTrack.Siegel.Theta
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.E8

/-!
# First examples of Siegel modular forms (degree one)

Through the degree-one comparison (`DegreeOne.exists_siegelModularForm`), every level-one modular
form is a Siegel modular form of degree one. In particular the theta series of an even
unimodular lattice of rank `2k` is a Siegel modular form of degree one and weight `k`.
-/

@[expose] public section

open Module UpperHalfPlane
open scoped MatrixGroups

namespace TauTrack.Siegel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- The theta series of an even unimodular lattice of rank `2k` is a Siegel modular form of
degree one and weight `k`. -/
theorem exists_theta_degreeOne (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) :
    ∃ F : SiegelModularForm (Fin 1) k,
      ∀ z : ℍ, F (DegreeOne.toSiegel z) = ZLattice.thetaSeries L z := by
  obtain ⟨F, hF⟩ := DegreeOne.exists_siegelModularForm (ZLattice.thetaForm hL hU hk)
  exact ⟨F, fun z => by rw [hF z, ZLattice.coe_thetaForm]⟩

open TauCeti.IntegralLattice in
/-- **The E₈ theta series of degree two on the diagonal.** At `Z = diag(τ₁, τ₂)` the degree-two
theta series of the E₈ lattice is `E₄(τ₁) · E₄(τ₂)`. -/
theorem siegelTheta_E8_diag (τ₁ τ₂ : ℍ) :
    siegelTheta (typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice)
        (Matrix.fromBlocks (DegreeOne.m1 (τ₁ : ℂ)) 0 0 (DegreeOne.m1 (τ₂ : ℂ))) =
      ModularForm.E₄ τ₁ * ModularForm.E₄ τ₂ := by
  rw [siegelTheta_fromBlocks _ (by rw [DegreeOne.m1_map]; exact DegreeOne.posDef_m1.mpr τ₁.im_pos)
    (by rw [DegreeOne.m1_map]; exact DegreeOne.posDef_m1.mpr τ₂.im_pos),
    siegelTheta_m1, siegelTheta_m1, thetaSeries_realModel_typeE₈RootLattice]

end TauTrack.Siegel
