module

public import TauTrack.Siegel.Generation
public import TauTrack.Siegel.ThetaForm
public import TauTrack.Siegel.GradedRing
public import TauTrack.Siegel.Examples

/-!
# The theta series of an even unimodular lattice is a Siegel modular form

With the generation theorem `standardSubgroup_eq_top` the hypothesis of `thetaForm` is removed:
for an even unimodular lattice `L` of rank `2k` and every degree `n`, the theta series

  `Θ_L(Z) = ∑_{x ∈ Lⁿ} exp(π i · tr(G(x) Z))`

is a Siegel modular form of degree `n` and weight `k`.

* `thetaModularForm hL hU hk : SiegelModularForm n k`, with `thetaModularForm_apply`.
* `siegelTheta_smul`: the transformation law `Θ_L(γ·Z) = det(CZ + D)^k · Θ_L(Z)` for every
  `γ ∈ Sp(2n, ℤ)`.
* `thetaE8 n : SiegelModularForm n 4`: the theta series of the `E₈` lattice in degree `n`.
-/

@[expose] public noncomputable section

open Matrix Complex Module

namespace TauTrack.Siegel

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- **The theta series of an even unimodular lattice of rank `2k` is a Siegel modular form of
weight `k`, in every degree `n`.** -/
def thetaModularForm (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) : SiegelModularForm n k :=
  thetaForm hL hU hk (standardSubgroup_eq_top n)

@[simp] theorem thetaModularForm_apply (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) (Z : SiegelUpperHalfSpace n) :
    thetaModularForm hL hU hk Z = siegelTheta L Z.1 := rfl

/-- The transformation law of the theta series under the whole of `Sp(2n, ℤ)`:
`Θ_L(γ·Z) = det(CZ + D)^k · Θ_L(Z)`. -/
theorem siegelTheta_smul (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L)
    (hk : finrank ℝ E = 2 * k) (γ : symplecticGroup n ℤ) (Z : SiegelUpperHalfSpace n) :
    siegelTheta L (ofInt γ • Z).1 = j (ofInt γ).1 Z.1 ^ (k : ℤ) * siegelTheta L Z.1 :=
  (thetaModularForm hL hU hk).map_smul γ Z

open TauCeti.IntegralLattice in
/-- The theta series of the `E₈` lattice in degree `n`, a Siegel modular form of weight `4`. -/
def thetaE8 (n : Type*) [Fintype n] [DecidableEq n] : SiegelModularForm n ((4 : ℕ) : ℤ) :=
  thetaModularForm (k := 4)
    ((typeE₈RootLattice.isEven_realModel_iff _).mpr isEven_typeE₈RootLattice)
    ((typeE₈RootLattice.isUnimodular_realModel_iff isPosDef_typeE₈RootLattice).mpr
      isUnimodular_typeE₈RootLattice)
    (by simp [RealModelSpace.finrank_eq, finrank_carrier])

open TauCeti.IntegralLattice in
/-- In degree two, on the diagonal, the `E₈` theta series is `E₄(τ₁) · E₄(τ₂)`. -/
theorem thetaE8_diag (τ₁ τ₂ : UpperHalfPlane) (Z : SiegelUpperHalfSpace (Fin 1 ⊕ Fin 1))
    (hZ : Z.1 = Matrix.fromBlocks (DegreeOne.m1 (τ₁ : ℂ)) 0 0 (DegreeOne.m1 (τ₂ : ℂ))) :
    thetaE8 (Fin 1 ⊕ Fin 1) Z = ModularForm.E₄ τ₁ * ModularForm.E₄ τ₂ := by
  change siegelTheta _ Z.1 = _
  rw [hZ, siegelTheta_E8_diag]

end TauTrack.Siegel
