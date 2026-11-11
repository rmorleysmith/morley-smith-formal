module

public import TauTrack.LevelEleven.Invariance
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# `η(z)² η(11z)²` as a cusp form of weight 2 and level 11
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup TauCeti
open scoped MatrixGroups Real Pointwise

namespace TauTrack

/-- `Γ₀(11)` inside `GL(2, ℝ)`. -/
abbrev Γ₁₁ : Subgroup (GL (Fin 2) ℝ) := (Gamma0 11).map (mapGL ℝ)

theorem Γ₁₁_le : Γ₁₁ ≤ ConjAct.toConjAct (scaleGL 11)⁻¹ • 𝒮ℒ := by
  simpa [Gamma0_one_top, ← MonoidHom.range_eq_map] using Gamma0_map_le_conjAct_scaleGL 1 11

/-- `Δ(11z)` as a cusp form of weight 12 and level 11. -/
noncomputable def discriminant11 : CuspForm Γ₁₁ 12 :=
  TauCeti.CuspForm.levelRaise 11 Γ₁₁_le CuspForm.discriminant

theorem eta11_pow_twelve (z : ℍ) : eta11 z ^ 12 = discriminant z * discriminant11 z := by
  rw [discriminant11, TauCeti.CuspForm.levelRaise_apply, CuspForm.coe_discriminant]
  simp only [eta11, etaSq, discriminant]
  ring

theorem eta11_slash_pow_twelve (γ : SL(2, ℤ)) (z : ℍ) :
    (eta11 ∣[(2 : ℤ)] γ) z ^ 12 = discriminant z * (⇑discriminant11 ∣[(12 : ℤ)] γ) z := by
  have hΔ : (discriminant ∣[(12 : ℤ)] γ) z = discriminant z := by
    rw [SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant
      discriminant_T_invariant]
  rw [← hΔ, SL_slash_apply, SL_slash_apply, SL_slash_apply, mul_pow, eta11_pow_twelve]
  have hd : denom γ z ≠ 0 := denom_ne_zero _ z
  rw [← zpow_natCast (denom γ z ^ (-2 : ℤ)), ← zpow_mul]
  rw [show ((-2 : ℤ) * (12 : ℕ)) = -12 + -12 by norm_num, zpow_add₀ hd]
  ring

/-- **The level-11 newform as a cusp form**: `η(z)² η(11z)²` is a cusp form of weight 2 for
`Γ₀(11)`. -/
noncomputable def eta11Form : CuspForm Γ₁₁ 2 where
  toFun := eta11
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    exact eta11_slash γ hγ
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have h11 : ∀ z : ℂ, z ∈ upperHalfPlaneSet → (11 * z) ∈ upperHalfPlaneSet := by
      intro z hz
      simpa [upperHalfPlaneSet] using hz
    refine DifferentiableOn.congr (f := fun z : ℂ ↦ η z ^ 2 * η (11 * z) ^ 2)
      (fun z hz ↦ ?_) fun z hz ↦ ?_
    · exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 2).mul
        (((differentiableAt_eta_of_mem_upperHalfPlaneSet (h11 z hz)).comp z
          (by fun_prop)).pow 2)).differentiableWithinAt
    · simp [eta11, etaSq, ofComplex_apply_of_im_pos hz]
  zero_at_cusps' {c} hc := by
    have hc' := hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ hγ
    have h1 : IsZeroAtImInfty (⇑discriminant11 ∣[(12 : ℤ)] γ) :=
      (OnePoint.isZeroAt_iff_forall_SL2Z hc).mp (discriminant11.zero_at_cusps' hc') γ hγ
    have h2 : IsZeroAtImInfty (fun z ↦ (eta11 ∣[(2 : ℤ)] γ) z ^ 12) := by
      have h3 : IsZeroAtImInfty (fun z ↦ discriminant z * (⇑discriminant11 ∣[(12 : ℤ)] γ) z) := by
        have h := Filter.Tendsto.mul discriminant_isZeroAtImInfty h1
        rw [mul_zero] at h
        exact h
      simpa [eta11_slash_pow_twelve] using h3
    rw [isZeroAtImInfty_iff] at h2 ⊢
    intro ε hε
    obtain ⟨A, hA⟩ := h2 (ε ^ 12) (by positivity)
    refine ⟨A, fun z hz ↦ ?_⟩
    have := hA z hz
    rw [norm_pow] at this
    exact le_of_pow_le_pow_left₀ (by norm_num) hε.le this

@[simp] theorem coe_eta11Form : ⇑eta11Form = eta11 := rfl

end TauTrack
