module

public import TauTrack.LevelEleven.QExpansion
public import TauCeti.NumberTheory.ModularForms.SturmBound
public import TauCeti.NumberTheory.ModularForms.Norm.Trace
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# `S₂(Γ₀(11))` is spanned by `η(z)² η(11z)²`
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup TauCeti Filter
  Function
open scoped MatrixGroups Real Pointwise Topology

namespace TauTrack

theorem card_quotient_Γ₁₁ : Nat.card (𝒮ℒ ⧸ Γ₁₁.subgroupOf 𝒮ℒ) = 12 := by
  rw [← Subgroup.index_eq_card, ← Subgroup.relIndex,
    MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ), ← Subgroup.relIndex_comap,
    Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right, Gamma0_prime_index 11 (by decide)]

theorem integerCuspWidth_Γ₁₁ : Subgroup.integerCuspWidth Γ₁₁ = 1 :=
  le_antisymm (Subgroup.integerCuspWidth_le one_pos (by simp))
    Subgroup.integerCuspWidth_pos

theorem isZeroAtImInfty_quotientFunc (g : CuspForm Γ₁₁ 2) (q : 𝒮ℒ ⧸ Γ₁₁.subgroupOf 𝒮ℒ) :
    IsZeroAtImInfty (SlashInvariantForm.quotientFunc g q) := by
  have hc : IsCusp OnePoint.infty (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.isCusp_of_mem_strictPeriods one_pos (by simp)
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨r, hr⟩ := r
    exact OnePoint.isZeroAt_infty_iff.mp <|
      (CuspForm.translate g _).zero_at_cusps' (hc.of_isFiniteRelIndex_conj hr)

/-- **A cusp form of weight 2 and level 11 whose coefficient of `q` vanishes is zero.** Its norm
to level one has weight 24 and vanishes to order at least 3 at `∞`: order 2 from the form itself and
at least 1 more from the other eleven coset translates, each of which vanishes at `∞`. -/
theorem cuspForm_eq_zero_of_coeff_one (g : CuspForm Γ₁₁ 2) (h1 : (qExpansion 1 g).coeff 1 = 0) :
    g = 0 := by
  classical
  let G : ModularForm Γ₁₁ 2 := CuspForm.toModularFormₗ g
  have hG : ⇑G = ⇑g := rfl
  let _ : Fintype (𝒮ℒ ⧸ Γ₁₁.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  -- the remaining factor of the norm vanishes at `∞`
  have hrest : IsZeroAtImInfty (TauCeti.ModularForm.normRest G) := by
    rw [TauCeti.ModularForm.normRest_def]
    set s := Finset.univ.filter (· ∉ Finset.univ.image
        fun j : Fin (Subgroup.integerCuspWidth Γ₁₁) ↦
          (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)) ^ (j : ℕ))⟧ :
            𝒮ℒ ⧸ (Γ₁₁.subgroupOf 𝒮ℒ))) with hs
    have hne : s.Nonempty := by
      rw [← Finset.card_pos, hs, Finset.filter_not, Finset.card_sdiff_of_subset
        (Finset.filter_subset _ _)]
      have h12 : (Finset.univ : Finset (𝒮ℒ ⧸ Γ₁₁.subgroupOf 𝒮ℒ)).card = 12 := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_quotient_Γ₁₁]
      have hle : (Finset.univ.filter (· ∈ Finset.univ.image
          fun j : Fin (Subgroup.integerCuspWidth Γ₁₁) ↦
            (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)) ^ (j : ℕ))⟧ :
              𝒮ℒ ⧸ (Γ₁₁.subgroupOf 𝒮ℒ)))).card ≤ 1 := by
        refine (Finset.card_le_card fun x hx ↦ (Finset.mem_filter.mp hx).2).trans ?_
        refine Finset.card_image_le.trans ?_
        simp [integerCuspWidth_Γ₁₁]
      rw [h12]
      exact Nat.sub_pos_of_lt (lt_of_le_of_lt (by convert hle) (by norm_num))
    have h := tendsto_finsetProd s fun q _ ↦ isZeroAtImInfty_quotientFunc g q
    rw [Finset.prod_const, zero_pow (Finset.card_ne_zero.mpr hne)] at h
    refine Tendsto.congr (fun z ↦ ?_) h
    rw [Finset.prod_apply]
    rfl
  -- orders of vanishing
  have hG0 : (qExpansion 1 G).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero g zero_lt_one one_mem_strictPeriods_Γ₁₁
  have hordG : (2 : ℕ∞) ≤ (qExpansion 1 G).order := by
    refine PowerSeries.nat_le_order _ _ fun i hi ↦ ?_
    interval_cases i
    · exact hG0
    · exact h1
  have hordR : (1 : ℕ∞) ≤ (qExpansion 1 (TauCeti.ModularForm.normRest G)).order := by
    refine PowerSeries.nat_le_order _ 1 fun i hi ↦ ?_
    interval_cases i
    rw [UpperHalfPlane.qExpansion_coeff]
    simp [hrest.cuspFunction_apply_zero zero_lt_one]
  have hord := TauCeti.ModularForm.qExpansion_one_norm_order_eq G
  rw [integerCuspWidth_Γ₁₁, Nat.cast_one] at hord
  have h3 : (3 : ℕ∞) ≤ (qExpansion 1 (ModularForm.norm 𝒮ℒ G)).order := by
    rw [hord]
    exact (by norm_num : (3 : ℕ∞) = 2 + 1) ▸ add_le_add hordG hordR
  have hN : ModularForm.norm 𝒮ℒ G = 0 := by
    refine sturm_bound_levelOne (lt_of_lt_of_le ?_ h3)
    rw [card_quotient_Γ₁₁]
    norm_num
  have hG' : G = 0 := by
    rw [← FunLike.coe_zero_iff, ← ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ)]
    exact hN
  ext z
  simpa [hG] using congrArg (fun F : ModularForm Γ₁₁ 2 ↦ F z) hG'

/-- **`S₂(Γ₀(11))` is spanned by `η(z)² η(11z)²`**: every cusp form of weight 2 and level 11 is
its coefficient of `q` times that form. -/
theorem cuspForm_eq_coeff_one_smul (g : CuspForm Γ₁₁ 2) :
    g = (qExpansion 1 g).coeff 1 • eta11Form := by
  let L := CuspForm.qExpansionCoeffₗ (Γ := Γ₁₁) zero_lt_one one_mem_strictPeriods_Γ₁₁ 2 1
  have hL : ∀ f : CuspForm Γ₁₁ 2, L f = (qExpansion 1 f).coeff 1 := fun f ↦
    CuspForm.qExpansionCoeffₗ_apply _ _ _ _
  rw [← sub_eq_zero]
  apply cuspForm_eq_zero_of_coeff_one
  rw [← hL, map_sub, map_smul, hL, hL, eta11Form_coeff_one]
  simp

theorem eta11Form_ne_zero : eta11Form ≠ 0 := by
  intro h
  have := eta11Form_coeff_one
  rw [h] at this
  simp [UpperHalfPlane.qExpansion_zero] at this

/-- The space of cusp forms of weight 2 and level 11 has dimension 1. -/
theorem finrank_cuspForm_Γ₁₁ : Module.finrank ℂ (CuspForm Γ₁₁ 2) = 1 :=
  finrank_eq_one_iff_of_ne_zero' eta11Form eta11Form_ne_zero |>.mpr fun g ↦
    ⟨_, (cuspForm_eq_coeff_one_smul g).symm⟩

/-- **Determination at the Sturm bound.** A modular form of weight 2 and level 11 whose
`q`-expansion agrees with that of `η(z)² η(11z)²` up to `q²` is equal to it. -/
theorem eq_eta11Form_of_coeff (g : ModularForm Γ₁₁ 2)
    (h : ∀ i ≤ 2, (qExpansion 1 g).coeff i = (qExpansion 1 eta11Form).coeff i) :
    g = CuspForm.toModularFormₗ eta11Form := by
  have hw : Γ₁₁.strictWidthInfty = 1 := CongruenceSubgroup.strictWidthInfty_Gamma0 11
  refine ModularForm.eq_of_sturm_bound g _ fun i hi ↦ ?_
  rw [card_quotient_Γ₁₁] at hi
  rw [hw]
  exact h i (by simpa using hi)

end TauTrack
