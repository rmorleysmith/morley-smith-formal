module

public import TauTrack.LevelEleven.CuspForm
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
# The leading coefficient of `η(z)² η(11z)²`
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup TauCeti Filter
  Function
open scoped MatrixGroups Real Pointwise Topology

namespace TauTrack

theorem one_mem_strictPeriods_Γ₁₁ : (1 : ℝ) ∈ Γ₁₁.strictPeriods := by
  have h := Subgroup.strictWidthInfty_mem_strictPeriods (𝒢 := Γ₁₁)
  rwa [show Γ₁₁.strictWidthInfty = 1 from CongruenceSubgroup.strictWidthInfty_Gamma0 11] at h

theorem tendsto_tprod_one_sub_pow :
    Tendsto (fun q : ℂ ↦ ∏' (n : ℕ), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
  have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
    (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
  simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
  simp_rw [sub_eq_add_neg]
  refine this
    (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
    (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by simp : (0 : ℝ) < 1 / 2)] with q hq k
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _

theorem eta11_eq (z : ℍ) : eta11 z = Periodic.qParam 1 z *
    ((∏' (n : ℕ), (1 - Periodic.qParam 1 z ^ (n + 1))) ^ 2 *
      (∏' (n : ℕ), (1 - (Periodic.qParam 1 z ^ 11) ^ (n + 1))) ^ 2) := by
  have h1 : Periodic.qParam 24 (z : ℂ) ^ 2 * Periodic.qParam 24 (11 * (z : ℂ)) ^ 2 =
      Periodic.qParam 1 z := by
    simp only [Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : ∀ n : ℕ, eta_q n (z : ℂ) = Periodic.qParam 1 z ^ (n + 1) := fun n ↦ rfl
  have h3 : ∀ n : ℕ, eta_q n (11 * (z : ℂ)) = (Periodic.qParam 1 z ^ 11) ^ (n + 1) := by
    intro n
    simp only [eta_q, Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e : eta11 z = (Periodic.qParam 24 (z : ℂ) ^ 2 * Periodic.qParam 24 (11 * (z : ℂ)) ^ 2) *
      ((∏' (n : ℕ), (1 - eta_q n (z : ℂ))) ^ 2 *
        (∏' (n : ℕ), (1 - eta_q n (11 * (z : ℂ)))) ^ 2) := by
    simp only [eta11, etaSq, ModularForm.eta, coe_scaleGL_smul]
    push_cast
    ring
  rw [e, h1]
  simp only [h2, h3]

theorem tendsto_eta11_div_qParam :
    Tendsto (fun z : ℍ ↦ eta11 z / Periodic.qParam 1 z) atImInfty (𝓝 1) := by
  have hq : Tendsto (fun z : ℍ ↦ Periodic.qParam 1 (z : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one
  have hq11 : Tendsto (fun z : ℍ ↦ Periodic.qParam 1 (z : ℂ) ^ 11) atImInfty (𝓝 0) := by
    simpa using hq.pow 11
  have h := ((tendsto_tprod_one_sub_pow.comp hq).pow 2).mul
    ((tendsto_tprod_one_sub_pow.comp hq11).pow 2)
  simp only [one_pow, mul_one] at h
  refine h.congr fun z ↦ ?_
  rw [eta11_eq, mul_div_cancel_left₀ _ (Periodic.qParam_ne_zero _)]
  rfl

/-- The coefficient of `q` in `η(z)² η(11z)²` is `1`. -/
theorem eta11Form_coeff_one : (qExpansion 1 eta11Form).coeff 1 = 1 := by
  have h := UpperHalfPlane.tendsto_div_qParam_atImInfty (f := eta11Form) zero_lt_one
    (SlashInvariantFormClass.periodic_comp_ofComplex (k := 2) eta11Form one_mem_strictPeriods_Γ₁₁)
    (ModularFormClass.analyticAt_cuspFunction_zero eta11Form zero_lt_one
      one_mem_strictPeriods_Γ₁₁).differentiableAt
    (CuspFormClass.qExpansion_coeff_zero eta11Form zero_lt_one one_mem_strictPeriods_Γ₁₁)
  exact tendsto_nhds_unique h tendsto_eta11_div_qParam

end TauTrack
