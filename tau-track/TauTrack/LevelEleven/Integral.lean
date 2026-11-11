module

public import TauTrack.LevelEleven.QExpansion
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The `q`-expansion of `η(z)² η(11z)²` as an integer power series
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex TauCeti Filter Function PowerSeries
open scoped MatrixGroups Real Pointwise Topology

namespace TauTrack

/-- The integer power series `A` represents the function `F` on the open unit disc. -/
def Rep (A : ℤ⟦X⟧) (F : ℂ → ℂ) : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → Summable (fun n ↦ ‖(A.coeff n : ℂ) * q ^ n‖) ∧
    ∑' n, (A.coeff n : ℂ) * q ^ n = F q

theorem Rep.mul {A B : ℤ⟦X⟧} {F G : ℂ → ℂ} (hA : Rep A F) (hB : Rep B G) :
    Rep (A * B) (fun q ↦ F q * G q) := by
  intro q hq
  obtain ⟨sA, eA⟩ := hA q hq
  obtain ⟨sB, eB⟩ := hB q hq
  have key : ∀ n, ((A * B).coeff n : ℂ) * q ^ n = ∑ kl ∈ Finset.antidiagonal n,
      ((A.coeff kl.1 : ℂ) * q ^ kl.1) * ((B.coeff kl.2 : ℂ) * q ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [key] using summable_norm_sum_mul_antidiagonal_of_summable_norm sA sB
  · simp only [key]
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sA sB, eA, eB]

theorem Rep.var : Rep (PowerSeries.X : ℤ⟦X⟧) (fun q ↦ q) := by
  intro q hq
  have h : ∀ n, (((PowerSeries.X : ℤ⟦X⟧).coeff n : ℤ) : ℂ) * q ^ n = if n = 1 then q else 0 := by
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs with h <;> simp [h]
  simp only [h]
  refine ⟨?_, by simp⟩
  exact summable_of_ne_finset_zero (s := {1}) fun n hn ↦ by
    rw [Finset.mem_singleton] at hn
    simp [hn]

theorem Rep.expand {A : ℤ⟦X⟧} {F : ℂ → ℂ} (hA : Rep A F) :
    Rep (PowerSeries.expand 11 (by norm_num) A) (fun q ↦ F (q ^ 11)) := by
  intro q hq
  have hq11 : ‖q ^ 11‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  obtain ⟨sA, eA⟩ := hA (q ^ 11) hq11
  have hinj : Injective (fun m : ℕ ↦ 11 * m) := fun a b h ↦ by simpa using h
  have hcomp : ∀ m : ℕ, ((PowerSeries.expand 11 (by norm_num) A).coeff (11 * m) : ℂ) * q ^ (11 * m)
      = (A.coeff m : ℂ) * (q ^ 11) ^ m := by
    intro m
    rw [PowerSeries.coeff_expand_mul, pow_mul]
  have hzero : ∀ n ∉ Set.range (fun m : ℕ ↦ 11 * m),
      ((PowerSeries.expand 11 (by norm_num) A).coeff n : ℂ) * q ^ n = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand_of_not_dvd, Int.cast_zero, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (fun n hn ↦ by rw [hzero n hn, norm_zero])]
    simpa only [comp_def, hcomp] using sA
  · rw [← hinj.tsum_eq (fun n hn ↦ by
      by_contra h; exact hn (hzero n h))]
    simp only [hcomp]
    exact eA

theorem coeff_pentagonalSeries_cast (n : ℕ) :
    (((pentagonalSeries ℤ).coeff n : ℤ) : ℂ) = (pentagonalSeries ℂ).coeff n := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp
  · simp [coeff_pentagonalSeries_eq_zero _ hn]

theorem Rep.euler : Rep (pentagonalSeries ℤ) (fun q ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) := by
  intro q hq
  simp only [coeff_pentagonalSeries_cast]
  refine ⟨?_, ?_⟩
  · refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      rw [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
      simp
    · simp [coeff_pentagonalSeries_eq_zero ℂ hn]
  · rw [← eulerFunction_eq_tprod hq, eulerFunction_def]

/-- The integer power series `q ∏ (1 - qⁿ)² (1 - q¹¹ⁿ)²`. -/
noncomputable def eta11Series : ℤ⟦X⟧ :=
  PowerSeries.X * (pentagonalSeries ℤ * pentagonalSeries ℤ *
    (PowerSeries.expand 11 (by norm_num) (pentagonalSeries ℤ) *
      PowerSeries.expand 11 (by norm_num) (pentagonalSeries ℤ)))

theorem rep_eta11Series : Rep eta11Series (fun q ↦ q *
    ((∏' n : ℕ, (1 - q ^ (n + 1))) * (∏' n : ℕ, (1 - q ^ (n + 1))) *
      ((∏' n : ℕ, (1 - (q ^ 11) ^ (n + 1))) * (∏' n : ℕ, (1 - (q ^ 11) ^ (n + 1))))) ) :=
  Rep.var.mul ((Rep.euler.mul Rep.euler).mul (Rep.euler.expand.mul Rep.euler.expand))

/-- **The `q`-expansion of `η(z)² η(11z)²` has integer coefficients**, those of the power series
`q ∏ (1 - qⁿ)² (1 - q¹¹ⁿ)²`. -/
theorem eta11Form_coeff (n : ℕ) :
    (qExpansion 1 eta11Form).coeff n = (eta11Series.coeff n : ℂ) := by
  symm
  refine UpperHalfPlane.qExpansion_coeff_unique (f := eta11Form)
    (c := fun n ↦ (eta11Series.coeff n : ℂ)) zero_lt_one
    (ModularFormClass.analyticAt_cuspFunction_zero eta11Form zero_lt_one
      one_mem_strictPeriods_Γ₁₁) (fun τ ↦ ?_) n
  have hq : ‖Periodic.qParam 1 (τ : ℂ)‖ < 1 := Periodic.norm_qParam_lt_one zero_lt_one τ.im_pos
  obtain ⟨hs, he⟩ := rep_eta11Series _ hq
  have : eta11Form τ = Periodic.qParam 1 (τ : ℂ) *
      ((∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) *
        (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) *
      ((∏' n : ℕ, (1 - (Periodic.qParam 1 (τ : ℂ) ^ 11) ^ (n + 1))) *
        (∏' n : ℕ, (1 - (Periodic.qParam 1 (τ : ℂ) ^ 11) ^ (n + 1))))) := by
    change eta11 τ = _
    rw [eta11_eq]; ring
  beta_reduce at he
  rw [this, ← he]
  simpa only [smul_eq_mul] using hs.of_norm.hasSum

end TauTrack
