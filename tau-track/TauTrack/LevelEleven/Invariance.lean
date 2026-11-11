module

public import TauTrack.LevelEleven.EtaSq
public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# `η(z)² η(11z)²` is invariant under `Γ₀(11)` in weight 2
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup TauCeti
open scoped MatrixGroups Real

namespace TauTrack

/-- `f₁₁(z) = η(z)² η(11z)²`. -/
noncomputable def eta11 (z : ℍ) : ℂ := etaSq z * etaSq (scaleGL 11 • z)

theorem etaSq_smul (γ : SL(2, ℤ)) (z : ℍ) :
    etaSq (γ • z) = ZMod.stdAddChar (etaSqExp γ) * etaSq z * denom γ z := by
  have h := congrFun (etaSq_slash γ) z
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_one] at h
  have hd : denom γ z ≠ 0 := denom_ne_zero _ z
  field_simp at h
  linear_combination h

theorem etaSqExp_conjScale (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = (11 : ℕ) * c) :
    etaSqExp γ + etaSqExp (conjScale 11 γ c hc) = 0 := by
  have hdet : ((γ 0 0 : ℤ) : ZMod 12) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 12) h
  have h := etaSqExponent_conj _ _ _ _ hdet
  have h11 : ((11 : ℤ) : ZMod 12) = -1 := by decide
  have hc' : ((c : ℤ) : ZMod 12) = -((γ 1 0 : ℤ) : ZMod 12) := by
    rw [hc]; push_cast; rw [show (11 : ZMod 12) = -1 by decide]; ring
  simp only [etaSqExp, coe_conjScale, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [hc', show (11 : ZMod 12) = -1 by decide, neg_one_mul]
  exact h

theorem eta11_slash (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 11) : eta11 ∣[(2 : ℤ)] γ = eta11 := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, γ 1 0 = (11 : ℕ) * c := by
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
    exact ⟨c, by simpa using hc⟩
  ext z
  have hconj : (scaleGL 11 • (γ • z) : ℍ) = conjScale 11 γ c hc • (scaleGL 11 • z : ℍ) := by
    rw [sl_moeb, sl_moeb, ← mul_smul, ← mul_smul]
    congr 1
    have := mapGL_conjScale (d := 11) γ c hc
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hden : denom (conjScale 11 γ c hc) ((scaleGL 11 • z : ℍ) : ℂ) = denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, coe_scaleGL_smul]
    have : ((γ 1 0 : ℤ) : ℂ) = 11 * (c : ℂ) := by rw [hc]; push_cast; ring
    simp [this]
    ring
  have hχ : (ZMod.stdAddChar (etaSqExp γ) : ℂ) * ZMod.stdAddChar (etaSqExp (conjScale 11 γ c hc))
      = 1 := by
    rw [← AddChar.map_add_eq_mul, etaSqExp_conjScale, AddChar.map_zero_eq_one]
  have hd : denom γ z ≠ 0 := denom_ne_zero _ z
  rw [SL_slash_apply, eta11, eta11, hconj, etaSq_smul, etaSq_smul, hden, zpow_neg]
  field_simp
  linear_combination (etaSq z * etaSq (scaleGL 11 • z)) * hχ

end TauTrack
