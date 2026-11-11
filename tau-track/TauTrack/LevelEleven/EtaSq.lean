module

public import TauCeti.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The multiplier of `η²` on `SL(2, ℤ)`

`η²` is a weight-one form with a character: `η² ∣[1] γ = χ(γ) η²` for every `γ ∈ SL(2, ℤ)`, where
`χ(γ) = exp(2πi ψ(γ) / 12)` and `ψ(γ)` depends only on the entries of `γ` modulo 12 (`etaSqExponent`).
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups Real

namespace TauTrack

/-- The exponent `ψ` of the multiplier of `η²`, as a function of the entries modulo 12. -/
def etaSqExponent (a b c d : ZMod 12) : ZMod 12 :=
  if c.val % 2 = 1 then (a + d) * c - b * d * (c * c - 1) - 3 * c
  else (a + d) * c - b * d * (c * c - 1) + 3 * d - 3 - 3 * c * d

theorem etaSqExponent_T : ∀ a b c d : ZMod 12, a * d - b * c = 1 →
    etaSqExponent a (a + b) c (c + d) = etaSqExponent a b c d + 1 := by decide +kernel

theorem etaSqExponent_S : ∀ a b c d : ZMod 12, a * d - b * c = 1 →
    etaSqExponent b (-a) d (-c) = etaSqExponent a b c d - 3 := by decide +kernel

theorem etaSqExponent_conj : ∀ a b c d : ZMod 12, a * d - b * c = 1 →
    etaSqExponent a b c d + etaSqExponent a (-b) (-c) d = 0 := by decide +kernel

/-- `ψ(γ)` for `γ ∈ SL(2, ℤ)`. -/
def etaSqExp (γ : SL(2, ℤ)) : ZMod 12 :=
  etaSqExponent (γ 0 0 : ℤ) (γ 0 1 : ℤ) (γ 1 0 : ℤ) (γ 1 1 : ℤ)

/-- `η²` as a function on the upper half-plane. -/
noncomputable def etaSq (z : ℍ) : ℂ := η z ^ 2

theorem eta_add_one (z : ℂ) : η (z + 1) = cexp (2 * π * I / 24) * η z := by
  have h1 : Function.Periodic.qParam 24 (z + 1) =
      cexp (2 * π * I / 24) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : ∀ n, eta_q n (z + 1) = eta_q n z := by
    intro n
    simp only [eta_q_eq_cexp]
    rw [show 2 * π * I * (n + 1) * (z + 1) = 2 * π * I * (n + 1) * z + (n + 1 : ℕ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp only [ModularForm.eta, h1, h2]
  ring

theorem etaSq_slash_T : etaSq ∣[(1 : ℤ)] T = ZMod.stdAddChar (1 : ZMod 12) • etaSq := by
  ext z
  have h1 : ZMod.stdAddChar (1 : ZMod 12) = cexp (2 * π * I / 12) := by
    simpa using ZMod.stdAddChar_coe (N := 12) 1
  have hz : ((T • z : ℍ) : ℂ) = z + 1 := by
    rw [modular_T_smul]; simp [add_comm]
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, etaSq, etaSq, hz, eta_add_one, h1]
  have hd : denom T z = 1 := by
    rw [ModularGroup.denom_apply]; simp [ModularGroup.coe_T]
  rw [hd, mul_pow, ← Complex.exp_nat_mul]
  simp only [one_zpow, mul_one]
  congr 2
  push_cast
  ring

theorem etaSq_slash_S : etaSq ∣[(1 : ℤ)] S = ZMod.stdAddChar (-3 : ZMod 12) • etaSq := by
  ext z
  have h1 : ZMod.stdAddChar (-3 : ZMod 12) = -I := by
    have := ZMod.stdAddChar_coe (N := 12) (-3)
    push_cast at this
    rw [this, show 2 * (π : ℂ) * I * (-3) / 12 = -(π / 2 * I) by ring, Complex.exp_neg,
      Complex.exp_mul_I]
    simp
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  rw [SlashInvariantForm.slash_S_apply, Pi.smul_apply, smul_eq_mul, etaSq, etaSq, h1]
  have := TauCeti.ModularForm.eta_neg_one_div_sq z.im_pos
  change η ((-(z : ℂ))⁻¹) ^ 2 * _ = _
  rw [show (-(z : ℂ))⁻¹ = -1 / z by field_simp, this, zpow_neg, zpow_one]
  field_simp

theorem etaSqExp_mul_T (γ : SL(2, ℤ)) : etaSqExp (γ * T) = etaSqExp γ + 1 := by
  have hdet : ((γ 0 0 : ℤ) : ZMod 12) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 12) h
  have := etaSqExponent_T _ _ _ _ hdet
  simpa [etaSqExp, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two] using this

theorem etaSqExp_mul_S (γ : SL(2, ℤ)) : etaSqExp (γ * S) = etaSqExp γ - 3 := by
  have hdet : ((γ 0 0 : ℤ) : ZMod 12) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 12) h
  have := etaSqExponent_S _ _ _ _ hdet
  simpa [etaSqExp, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two] using this

/-- **The multiplier of `η²`.** For every `γ ∈ SL(2, ℤ)`,
`η² ∣[1] γ = exp(2πi ψ(γ)/12) η²`. -/
theorem etaSq_slash (γ : SL(2, ℤ)) :
    etaSq ∣[(1 : ℤ)] γ = ZMod.stdAddChar (etaSqExp γ) • etaSq := by
  have hγ : γ ∈ Subgroup.closure {S, T} := by simp [_root_.SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction_right with
  | one => simp [etaSqExp, etaSqExponent]
  | mul_right x hx y hy ih =>
    rcases hy with rfl | rfl
    · rw [SlashAction.slash_mul, ih, SL_smul_slash, etaSq_slash_S, smul_smul, etaSqExp_mul_S,
        sub_eq_add_neg, AddChar.map_add_eq_mul]
    · rw [SlashAction.slash_mul, ih, SL_smul_slash, etaSq_slash_T, smul_smul, etaSqExp_mul_T,
        AddChar.map_add_eq_mul]
  | mul_inv_cancel x hx y hy ih =>
    have key : ∀ (g : SL(2, ℤ)) (n : ZMod 12), etaSq ∣[(1 : ℤ)] g = ZMod.stdAddChar n • etaSq →
        etaSq ∣[(1 : ℤ)] g⁻¹ = ZMod.stdAddChar (-n) • etaSq := by
      intro g n hg
      have h := congrArg (fun f ↦ (ZMod.stdAddChar (-n) : ℂ) • (f ∣[(1 : ℤ)] g⁻¹)) hg
      simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, SL_smul_slash,
        smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        one_smul] at h
      exact h.symm
    rcases hy with rfl | rfl
    · have e : etaSqExp (x * S⁻¹) = etaSqExp x + 3 := by
        have := etaSqExp_mul_S (x * S⁻¹)
        rw [inv_mul_cancel_right] at this
        rw [this]; ring
      rw [SlashAction.slash_mul, ih, SL_smul_slash, key S _ etaSq_slash_S, smul_smul, e,
        neg_neg, AddChar.map_add_eq_mul]
    · have e : etaSqExp (x * T⁻¹) = etaSqExp x + -1 := by
        have := etaSqExp_mul_T (x * T⁻¹)
        rw [inv_mul_cancel_right] at this
        rw [this]; ring
      rw [SlashAction.slash_mul, ih, SL_smul_slash, key T _ etaSq_slash_T, smul_smul, e,
        AddChar.map_add_eq_mul]

end TauTrack
