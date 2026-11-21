module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Data.ZMod.Basic
public import TauTrack.Tones.Pitch
public import TauTrack.LevelEleven.Invariance
import Mathlib.Tactic

/-!
# Solution: the twelve characters of the modular group

The statements of `Challenge.lean`, proved from `TauTrack.Tones.EtaCharacter` (the character of
`η²` and the classification of characters) and `TauTrack.LevelEleven.EtaSq` (the explicit exponent
`etaSqExp` of the multiplier, with `η² ∣[1] γ = e^{2πi ψ(γ)/12} η²`).
-/

@[expose] public section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups Real

namespace Tones

open TauTrack TauTrack.Tones

theorem character_determined {G : Type*} [CommGroup G] (χ : SL(2, ℤ) →* G) :
    χ S = (χ T ^ 3)⁻¹ ∧ χ T ^ 12 = 1 ∧ ∀ χ' : SL(2, ℤ) →* G, χ' T = χ T → χ' = χ :=
  ⟨char_S χ, char_T_pow_twelve χ, fun _ h ↦ char_ext h⟩

/-- The two descriptions of the multiplier agree: `etaChar γ = e^{2πi ψ(γ)/12}`. -/
theorem etaChar_eq_stdAddChar (γ : SL(2, ℤ)) : etaChar γ = ZMod.stdAddChar (etaSqExp γ) :=
  smul_etaSq_inj ((TauTrack.Tones.etaSq_slash γ).symm.trans (TauTrack.etaSq_slash γ))

theorem etaSqExp_mul (γ δ : SL(2, ℤ)) : etaSqExp (γ * δ) = etaSqExp γ + etaSqExp δ := by
  apply ZMod.injective_stdAddChar
  rw [AddChar.map_add_eq_mul, ← etaChar_eq_stdAddChar, ← etaChar_eq_stdAddChar,
    ← etaChar_eq_stdAddChar, map_mul]

theorem stdAddChar_eq_exp (x : ZMod 12) :
    ZMod.stdAddChar x = Complex.exp (2 * π * Complex.I * ((x.val : ℕ) : ℂ) / 12) := by
  have h := ZMod.stdAddChar_coe (N := 12) (x.val : ℤ)
  rw [show ((x.val : ℤ) : ZMod 12) = x by simp] at h
  rw [h]
  push_cast
  rfl

theorem odd_iff_val (n : ℤ) : ((n : ZMod 12).val % 2 = 1) ↔ Odd n := by
  have h : (((n : ZMod 12).val : ℕ) : ℤ) = n % 12 := ZMod.val_intCast n
  rw [Int.odd_iff]
  omega

theorem exists_pitch.{u} :
    ∃ p : SL(2, ℤ) → ZMod 12,
      (∀ γ δ, p (γ * δ) = p γ + p δ) ∧ p T = 1 ∧ p S = 9 ∧ p (-1) = 6 ∧
      (∀ (G : Type u) [CommGroup G] (χ : SL(2, ℤ) →* G) (γ : SL(2, ℤ)), χ γ = χ T ^ (p γ).val) ∧
      (∀ (γ : SL(2, ℤ)) (a b c d : ZMod 12),
        a = ((γ 0 0 : ℤ) : ZMod 12) → b = ((γ 0 1 : ℤ) : ZMod 12) →
        c = ((γ 1 0 : ℤ) : ZMod 12) → d = ((γ 1 1 : ℤ) : ZMod 12) →
        p γ = if Odd (γ 1 0) then (a + d) * c - b * d * (c * c - 1) - 3 * c
          else (a + d) * c - b * d * (c * c - 1) + 3 * d - 3 - 3 * c * d) ∧
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), ModularForm.eta ↑(γ • τ) ^ 2 =
        Complex.exp (2 * π * Complex.I * ((p γ).val : ℂ) / 12) *
          (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * ModularForm.eta ↑τ ^ 2) ∧
      ∀ χ : SL(2, ℤ) →* ℂˣ, ∃! k : ZMod 12,
        ∀ γ, (χ γ : ℂ) = Complex.exp (2 * π * Complex.I * (((k * p γ).val : ℕ) : ℂ) / 12) := by
  have hT : etaSqExp T = 1 := by
    have h := etaSqExp_mul_T 1
    rw [one_mul] at h
    rw [h]
    simp [etaSqExp, etaSqExponent]
  have hS : etaSqExp S = 9 := by
    have h := etaSqExp_mul_S 1
    rw [one_mul] at h
    rw [h]
    simp [etaSqExp, etaSqExponent]
    decide
  refine ⟨etaSqExp, etaSqExp_mul, hT, hS, ?_, ?_, ?_, ?_, ?_⟩
  · -- `p(−1) = p(S) + p(S) = 18 = 6`
    rw [← TauTrack.Tones.S_mul_S, etaSqExp_mul, hS]
    decide
  · -- `γ ↦ χ(T)^{p(γ)}` is a homomorphism agreeing with `χ` at `T`
    intro G _ χ γ
    have h12 := char_T_pow_twelve χ
    let χ' : SL(2, ℤ) →* G :=
      { toFun := fun δ ↦ χ T ^ (etaSqExp δ).val
        map_one' := by
          have h0 : etaSqExp 1 = 0 := by simp [etaSqExp, etaSqExponent]
          simp [h0]
        map_mul' := fun δ ε ↦ by
          rw [etaSqExp_mul, ZMod.val_add, ← pow_add]
          exact (pow_eq_pow_mod _ h12).symm }
    have hval : (1 : ZMod 12).val = 1 := by decide
    have hχ : χ = χ' := char_ext (by simp [χ', hT, hval])
    exact congrArg (fun f : SL(2, ℤ) →* G ↦ f γ) hχ
  · rintro γ a b c d rfl rfl rfl rfl
    rw [etaSqExp, etaSqExponent]
    simp only [odd_iff_val]
  · intro γ τ
    have h := TauTrack.etaSq_smul γ τ
    rw [TauTrack.etaSq, TauTrack.etaSq, stdAddChar_eq_exp, ModularGroup.denom_apply] at h
    rw [h]
    ring
  · intro χ
    obtain ⟨k₀, -, hk₀⟩ := exists_eq_pow χ
    have key : ∀ (k : ZMod 12) (γ : SL(2, ℤ)),
        Complex.exp (2 * π * Complex.I * (((k * etaSqExp γ).val : ℕ) : ℂ) / 12) =
          ZMod.stdAddChar (k * etaSqExp γ) := fun k γ ↦ (stdAddChar_eq_exp _).symm
    refine ⟨(k₀ : ZMod 12), fun γ ↦ ?_, fun k hk ↦ ?_⟩
    · rw [key, hk₀, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_etaCharUnits,
        etaChar_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    · have h1 := hk T
      have h2 : (χ T : ℂ) = ZMod.stdAddChar ((k₀ : ZMod 12) * etaSqExp T) := by
        rw [hk₀, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_etaCharUnits,
          etaChar_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
      rw [key, h2, hT, mul_one, mul_one] at h1
      exact (ZMod.injective_stdAddChar h1).symm

end Tones
