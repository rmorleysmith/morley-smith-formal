module

public import TauTrack.LevelEleven.Basic
public import TauCeti.NumberTheory.ModularForms.LFunction.Sign
import Mathlib.Tactic

/-!
# The Fricke involution at level 11 and the functional equation of `L(f, s)`

Let `f(z) = η(z)² η(11z)² = ∑ a(n) qⁿ` (`eta11Form`, the newform of level 11 and weight 2).

**The Fricke relation** (`eta11_S_smul`). From `η(−1/u)² = −iu η(u)²` (TauCeti's
`eta_neg_one_div_sq`), applied at `u = w` and at `u = w/11`,

`f(−1/w) = −(w²/11) f(w/11)`.

**The Fricke eigenvalue** (`normalizedFrickeOperatorCusp_eta11Form₁`). Equivalently
`f(−1/(11z)) = −11 z² f(z)` (`eta11_frickeGL_smul`), so the normalized Fricke operator
`W₁₁ = (0 −1; 11 0)` acts on `f` by `−1`.

**The functional equation, root number `+1`.** TauCeti's functional equation for Fricke
eigenvectors gives, for the level-11 completed `L`-function
`Λ₁₁(s) = 11^{s/2} (2π)^{−s} Γ(s) L(f, s)`,

`Λ₁₁(2 − s) = Λ₁₁(s)`   (`frickeCompletedL_eta11_two_sub`),

the sign being `i² · (−1) = +1`. In Mathlib's normalisation `Λ(s) = (2π)^{−s} Γ(s) L(f, s)` this
reads `Λ(2 − s) = 11^{s−1} Λ(s)` (`Λ_eta11_two_sub` for the form on `Γ₁(11)`,
`Λ_eta11Form_two_sub` for the form on `Γ₀(11)`).

## References

* F. Diamond and J. Shurman, *A first course in modular forms*, Springer, 2005, Theorem 5.10.2
  (the functional equation of a Fricke eigenvector).
* LMFDB, newform 11.2.a.a: Fricke sign `−1`, sign of the functional equation `+1`.
-/

@[expose] public section

open Complex ModularGroup Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open TauCeti
open scoped MatrixGroups ModularForm Real

namespace TauTrack

/-! ## The Fricke relation -/

/-- `η(−1/u)² = −iu η(u)²`, on `ℍ`. -/
theorem etaSq_S_smul (u : ℍ) : etaSq (S • u) = -I * u * etaSq u := by
  rw [modular_S_smul]
  change ModularForm.eta ((-(u : ℂ))⁻¹) ^ 2 = -I * u * ModularForm.eta u ^ 2
  rw [show (-(u : ℂ))⁻¹ = -1 / u by field_simp,
    TauCeti.ModularForm.eta_neg_one_div_sq u.im_pos]

/-- `w ↦ w/11` on `ℍ`, as the action of `diag(11, 1)⁻¹`. -/
noncomputable def div11 (w : ℍ) : ℍ := (scaleGL 11)⁻¹ • w

theorem coe_div11 (w : ℍ) : (div11 w : ℂ) = w / 11 := by
  have h := coe_scaleGL_smul (d := 11) (div11 w)
  rw [div11, smul_inv_smul] at h
  rw [div11]
  conv_rhs => rw [h]
  push_cast
  ring

theorem im_div11 (w : ℍ) : (div11 w).im = w.im / 11 := by
  change (div11 w : ℂ).im = (w : ℂ).im / 11
  rw [coe_div11]
  simp

theorem re_div11 (w : ℍ) : (div11 w).re = w.re / 11 := by
  change (div11 w : ℂ).re = (w : ℂ).re / 11
  rw [coe_div11]
  simp

theorem scaleGL_smul_S_smul (w : ℍ) : scaleGL 11 • (S • w) = S • div11 w := by
  apply UpperHalfPlane.ext
  simp only [coe_scaleGL_smul, modular_S_smul, UpperHalfPlane.coe_mk]
  rw [coe_div11]
  have := w.ne_zero
  push_cast
  field_simp

theorem scaleGL_smul_div11 (w : ℍ) : scaleGL 11 • div11 w = w := smul_inv_smul _ _

/-- **The Fricke relation** for `f = η(z)²η(11z)²`: `f(−1/w) = −(w²/11) f(w/11)`. -/
theorem eta11_S_smul (w : ℍ) : eta11 (S • w) = -((w : ℂ) ^ 2 / 11) * eta11 (div11 w) := by
  rw [eta11, eta11, scaleGL_smul_S_smul, scaleGL_smul_div11, etaSq_S_smul, etaSq_S_smul,
    coe_div11]
  linear_combination ((w : ℂ) ^ 2 / 11 * etaSq w * etaSq (div11 w)) * Complex.I_sq

/-! ## The Fricke eigenvalue and the functional equation -/

/-- `f` as a cusp form for `Γ₁(11)`. -/
noncomputable def eta11Form₁ : CuspForm ((Gamma1 11).map (mapGL ℝ)) 2 :=
  CuspForm.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 11)) eta11Form

@[simp] theorem coe_eta11Form₁ : ⇑eta11Form₁ = eta11 := rfl

/-- `f(−1/(11z)) = −11 z² f(z)`. -/
theorem eta11_frickeGL_smul (z : ℍ) :
    eta11 (frickeGL ℝ 11 • z) = -(11 * (z : ℂ) ^ 2) * eta11 z := by
  rw [frickeGL_smul_eq_S_smul, eta11_S_smul]
  set w : ℍ := (⟨((11 : ℕ) : ℝ), Nat.cast_pos.mpr (NeZero.pos 11)⟩ : {r : ℝ // 0 < r}) • z
  have hw : (w : ℂ) = 11 * z := by
    simp only [w, coe_pos_real_smul, Complex.real_smul]
    push_cast
    ring
  have hd : div11 w = z := by
    apply UpperHalfPlane.ext
    rw [coe_div11, hw]
    ring
  rw [hd, hw]
  ring

/-- **`f ∣ W₁₁ = −f`**: the normalized Fricke operator acts on `f` by `−1`. -/
theorem normalizedFrickeOperatorCusp_eta11Form₁ :
    normalizedFrickeOperatorCusp 2 eta11Form₁ = (-1 : ℂ) • eta11Form₁ := by
  apply DFunLike.ext
  intro z
  rw [coe_normalizedFrickeOperatorCusp]
  have hdet : (0 : ℝ) < ((frickeGL ℝ 11).det : ℝ) := val_det_frickeGL_pos
  have hcoe : ⇑eta11Form₁ = eta11 := rfl
  have hσ : σ (frickeGL ℝ 11) = .refl ℝ ℂ := by simp only [σ, hdet, ↓reduceIte]
  have hden : denom (frickeGL ℝ 11) z = 11 * z := by simp [denom]
  have hN : atkinLehnerNormalizer 11 2 = 1 := by simp [atkinLehnerNormalizer_def]
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  rw [Pi.smul_apply, hN, one_smul, FunLike.coe_smul, Pi.smul_apply, hcoe, ModularForm.slash_apply,
    eta11_frickeGL_smul, hσ, hden, val_det_frickeGL]
  simp only [ContinuousAlgEquiv.refl_apply, smul_eq_mul]
  norm_num
  field_simp

/-- **The functional equation at level 11, root number `+1`**: `Λ₁₁(2 − s) = Λ₁₁(s)`. -/
theorem frickeCompletedL_eta11_two_sub (s : ℂ) :
    CuspForm.frickeCompletedL eta11Form₁ ((11 : ℕ).toPNat (NeZero.pos 11)) (2 - s) =
      CuspForm.frickeCompletedL eta11Form₁ ((11 : ℕ).toPNat (NeZero.pos 11)) s := by
  have h := CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul
    eta11Form₁ (by norm_num) normalizedFrickeOperatorCusp_eta11Form₁ s
  rw [show ((2 : ℤ) : ℂ) = 2 by norm_num] at h
  rw [h]
  simp [I_sq]

/-- **The functional equation in Mathlib's normalisation**: `Λ(2 − s) = 11^{s−1} Λ(s)`. -/
theorem Λ_eta11_two_sub (s : ℂ) :
    ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form₁ (2 - s) =
      (11 : ℂ) ^ (s - 1) * ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form₁ s := by
  have h := CuspForm.Λ_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul
    eta11Form₁ (by norm_num) normalizedFrickeOperatorCusp_eta11Form₁ s
  rw [show ((2 : ℤ) : ℂ) = 2 by norm_num] at h
  rw [h]
  norm_num [I_sq]

/-- Mathlib's completed `L`-function is the Mellin transform of `t ↦ f(it)`, so it is the same
for `f` on `Γ₁(11)` and on `Γ₀(11)`. -/
theorem Λ_eta11Form₁ :
    ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form₁ =
      ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form := by
  rw [CuspForm.Λ_eq_mellin, CuspForm.Λ_eq_mellin]
  rfl

/-- **The functional equation of `L(f, s)`** for `f` on `Γ₀(11)`, in Mathlib's normalisation:
`Λ(2 − s) = 11^{s−1} Λ(s)`. -/
theorem Λ_eta11Form_two_sub (s : ℂ) :
    ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form (2 - s) =
      (11 : ℂ) ^ (s - 1) * ModularForm.Λ (by norm_num : (0 : ℤ) < 2) eta11Form s := by
  rw [← Λ_eta11Form₁]
  exact Λ_eta11_two_sub s

end TauTrack
