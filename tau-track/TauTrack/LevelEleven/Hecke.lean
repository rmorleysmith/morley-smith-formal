module

public import TauTrack.LevelEleven.Dimension
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# `η(z)² η(11z)²` is a Hecke eigenform
-/

@[expose] public section

open UpperHalfPlane hiding I
open ModularForm Complex Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup TauCeti Filter
  Function HeckeRing.GL2
open scoped MatrixGroups Real Pointwise Topology

namespace TauTrack

/-- The Hecke operator `Tₙ` on `S₂(Γ₀(11))`. -/
noncomputable def hecke11 (n : ℕ) : Module.End ℂ (CuspForm Γ₁₁ 2) :=
  (cuspFormCharSpaceOneEquiv 11 2).conj
    (heckeRingHomCuspCharSpace 2 (1 : (ZMod 11)ˣ →* ℂˣ) (heckeTCompositeGamma0 11 n))

/-- The trivial Dirichlet character modulo 11 at a natural number. -/
theorem trivChar_apply (d : ℕ) :
    (MulChar.ofUnitHom (1 : (ZMod 11)ˣ →* ℂˣ) : DirichletCharacter ℂ 11) d =
      if 11 ∣ d then 0 else 1 := by
  have h1 : MulChar.ofUnitHom (1 : (ZMod 11)ˣ →* ℂˣ) = 1 := by
    ext a; simp
  rw [h1]
  have hcop : IsUnit (d : ZMod 11) ↔ ¬ 11 ∣ d := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 11)]
  split_ifs with h
  · exact MulChar.map_nonunit _ (fun hu ↦ hcop.mp hu h)
  · exact MulChar.one_apply (hcop.mpr h)

/-- The coefficients of `q`-expansions of cusp forms of level 11, written `a m g`. -/
noncomputable abbrev coeff11 (g : CuspForm Γ₁₁ 2) (m : ℕ) : ℂ := (qExpansion 1 g).coeff m

/-- **The coefficient formula for `Tₙ` on `S₂(Γ₀(11))`**:
`a_m(Tₙ g) = ∑_{d ∣ (m, n), 11 ∤ d} d · a_{mn/d²}(g)`. -/
theorem coeff_hecke11 {n : ℕ} (hn : n ≠ 0) (g : CuspForm Γ₁₁ 2) (m : ℕ) :
    coeff11 (hecke11 n g) m = ∑ d ∈ (Nat.gcd m n).divisors,
      (if 11 ∣ d then 0 else (d : ℂ)) * coeff11 g (m * n / d ^ 2) := by
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 (N := 11) (k := 2)
    (χ := 1) hn ((cuspFormCharSpaceOneEquiv 11 2).symm g) m
  have e1 : ⇑(hecke11 n g) = ⇑((heckeRingHomCuspCharSpace 2 (1 : (ZMod 11)ˣ →* ℂˣ)
      (heckeTCompositeGamma0 11 n) ((cuspFormCharSpaceOneEquiv 11 2).symm g) :
        cuspFormCharSpace 2 (1 : (ZMod 11)ˣ →* ℂˣ)) :
        CuspForm ((Gamma1 11).map (mapGL ℝ)) 2) :=
    coe_cuspFormCharSpaceOneEquiv_apply _
  have e2 : ⇑(((cuspFormCharSpaceOneEquiv 11 2).symm g :
      cuspFormCharSpace 2 (1 : (ZMod 11)ˣ →* ℂˣ)) : CuspForm ((Gamma1 11).map (mapGL ℝ)) 2) = ⇑g := by
    rw [coe_cuspFormCharSpaceOneEquiv_symm_apply]
    rfl
  rw [coeff11, e1, h]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [trivChar_apply, e2]
  split_ifs <;> simp

/-- **`η(z)² η(11z)²` is an eigenform of every `Tₙ`**, with eigenvalue its `n`-th coefficient. -/
theorem hecke11_eta11Form {n : ℕ} (hn : n ≠ 0) :
    hecke11 n eta11Form = coeff11 eta11Form n • eta11Form := by
  rw [cuspForm_eq_coeff_one_smul (hecke11 n eta11Form)]
  congr 1
  have := coeff_hecke11 hn eta11Form 1
  simpa [coeff11] using this

/-- **The product formula for the coefficients of the level-11 newform**:
`a_m a_n = ∑_{d ∣ (m, n), 11 ∤ d} d · a_{mn/d²}`. -/
theorem coeff11_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    coeff11 eta11Form m * coeff11 eta11Form n = ∑ d ∈ (Nat.gcd m n).divisors,
      (if 11 ∣ d then 0 else (d : ℂ)) * coeff11 eta11Form (m * n / d ^ 2) := by
  rw [← coeff_hecke11 hn, hecke11_eta11Form hn]
  let L := CuspForm.qExpansionCoeffₗ (Γ := Γ₁₁) zero_lt_one one_mem_strictPeriods_Γ₁₁ 2 m
  have hL : ∀ f : CuspForm Γ₁₁ 2, L f = coeff11 f m := fun f ↦
    CuspForm.qExpansionCoeffₗ_apply _ _ _ _
  rw [← hL, ← hL, map_smul, smul_eq_mul, mul_comm]

end TauTrack
