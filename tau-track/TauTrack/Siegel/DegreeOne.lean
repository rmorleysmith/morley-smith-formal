module

public import TauTrack.Siegel.Form

/-!
# Degree one: Siegel modular forms are modular forms

For `n = 1` the Siegel upper half-space is the upper half-plane, `Sp(2, ℤ) = SL(2, ℤ)`, and
`det (C Z + D) = c z + d`. A Siegel modular form of degree one and weight `k` is the same thing
as a modular form of level one and weight `k` in Mathlib's sense.

* `toSiegel`, `ofSiegel`: the identification of `ℍ` with `ℍ_1`.
* `spOf`: `SL(2, ℤ) → Sp(2, ℤ)`, and `exists_spOf`: it is onto.
* `toSiegel_smul`, `j_spOf`: the two actions and the two automorphy factors agree.
* `exists_modularForm`, `exists_siegelModularForm`: the two notions of modular form agree.
-/

@[expose] public section

open Matrix Complex UpperHalfPlane ModularForm
open scoped MatrixGroups ComplexOrder Manifold

namespace TauTrack.Siegel.DegreeOne

/-! ## One by one matrices -/

/-- The `1 × 1` matrix with entry `a`. -/
def m1 {α : Type*} (a : α) : Matrix (Fin 1) (Fin 1) α := Matrix.of fun _ _ => a

@[simp] theorem m1_apply {α : Type*} (a : α) (i j : Fin 1) : m1 a i j = a := rfl

theorem eq_m1 {α : Type*} (A : Matrix (Fin 1) (Fin 1) α) : A = m1 (A 0 0) := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  rfl

theorem m1_injective {α : Type*} {a b : α} (h : m1 a = m1 b) : a = b := by
  simpa using congrFun (congrFun h 0) 0

@[simp] theorem m1_mul {α : Type*} [NonUnitalNonAssocSemiring α] (a b : α) :
    m1 a * m1 b = m1 (a * b) := by
  ext i j; simp [Matrix.mul_apply]

@[simp] theorem m1_add {α : Type*} [Add α] (a b : α) : m1 a + m1 b = m1 (a + b) := by
  ext i j; simp

@[simp] theorem m1_sub {α : Type*} [Sub α] (a b : α) : m1 a - m1 b = m1 (a - b) := by
  ext i j; simp

@[simp] theorem m1_transpose {α : Type*} (a : α) : (m1 a)ᵀ = m1 a := by
  ext i j; simp

theorem m1_one {α : Type*} [Zero α] [One α] : (1 : Matrix (Fin 1) (Fin 1) α) = m1 1 := by
  ext i j
  rw [Subsingleton.elim i j]
  simp

@[simp] theorem m1_map {α β : Type*} (f : α → β) (a : α) : (m1 a).map f = m1 (f a) := rfl

@[simp] theorem cx_m1 (a : ℝ) : cx (m1 a) = m1 (a : ℂ) := rfl

@[simp] theorem det_m1 {α : Type*} [CommRing α] (a : α) : (m1 a).det = a := by
  simp [det_unique]

theorem m1_inv {w : ℂ} (hw : w ≠ 0) : (m1 w)⁻¹ = m1 w⁻¹ := by
  apply inv_eq_right_inv
  rw [m1_mul, mul_inv_cancel₀ hw, m1_one]

theorem posDef_m1 {r : ℝ} : (m1 r).PosDef ↔ 0 < r := by
  have h : m1 r = diagonal fun _ => r := by
    ext i j
    rw [Subsingleton.elim i j]
    simp
  rw [h, posDef_diagonal_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem posSemidef_m1 {r : ℝ} : (m1 r).PosSemidef ↔ 0 ≤ r := by
  have h : m1 r = diagonal fun _ => r := by
    ext i j
    rw [Subsingleton.elim i j]
    simp
  rw [h, posSemidef_diagonal_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-! ## Points -/

/-- A point of the upper half-plane as a point of `ℍ_1`. -/
def toSiegel (z : ℍ) : SiegelUpperHalfSpace (Fin 1) :=
  ⟨m1 (z : ℂ), m1_transpose _, by rw [m1_map]; exact posDef_m1.mpr z.im_pos⟩

/-- A point of `ℍ_1` as a point of the upper half-plane. -/
def ofSiegel (Z : SiegelUpperHalfSpace (Fin 1)) : ℍ :=
  ⟨Z.1 0 0, by
    have h := Z.2.2
    rw [eq_m1 Z.1, m1_map, posDef_m1] at h
    exact h⟩

@[simp] theorem toSiegel_val (z : ℍ) : (toSiegel z).1 = m1 (z : ℂ) := rfl

@[simp] theorem ofSiegel_toSiegel (z : ℍ) : ofSiegel (toSiegel z) = z := rfl

@[simp] theorem toSiegel_ofSiegel (Z : SiegelUpperHalfSpace (Fin 1)) :
    toSiegel (ofSiegel Z) = Z :=
  Subtype.ext (eq_m1 Z.1).symm

/-! ## The groups -/

/-- `SL(2, ℤ) → Sp(2, ℤ)`. -/
def spOf (γ : SL(2, ℤ)) : symplecticGroup (Fin 1) ℤ :=
  ⟨fromBlocks (m1 (γ 0 0)) (m1 (γ 0 1)) (m1 (γ 1 0)) (m1 (γ 1 1)), by
    have hdet : γ 0 0 * γ 1 1 - γ 1 0 * γ 0 1 = 1 := by
      have := γ.det_coe
      rw [det_fin_two] at this
      linarith
    refine SymplecticGroup.fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [hdet, m1_one]⟩

/-- Every element of `Sp(2, ℤ)` comes from `SL(2, ℤ)`. -/
theorem exists_spOf (M : symplecticGroup (Fin 1) ℤ) : ∃ γ : SL(2, ℤ), spOf γ = M := by
  have hM : fromBlocks M.1.toBlocks₁₁ M.1.toBlocks₁₂ M.1.toBlocks₂₁ M.1.toBlocks₂₂ ∈
      symplecticGroup (Fin 1) ℤ := by rw [fromBlocks_toBlocks]; exact M.2
  obtain ⟨-, -, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.mp hM
  rw [eq_m1 M.1.toBlocks₁₁, eq_m1 M.1.toBlocks₁₂, eq_m1 M.1.toBlocks₂₁, eq_m1 M.1.toBlocks₂₂,
    m1_transpose, m1_transpose, m1_mul, m1_mul, m1_sub, m1_one] at r3
  have hdet := m1_injective r3
  refine ⟨⟨!![M.1.toBlocks₁₁ 0 0, M.1.toBlocks₁₂ 0 0; M.1.toBlocks₂₁ 0 0, M.1.toBlocks₂₂ 0 0],
    by rw [det_fin_two_of]; linarith⟩, ?_⟩
  apply Subtype.ext
  simp only [spOf]
  conv_rhs => rw [← fromBlocks_toBlocks M.1]
  rw [eq_m1 M.1.toBlocks₁₁, eq_m1 M.1.toBlocks₁₂, eq_m1 M.1.toBlocks₂₁, eq_m1 M.1.toBlocks₂₂]
  simp

theorem ofInt_spOf_val (γ : SL(2, ℤ)) : (ofInt (spOf γ)).1 =
    fromBlocks (m1 (γ 0 0 : ℝ)) (m1 (γ 0 1 : ℝ)) (m1 (γ 1 0 : ℝ)) (m1 (γ 1 1 : ℝ)) := by
  simp [ofInt, spOf, fromBlocks_map]

theorem num_spOf (γ : SL(2, ℤ)) (w : ℂ) :
    num (ofInt (spOf γ)).1 (m1 w) = m1 ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) := by
  simp [num, ofInt_spOf_val]

theorem den_spOf (γ : SL(2, ℤ)) (w : ℂ) :
    den (ofInt (spOf γ)).1 (m1 w) = m1 ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) := by
  simp [den, ofInt_spOf_val]

/-- The automorphy factors agree: `det (C Z + D) = c z + d`. -/
theorem j_spOf (γ : SL(2, ℤ)) (z : ℍ) : j (ofInt (spOf γ)).1 (toSiegel z).1 = denom γ z := by
  rw [j, toSiegel_val, den_spOf, det_m1, ModularGroup.denom_apply]

/-- The actions agree. -/
theorem toSiegel_smul (γ : SL(2, ℤ)) (z : ℍ) : ofInt (spOf γ) • toSiegel z = toSiegel (γ • z) := by
  apply Subtype.ext
  have hden : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    have h := j_ne_zero (ofInt (spOf γ)).2 (toSiegel z).2
    rwa [j, toSiegel_val, den_spOf, det_m1] at h
  rw [smul_val, toSiegel_val, act, num_spOf, den_spOf, m1_inv hden, m1_mul, toSiegel_val,
    coe_specialLinearGroup_apply]
  simp [div_eq_mul_inv]

/-! ## Holomorphy and boundedness in degree one -/

theorem smul_m1 (c a : ℝ) : c • m1 a = m1 (c * a) := by
  ext i j; simp

theorem mem_domain_iff {X : Fin 1 → Fin 1 → ℂ} : X ∈ domain (Fin 1) ↔ 0 < (X 0 0).im := by
  have hX : Matrix.of X = m1 (X 0 0) := eq_m1 (Matrix.of X)
  have hs : symPart (Matrix.of X) = m1 (X 0 0) := by
    rw [hX]; exact symPart_of_isSymm (m1_transpose _)
  change IsSiegel (symPart (Matrix.of X)) ↔ _
  rw [hs]
  exact ⟨fun h => posDef_m1.mp (by simpa using h.2), fun h => ⟨m1_transpose _, by
    rw [m1_map]; exact posDef_m1.mpr h⟩⟩

/-- On its domain, the extension of `F` is `F` at the point `X 0 0` of the upper half-plane. -/
theorem extend_eq (F : SiegelUpperHalfSpace (Fin 1) → ℂ) {X : Fin 1 → Fin 1 → ℂ}
    (hX : X ∈ domain (Fin 1)) : extend F X = F (toSiegel (ofComplex (X 0 0))) := by
  rw [extend_apply hX]
  congr 1
  apply Subtype.ext
  have hX' : Matrix.of X = m1 (X 0 0) := eq_m1 (Matrix.of X)
  rw [toSiegel_val, ofComplex_apply_of_im_pos (mem_domain_iff.mp hX)]
  change symPart (Matrix.of X) = m1 (X 0 0)
  rw [hX']
  exact symPart_of_isSymm (m1_transpose _)

theorem psd_iff (Z : SiegelUpperHalfSpace (Fin 1)) (c : ℝ) :
    (Z.1.map Complex.im - c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ↔ c ≤ (ofSiegel Z).im := by
  have h : Z.1.map Complex.im - c • (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      m1 ((ofSiegel Z).im - c) := by
    conv_lhs => rw [eq_m1 Z.1, m1_map, m1_one, smul_m1, m1_sub, mul_one]
    rfl
  rw [h, posSemidef_m1, sub_nonneg]

/-! ## The two notions of modular form agree -/

/-- A Siegel modular form of degree one is a modular form of level one. -/
theorem exists_modularForm {k : ℤ} (F : SiegelModularForm (Fin 1) k) :
    ∃ f : ModularForm 𝒮ℒ k, ∀ z : ℍ, f z = F (toSiegel z) := by
  have hslash : ∀ γ : SL(2, ℤ), (fun z : ℍ => F (toSiegel z)) ∣[k] γ = fun z => F (toSiegel z) := by
    intro γ
    funext z
    rw [SL_slash_apply, ← toSiegel_smul, F.map_smul, j_spOf, mul_right_comm,
      ← zpow_add₀ (denom_ne_zero γ z)]
    simp
  refine ⟨{ toFun := fun z => F (toSiegel z)
            slash_action_eq' := ?_
            holo' := ?_
            bdd_at_cusps' := ?_ }, fun z => rfl⟩
  · rintro g ⟨γ, rfl⟩
    exact hslash γ
  · rw [UpperHalfPlane.mdifferentiable_iff]
    have hL : Differentiable ℂ (fun w : ℂ => (fun _ _ => w : Fin 1 → Fin 1 → ℂ)) := by
      fun_prop
    have hmaps : Set.MapsTo (fun w : ℂ => (fun _ _ => w : Fin 1 → Fin 1 → ℂ)) {z | 0 < z.im}
        (domain (Fin 1)) := fun w hw => mem_domain_iff.mpr hw
    refine (F.holo.comp hL.differentiableOn hmaps).congr fun w hw => ?_
    simp only [Function.comp_apply]
    rw [extend_eq F.toFun (hmaps hw)]
    rfl
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hslash γ, isBoundedAtImInfty_iff]
    obtain ⟨c', B, h⟩ := F.bdd
    exact ⟨B, c', fun z hz => h (toSiegel z) ((psd_iff _ _).mpr hz)⟩

/-- A modular form of level one is a Siegel modular form of degree one. -/
theorem exists_siegelModularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ∃ F : SiegelModularForm (Fin 1) k, ∀ z : ℍ, F (toSiegel z) = f z := by
  refine ⟨{ toFun := fun Z => f (ofSiegel Z)
            holo := ?_
            slash_eq := ?_
            bdd := ?_ }, fun z => rfl⟩
  · have hf := UpperHalfPlane.mdifferentiable_iff.mp f.holo'
    have hP : Differentiable ℂ (fun X : Fin 1 → Fin 1 → ℂ => X 0 0) := by fun_prop
    have hmaps : Set.MapsTo (fun X : Fin 1 → Fin 1 → ℂ => X 0 0) (domain (Fin 1))
        {z | 0 < z.im} := fun X hX => mem_domain_iff.mp hX
    refine (hf.comp hP.differentiableOn hmaps).congr fun X hX => ?_
    rw [extend_eq _ hX]
    rfl
  · intro M
    obtain ⟨γ, rfl⟩ := exists_spOf M
    funext Z
    have hZ : Z = toSiegel (ofSiegel Z) := (toSiegel_ofSiegel Z).symm
    have h : (f.toFun ∣[k] γ) (ofSiegel Z) = f.toFun (ofSiegel Z) :=
      congrFun (f.slash_action_eq' _ ⟨γ, rfl⟩) (ofSiegel Z)
    rw [SL_slash_apply] at h
    rw [slash_apply]
    conv_lhs => rw [hZ, toSiegel_smul, j_spOf, ofSiegel_toSiegel]
    rw [mul_comm]
    exact h
  · obtain ⟨B, A, h⟩ := isBoundedAtImInfty_iff.mp (ModularFormClass.bdd_at_infty f)
    exact ⟨A, B, fun Z hZ => h (ofSiegel Z) ((psd_iff _ _).mp hZ)⟩

end TauTrack.Siegel.DegreeOne
