module

public import Mathlib

/-!
# The Siegel upper half-space and the symplectic action

`ℍ_n` is the set of symmetric complex `n × n` matrices `Z` whose imaginary part is positive
definite. A real symplectic matrix `M = (A B; C D)` acts by `Z ↦ (A Z + B)(C Z + D)⁻¹`.

* `isUnit_den`: `C Z + D` is invertible.
* `isSiegel_act`: `(A Z + B)(C Z + D)⁻¹` is again in `ℍ_n`.
* `den_mul`, `act_mul`: the cocycle relation and the action law.
-/

@[expose] public section

open Matrix Complex
open scoped ComplexOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Algebra with complex blocks -/

/-- The Hermitian imaginary part `(Z − Zᴴ) / 2i`. -/
noncomputable def imH (Z : Matrix n n ℂ) : Matrix n n ℂ := (-(I / 2)) • (Z - Zᴴ)

/-- `(cZ + d)ᴴ (aZ + b) − (aZ + b)ᴴ (cZ + d) = Z − Zᴴ` for a block matrix `(a b; c d)` that
preserves the Hermitian symplectic form. -/
theorem key_conjTranspose (a b c d Z : Matrix n n ℂ) (h1 : aᴴ * c = cᴴ * a)
    (h2 : bᴴ * d = dᴴ * b) (h3 : aᴴ * d - cᴴ * b = 1) :
    (c * Z + d)ᴴ * (a * Z + b) - (a * Z + b)ᴴ * (c * Z + d) = Z - Zᴴ := by
  have h3' : dᴴ * a - bᴴ * c = 1 := by
    simpa [conjTranspose_sub, conjTranspose_mul] using congrArg conjTranspose h3
  calc (c * Z + d)ᴴ * (a * Z + b) - (a * Z + b)ᴴ * (c * Z + d)
      = Zᴴ * (cᴴ * a - aᴴ * c) * Z - Zᴴ * (aᴴ * d - cᴴ * b) + (dᴴ * a - bᴴ * c) * Z
          - (bᴴ * d - dᴴ * b) := by
        simp only [conjTranspose_add, conjTranspose_mul]; noncomm_ring
    _ = Z - Zᴴ := by rw [h3, h3', h1, h2]; simp; abel

/-- The transpose version: `(cZ + d)ᵀ (aZ + b) = (aZ + b)ᵀ (cZ + d)` for symmetric `Z`. -/
theorem key_transpose (a b c d Z : Matrix n n ℂ) (h1 : aᵀ * c = cᵀ * a)
    (h2 : bᵀ * d = dᵀ * b) (h3 : aᵀ * d - cᵀ * b = 1) (hZ : Zᵀ = Z) :
    (c * Z + d)ᵀ * (a * Z + b) = (a * Z + b)ᵀ * (c * Z + d) := by
  have h3' : dᵀ * a - bᵀ * c = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg transpose h3
  rw [← sub_eq_zero]
  calc (c * Z + d)ᵀ * (a * Z + b) - (a * Z + b)ᵀ * (c * Z + d)
      = Zᵀ * (cᵀ * a - aᵀ * c) * Z - Zᵀ * (aᵀ * d - cᵀ * b) + (dᵀ * a - bᵀ * c) * Z
          - (bᵀ * d - dᵀ * b) := by
        simp only [transpose_add, transpose_mul]; noncomm_ring
    _ = 0 := by rw [h3, h3', h1, h2, hZ]; simp

/-- `cZ + d` is invertible when the Hermitian imaginary part of `Z` is positive definite. -/
theorem isUnit_den_aux (a b c d Z : Matrix n n ℂ) (h1 : aᴴ * c = cᴴ * a)
    (h2 : bᴴ * d = dᴴ * b) (h3 : aᴴ * d - cᴴ * b = 1) (hZ : (imH Z).PosDef) :
    IsUnit (c * Z + d) := by
  rw [← mulVec_injective_iff_isUnit]
  suffices H : ∀ v, (c * Z + d) *ᵥ v = 0 → v = 0 by
    intro v w h
    exact sub_eq_zero.mp (H (v - w) (by rw [mulVec_sub, h, sub_self]))
  intro v hv
  by_contra hne
  have hpos := hZ.dotProduct_mulVec_pos hne
  have hkey := key_conjTranspose a b c d Z h1 h2 h3
  have h0 : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← hkey, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hv,
      dotProduct_mulVec, vecMul_conjTranspose, star_star, hv]
    simp
  rw [imH, smul_mulVec, dotProduct_smul, h0] at hpos
  simp at hpos

/-- The Hermitian imaginary part of `(aZ + b)(cZ + d)⁻¹`. -/
theorem imH_act_aux (a b c d Z : Matrix n n ℂ) (h1 : aᴴ * c = cᴴ * a)
    (h2 : bᴴ * d = dᴴ * b) (h3 : aᴴ * d - cᴴ * b = 1) (hQ : IsUnit (c * Z + d)) :
    imH ((a * Z + b) * (c * Z + d)⁻¹) = (c * Z + d)⁻¹ᴴ * imH Z * (c * Z + d)⁻¹ := by
  have hkey := key_conjTranspose a b c d Z h1 h2 h3
  have hdet : IsUnit (c * Z + d).det := (isUnit_iff_isUnit_det _).mp hQ
  have e1 : (c * Z + d)⁻¹ᴴ * (c * Z + d)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ hdet, conjTranspose_one]
  have e2 : (c * Z + d) * (c * Z + d)⁻¹ = 1 := mul_nonsing_inv _ hdet
  simp only [imH, ← hkey, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc (a * Z + b) * (c * Z + d)⁻¹ - (c * Z + d)⁻¹ᴴ * (a * Z + b)ᴴ
      = ((c * Z + d)⁻¹ᴴ * (c * Z + d)ᴴ) * (a * Z + b) * (c * Z + d)⁻¹
          - (c * Z + d)⁻¹ᴴ * (a * Z + b)ᴴ * ((c * Z + d) * (c * Z + d)⁻¹) := by
        rw [e1, e2]; simp
    _ = _ := by noncomm_ring

/-! ## Real matrices inside complex matrices -/

/-- A real matrix as a complex matrix. -/
noncomputable def cx (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

theorem cx_eq (A : Matrix n n ℝ) : cx A = Complex.ofRealHom.mapMatrix A := rfl

theorem cx_mul (A B : Matrix n n ℝ) : cx (A * B) = cx A * cx B := by simp [cx_eq]

theorem cx_add (A B : Matrix n n ℝ) : cx (A + B) = cx A + cx B := by ext i j; simp [cx]

theorem cx_sub (A B : Matrix n n ℝ) : cx (A - B) = cx A - cx B := by ext i j; simp [cx]

@[simp] theorem cx_one : cx (1 : Matrix n n ℝ) = 1 := by simp [cx_eq]

@[simp] theorem cx_zero : cx (0 : Matrix n n ℝ) = 0 := by simp [cx_eq]

theorem cx_transpose (A : Matrix n n ℝ) : cx Aᵀ = (cx A)ᵀ := by
  ext i j; simp [cx]

theorem cx_conjTranspose (A : Matrix n n ℝ) : (cx A)ᴴ = (cx A)ᵀ := by
  ext i j; simp [cx]

theorem cx_injective : Function.Injective (cx : Matrix n n ℝ → Matrix n n ℂ) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  simpa [cx] using this

theorem dotProduct_cx_mulVec (Y : Matrix n n ℝ) (p q : n → ℝ) :
    (fun i => (p i : ℂ)) ⬝ᵥ (cx Y *ᵥ fun i => (q i : ℂ)) = ((p ⬝ᵥ Y *ᵥ q : ℝ) : ℂ) := by
  simp [dotProduct, mulVec, cx]

/-- A real matrix is positive definite exactly when it is so as a complex matrix. -/
theorem posDef_cx_iff (Y : Matrix n n ℝ) : (cx Y).PosDef ↔ Y.PosDef := by
  constructor
  · intro h
    have hY : Yᵀ = Y := by
      apply cx_injective
      have := h.isHermitian
      rw [IsHermitian, cx_conjTranspose] at this
      rw [cx_transpose, this]
    refine PosDef.of_dotProduct_mulVec_pos (by simpa [IsHermitian] using hY) fun u hu => ?_
    have hx : (fun i => (u i : ℂ)) ≠ 0 := by
      intro h0
      apply hu
      ext i
      simpa using congrFun h0 i
    have := h.dotProduct_mulVec_pos hx
    have hs : star (fun i => (u i : ℂ)) = fun i => (u i : ℂ) := by ext i; simp
    rw [hs, dotProduct_cx_mulVec] at this
    simpa using this
  · intro h
    have hY : Yᵀ = Y := by simpa [IsHermitian] using h.isHermitian
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [IsHermitian, cx_conjTranspose, ← cx_transpose, hY]
    set u : n → ℝ := fun i => (x i).re with hu
    set w : n → ℝ := fun i => (x i).im with hw
    have hx' : x = (fun i => (u i : ℂ)) + I • fun i => (w i : ℂ) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, w]
      rw [mul_comm]
      exact (Complex.re_add_im (x i)).symm
    have hs : star x = (fun i => (u i : ℂ)) - I • fun i => (w i : ℂ) := by
      ext i
      apply Complex.ext <;> simp [u, w]
    have hsym : u ⬝ᵥ Y *ᵥ w = w ⬝ᵥ Y *ᵥ u := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hY, dotProduct_comm]
    have hval : star x ⬝ᵥ (cx Y *ᵥ x) = ((u ⬝ᵥ Y *ᵥ u + w ⬝ᵥ Y *ᵥ w : ℝ) : ℂ) := by
      rw [hs, hx']
      simp only [mulVec_add, mulVec_smul, dotProduct_add, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, dotProduct_cx_mulVec, hsym, smul_eq_mul]
      push_cast
      linear_combination (-((w ⬝ᵥ Y *ᵥ w : ℝ) : ℂ)) * Complex.I_mul_I
    rw [hval]
    have hne : u ≠ 0 ∨ w ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      apply hx
      ext i
      apply Complex.ext
      · simpa [u] using congrFun hcon.1 i
      · simpa [w] using congrFun hcon.2 i
    have hu0 := h.posSemidef.dotProduct_mulVec_nonneg u
    have hw0 := h.posSemidef.dotProduct_mulVec_nonneg w
    simp only [star_trivial] at hu0 hw0
    have : 0 < u ⬝ᵥ Y *ᵥ u + w ⬝ᵥ Y *ᵥ w := by
      rcases hne with hne | hne
      · have := h.dotProduct_mulVec_pos hne
        simp only [star_trivial] at this
        linarith
      · have := h.dotProduct_mulVec_pos hne
        simp only [star_trivial] at this
        linarith
    exact_mod_cast this

/-! ## The Siegel upper half-space -/

/-- `Z` is in the Siegel upper half-space: symmetric with positive definite imaginary part. -/
def IsSiegel (Z : Matrix n n ℂ) : Prop := Z.IsSymm ∧ (Z.map Complex.im).PosDef

theorem imH_of_isSymm {Z : Matrix n n ℂ} (hZ : Z.IsSymm) : imH Z = cx (Z.map Complex.im) := by
  ext i j
  have hji : Z j i = Z i j := by simpa using congrFun (congrFun hZ i) j
  change (-(I / 2)) * (Z i j - star (Z j i)) = ((Z i j).im : ℂ)
  rw [hji]
  apply Complex.ext
  · simp; ring
  · simp

theorem IsSiegel.imH_posDef {Z : Matrix n n ℂ} (hZ : IsSiegel Z) : (imH Z).PosDef := by
  rw [imH_of_isSymm hZ.1, posDef_cx_iff]; exact hZ.2

/-! ## The action of a real symplectic matrix -/

/-- `A Z + B` for `M = (A B; C D)`. -/
noncomputable def num (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  cx M.toBlocks₁₁ * Z + cx M.toBlocks₁₂

/-- `C Z + D` for `M = (A B; C D)`. -/
noncomputable def den (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  cx M.toBlocks₂₁ * Z + cx M.toBlocks₂₂

/-- `(A Z + B)(C Z + D)⁻¹` for `M = (A B; C D)`. -/
noncomputable def act (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  num M Z * (den M Z)⁻¹

/-- The block relations of a real symplectic matrix, for the complexified blocks. -/
theorem block_relations {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ) :
    (cx M.toBlocks₁₁)ᵀ * cx M.toBlocks₂₁ = (cx M.toBlocks₂₁)ᵀ * cx M.toBlocks₁₁ ∧
    (cx M.toBlocks₁₂)ᵀ * cx M.toBlocks₂₂ = (cx M.toBlocks₂₂)ᵀ * cx M.toBlocks₁₂ ∧
    (cx M.toBlocks₁₁)ᵀ * cx M.toBlocks₂₂ - (cx M.toBlocks₂₁)ᵀ * cx M.toBlocks₁₂ = 1 := by
  have h : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ ∈
      symplecticGroup n ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.mp h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [cx_mul, cx_transpose] using congrArg cx r1
  · simpa only [cx_mul, cx_transpose] using congrArg cx r2
  · simpa only [cx_mul, cx_transpose, cx_sub, cx_one] using congrArg cx r3

/-- `C Z + D` is invertible. -/
theorem isUnit_den {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ)
    {Z : Matrix n n ℂ} (hZ : IsSiegel Z) : IsUnit (den M Z) := by
  obtain ⟨r1, r2, r3⟩ := block_relations hM
  exact isUnit_den_aux (cx M.toBlocks₁₁) (cx M.toBlocks₁₂) (cx M.toBlocks₂₁) (cx M.toBlocks₂₂) Z (by simpa only [cx_conjTranspose] using r1)
    (by simpa only [cx_conjTranspose] using r2) (by simpa only [cx_conjTranspose] using r3)
    hZ.imH_posDef

/-- `Im ((A Z + B)(C Z + D)⁻¹) = (C Z + D)⁻ᴴ · Im Z · (C Z + D)⁻¹`, as Hermitian matrices. -/
theorem imH_act {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ)
    {Z : Matrix n n ℂ} (hZ : IsSiegel Z) :
    imH (act M Z) = (den M Z)⁻¹ᴴ * imH Z * (den M Z)⁻¹ := by
  obtain ⟨r1, r2, r3⟩ := block_relations hM
  exact imH_act_aux (cx M.toBlocks₁₁) (cx M.toBlocks₁₂) (cx M.toBlocks₂₁) (cx M.toBlocks₂₂) Z (by simpa only [cx_conjTranspose] using r1)
    (by simpa only [cx_conjTranspose] using r2) (by simpa only [cx_conjTranspose] using r3)
    (isUnit_den hM hZ)

/-- The action preserves the Siegel upper half-space. -/
theorem isSiegel_act {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ)
    {Z : Matrix n n ℂ} (hZ : IsSiegel Z) : IsSiegel (act M Z) := by
  obtain ⟨r1, r2, r3⟩ := block_relations hM
  have hQ := isUnit_den hM hZ
  have hdet : IsUnit (den M Z).det := (isUnit_iff_isUnit_det _).mp hQ
  have hsymm : (act M Z).IsSymm := by
    have hk : (den M Z)ᵀ * num M Z = (num M Z)ᵀ * den M Z :=
      key_transpose _ _ _ _ Z r1 r2 r3 hZ.1
    have e1 : (den M Z)ᵀ⁻¹ * (den M Z)ᵀ = 1 :=
      nonsing_inv_mul _ (by rwa [det_transpose])
    have e2 : den M Z * (den M Z)⁻¹ = 1 := mul_nonsing_inv _ hdet
    rw [IsSymm, act, transpose_mul, transpose_nonsing_inv]
    calc (den M Z)ᵀ⁻¹ * (num M Z)ᵀ
        = (den M Z)ᵀ⁻¹ * ((num M Z)ᵀ * den M Z) * (den M Z)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]
      _ = ((den M Z)ᵀ⁻¹ * (den M Z)ᵀ) * num M Z * (den M Z)⁻¹ := by
          rw [← hk]; simp only [Matrix.mul_assoc]
      _ = num M Z * (den M Z)⁻¹ := by rw [e1, Matrix.one_mul]
  refine ⟨hsymm, ?_⟩
  rw [← posDef_cx_iff, ← imH_of_isSymm hsymm, imH_act hM hZ]
  refine hZ.imH_posDef.conjTranspose_mul_mul_same ?_
  rw [mulVec_injective_iff_isUnit]
  exact (isUnit_nonsing_inv_iff).mpr hQ

/-! ## The cocycle relation and the action law -/

theorem toBlocks_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ ∧
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have h := fromBlocks_multiply M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
    N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂
  rw [fromBlocks_toBlocks, fromBlocks_toBlocks] at h
  rw [h]
  simp

/-- `A''Z + B'' = (A W + B)(C'Z + D')` with `W = M'·Z`, for the product `M M'`. -/
theorem num_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) {Z : Matrix n n ℂ} (hN : IsUnit (den N Z)) :
    num (M * N) Z = num M (act N Z) * den N Z := by
  have hdet : IsUnit (den N Z).det := (isUnit_iff_isUnit_det _).mp hN
  obtain ⟨t1, t2, -, -⟩ := toBlocks_mul M N
  have e : (den N Z)⁻¹ * den N Z = 1 := nonsing_inv_mul _ hdet
  have hW : act N Z * den N Z = num N Z := by rw [act, Matrix.mul_assoc, e, Matrix.mul_one]
  have h : num M (act N Z) * den N Z = cx M.toBlocks₁₁ * num N Z + cx M.toBlocks₁₂ * den N Z := by
    rw [num, add_mul, Matrix.mul_assoc, hW]
  rw [h]
  simp only [num, den, t1, t2, cx_add, cx_mul]
  noncomm_ring

/-- The cocycle relation `C''Z + D'' = (C W + D)(C'Z + D')` with `W = M'·Z`. -/
theorem den_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) {Z : Matrix n n ℂ} (hN : IsUnit (den N Z)) :
    den (M * N) Z = den M (act N Z) * den N Z := by
  have hdet : IsUnit (den N Z).det := (isUnit_iff_isUnit_det _).mp hN
  obtain ⟨-, -, t3, t4⟩ := toBlocks_mul M N
  have e : (den N Z)⁻¹ * den N Z = 1 := nonsing_inv_mul _ hdet
  have hW : act N Z * den N Z = num N Z := by rw [act, Matrix.mul_assoc, e, Matrix.mul_one]
  have h : den M (act N Z) * den N Z = cx M.toBlocks₂₁ * num N Z + cx M.toBlocks₂₂ * den N Z := by
    rw [den, add_mul, Matrix.mul_assoc, hW]
  rw [h]
  simp only [num, den, t3, t4, cx_add, cx_mul]
  noncomm_ring

/-- The action law `(M M')·Z = M·(M'·Z)`. -/
theorem act_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) {Z : Matrix n n ℂ} (hN : IsUnit (den N Z)) :
    act (M * N) Z = act M (act N Z) := by
  have hdet : IsUnit (den N Z).det := (isUnit_iff_isUnit_det _).mp hN
  have e : den N Z * (den N Z)⁻¹ = 1 := mul_nonsing_inv _ hdet
  rw [act, num_mul M N hN, den_mul M N hN, Matrix.mul_inv_rev]
  calc num M (act N Z) * den N Z * ((den N Z)⁻¹ * (den M (act N Z))⁻¹)
      = num M (act N Z) * (den N Z * (den N Z)⁻¹) * (den M (act N Z))⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]; rfl

theorem act_one (Z : Matrix n n ℂ) : act 1 Z = Z := by
  have h11 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₁ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]
  have h12 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₂ = 0 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₂]
  have h21 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]
  have h22 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₂ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]
  simp only [act, num, den, h11, h12, h21, h22, cx_one, cx_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add, add_zero, inv_one, Matrix.mul_one]

/-- The Siegel upper half-space `ℍ_n`. -/
def SiegelUpperHalfSpace (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  {Z : Matrix n n ℂ // IsSiegel Z}

/-- The real symplectic group acts on the Siegel upper half-space. -/
noncomputable instance : MulAction (symplecticGroup n ℝ) (SiegelUpperHalfSpace n) where
  smul M Z := ⟨act M.1 Z.1, isSiegel_act M.2 Z.2⟩
  one_smul Z := Subtype.ext (act_one Z.1)
  mul_smul M N Z := Subtype.ext (act_mul M.1 N.1 (isUnit_den N.2 Z.2))

end TauTrack.Siegel
