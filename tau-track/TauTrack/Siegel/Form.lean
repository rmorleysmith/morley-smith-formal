module

public import TauTrack.Siegel.Basic
public import TauCeti.Analysis.Matrix.PosDef

/-!
# Siegel modular forms: the definition

* `j M Z = det (C Z + D)`: the automorphy factor, with the cocycle relation `j_mul`.
* `slash k M F`: `(F ∣[k] M)(Z) = j(M, Z)^(-k) · F(M·Z)`, a right action of `Sp(2n, ℝ)`.
* `ofInt`: `Sp(2n, ℤ) → Sp(2n, ℝ)`.
* `IsHolomorphic F`: `F` is holomorphic on `ℍ_n`.
* `IsBoundedAtInfinity F`: `F` is bounded on some region `Im Z ≥ c · 1`.
* `SiegelModularForm n k`: holomorphic, invariant under the slash action of `Sp(2n, ℤ)` in
  weight `k`, and bounded at infinity.
-/

@[expose] public section

open Matrix Complex
open scoped ComplexOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The automorphy factor -/

/-- The automorphy factor `j(M, Z) = det (C Z + D)`. -/
noncomputable def j (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (Z : Matrix n n ℂ) : ℂ := (den M Z).det

theorem j_ne_zero {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ)
    {Z : Matrix n n ℂ} (hZ : IsSiegel Z) : j M Z ≠ 0 :=
  ((isUnit_iff_isUnit_det _).mp (isUnit_den hM hZ)).ne_zero

/-- The cocycle relation `j(M N, Z) = j(M, N·Z) · j(N, Z)`. -/
theorem j_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) {Z : Matrix n n ℂ} (hN : IsUnit (den N Z)) :
    j (M * N) Z = j M (act N Z) * j N Z := by
  rw [j, den_mul M N hN, det_mul]; rfl

theorem den_one (Z : Matrix n n ℂ) : den 1 Z = 1 := by
  have h21 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]
  have h22 : (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₂ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]
  simp only [den, h21, h22, cx_one, cx_zero, Matrix.zero_mul, zero_add]

@[simp] theorem j_one (Z : Matrix n n ℂ) : j 1 Z = 1 := by rw [j, den_one, det_one]

/-! ## The slash action -/

theorem smul_val (M : symplecticGroup n ℝ) (Z : SiegelUpperHalfSpace n) :
    (M • Z).1 = act M.1 Z.1 := rfl

/-- The weight `k` slash action: `(F ∣[k] M)(Z) = j(M, Z)^(-k) · F(M·Z)`. -/
noncomputable def slash (k : ℤ) (M : symplecticGroup n ℝ) (F : SiegelUpperHalfSpace n → ℂ) :
    SiegelUpperHalfSpace n → ℂ :=
  fun Z => j M.1 Z.1 ^ (-k) * F (M • Z)

theorem slash_apply (k : ℤ) (M : symplecticGroup n ℝ) (F : SiegelUpperHalfSpace n → ℂ)
    (Z : SiegelUpperHalfSpace n) : slash k M F Z = j M.1 Z.1 ^ (-k) * F (M • Z) := rfl

@[simp] theorem slash_one (k : ℤ) (F : SiegelUpperHalfSpace n → ℂ) : slash k 1 F = F := by
  funext Z
  simp [slash_apply]

/-- `F ∣[k] (M N) = (F ∣[k] M) ∣[k] N`. -/
theorem slash_mul (k : ℤ) (M N : symplecticGroup n ℝ) (F : SiegelUpperHalfSpace n → ℂ) :
    slash k (M * N) F = slash k N (slash k M F) := by
  funext Z
  simp only [slash_apply, Submonoid.coe_mul, mul_smul]
  rw [j_mul M.1 N.1 (isUnit_den N.2 Z.2), mul_zpow, ← smul_val]
  ring

theorem slash_add (k : ℤ) (M : symplecticGroup n ℝ) (F G : SiegelUpperHalfSpace n → ℂ) :
    slash k M (F + G) = slash k M F + slash k M G := by
  funext Z
  simp [slash_apply, mul_add]

theorem slash_smul (k : ℤ) (M : symplecticGroup n ℝ) (c : ℂ) (F : SiegelUpperHalfSpace n → ℂ) :
    slash k M (c • F) = c • slash k M F := by
  funext Z
  simp [slash_apply, mul_left_comm]

/-- Weights add under products: `(F G) ∣[k + l] M = (F ∣[k] M)(G ∣[l] M)`. -/
theorem slash_mul_fun (k l : ℤ) (M : symplecticGroup n ℝ) (F G : SiegelUpperHalfSpace n → ℂ) :
    slash (k + l) M (F * G) = slash k M F * slash l M G := by
  funext Z
  have h := j_ne_zero M.2 Z.2
  simp only [slash_apply, Pi.mul_apply, neg_add, zpow_add₀ h]
  ring

noncomputable instance : SlashAction ℤ (symplecticGroup n ℝ) (SiegelUpperHalfSpace n → ℂ) where
  map := slash
  zero_slash k M := by funext Z; simp [slash_apply]
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := slash_add

/-! ## Integral symplectic matrices -/

/-- `Sp(2n, ℤ) → Sp(2n, ℝ)`. -/
def ofInt : symplecticGroup n ℤ →* symplecticGroup n ℝ where
  toFun γ := ⟨(Int.castRingHom ℝ).mapMatrix γ.1, by
    have h := γ.2
    rw [SymplecticGroup.mem_iff] at h ⊢
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    simpa only [map_mul, RingHom.mapMatrix_apply, transpose_map, map_J] using this⟩
  map_one' := Subtype.ext (map_one (Int.castRingHom ℝ).mapMatrix)
  map_mul' γ δ := Subtype.ext (map_mul (Int.castRingHom ℝ).mapMatrix γ.1 δ.1)

/-! ## Holomorphy and boundedness -/

/-- The symmetric part `(X + Xᵀ) / 2`. -/
noncomputable def symPart (X : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (X + Xᵀ)

theorem symPart_isSymm (X : Matrix n n ℂ) : (symPart X).IsSymm := by
  rw [IsSymm, symPart, transpose_smul, transpose_add, transpose_transpose, add_comm]

theorem symPart_of_isSymm {X : Matrix n n ℂ} (hX : X.IsSymm) : symPart X = X := by
  rw [symPart, hX.eq, ← two_smul ℂ X, smul_smul]; norm_num

/-- The extension of `F` from `ℍ_n` to all square matrices: `X ↦ F((X + Xᵀ)/2)` where that is
defined, and `0` elsewhere. -/
noncomputable def extend (F : SiegelUpperHalfSpace n → ℂ) (X : n → n → ℂ) : ℂ :=
  open Classical in
  if h : IsSiegel (symPart (Matrix.of X)) then F ⟨symPart (Matrix.of X), h⟩ else 0

/-- The set of square matrices whose symmetric part lies in `ℍ_n`. It is open
(`isOpen_domain`), and it retracts linearly onto `ℍ_n`. -/
def domain (n : Type*) [Fintype n] [DecidableEq n] : Set (n → n → ℂ) :=
  {X | IsSiegel (symPart (Matrix.of X))}

/-- `F` is holomorphic on `ℍ_n`: its pull-back along the linear retraction `X ↦ (X + Xᵀ)/2` is
complex differentiable on the open set `domain n`. -/
def IsHolomorphic (F : SiegelUpperHalfSpace n → ℂ) : Prop :=
  DifferentiableOn ℂ (extend F) (domain n)

/-- `F` is bounded on some region `Im Z ≥ c · 1`. For an invariant holomorphic function this
is the same as being bounded on every such region with `c > 0` (for `n = 1` by the
`q`-expansion, for `n ≥ 2` automatically, by Koecher's principle); that equivalence is not
proved here. -/
def IsBoundedAtInfinity (F : SiegelUpperHalfSpace n → ℂ) : Prop :=
  ∃ c B : ℝ, ∀ Z : SiegelUpperHalfSpace n,
    (Z.1.map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef → ‖F Z‖ ≤ B

/-- The region `Im Z ≥ c · 1` shrinks as `c` grows. -/
theorem posSemidef_sub_of_le {Y : Matrix n n ℝ} {c c' : ℝ} (h : c ≤ c')
    (hY : (Y - c' • (1 : Matrix n n ℝ)).PosSemidef) : (Y - c • (1 : Matrix n n ℝ)).PosSemidef := by
  have e : Y - c • (1 : Matrix n n ℝ) = (Y - c' • (1 : Matrix n n ℝ)) + (c' - c) • 1 := by
    rw [sub_smul]; abel
  rw [e]
  exact hY.add (PosSemidef.one.smul (sub_nonneg.mpr h))

theorem IsBoundedAtInfinity.add {F G : SiegelUpperHalfSpace n → ℂ} (hF : IsBoundedAtInfinity F)
    (hG : IsBoundedAtInfinity G) : IsBoundedAtInfinity (F + G) := by
  obtain ⟨c₁, B₁, h₁⟩ := hF
  obtain ⟨c₂, B₂, h₂⟩ := hG
  refine ⟨max c₁ c₂, B₁ + B₂, fun Z hZ => (norm_add_le _ _).trans (add_le_add ?_ ?_)⟩
  · exact h₁ Z (posSemidef_sub_of_le (le_max_left _ _) hZ)
  · exact h₂ Z (posSemidef_sub_of_le (le_max_right _ _) hZ)

theorem IsBoundedAtInfinity.mul {F G : SiegelUpperHalfSpace n → ℂ} (hF : IsBoundedAtInfinity F)
    (hG : IsBoundedAtInfinity G) : IsBoundedAtInfinity (F * G) := by
  obtain ⟨c₁, B₁, h₁⟩ := hF
  obtain ⟨c₂, B₂, h₂⟩ := hG
  refine ⟨max c₁ c₂, B₁ * B₂, fun Z hZ => ?_⟩
  have a₁ := h₁ Z (posSemidef_sub_of_le (le_max_left _ _) hZ)
  have a₂ := h₂ Z (posSemidef_sub_of_le (le_max_right _ _) hZ)
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul a₁ a₂ (norm_nonneg _) ((norm_nonneg _).trans a₁)

/-- The imaginary part of the symmetric part, as a self-adjoint real matrix. -/
noncomputable def imSym (X : n → n → ℂ) : selfAdjoint (Matrix n n ℝ) :=
  ⟨(symPart (Matrix.of X)).map Complex.im, by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      ← transpose_map, (symPart_isSymm _).eq]⟩

theorem continuous_imSym : Continuous (imSym : (n → n → ℂ) → selfAdjoint (Matrix n n ℝ)) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun X : n → n → ℂ => ((symPart (Matrix.of X)).map Complex.im) i j) =
      fun X => ((1 / 2 : ℂ) * (X i j + X j i)).im := by
    funext X; simp [symPart]; ring
  rw [this]
  fun_prop

/-- The set of matrices whose symmetric part lies in `ℍ_n` is open. -/
theorem isOpen_domain : IsOpen (domain n) := by
  have h : domain n = imSym ⁻¹' {A : selfAdjoint (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef} := by
    ext X
    simp only [domain, IsSiegel, Set.mem_ofPred_eq, Set.mem_preimage, imSym]
    exact ⟨fun h => h.2, fun h => ⟨symPart_isSymm _, h⟩⟩
  rw [h]
  exact Matrix.isOpen_setOfPred_posDef_selfAdjoint.preimage continuous_imSym

theorem extend_apply {F : SiegelUpperHalfSpace n → ℂ} {X : n → n → ℂ} (h : X ∈ domain n) :
    extend F X = F ⟨symPart (Matrix.of X), h⟩ := by
  classical
  unfold extend
  split_ifs with h'
  · rfl
  · exact absurd h h'

/-! ## Siegel modular forms -/

/-- A Siegel modular form of degree `n` and weight `k`. -/
structure SiegelModularForm (n : Type*) [Fintype n] [DecidableEq n] (k : ℤ) where
  /-- The underlying function on the Siegel upper half-space. -/
  toFun : SiegelUpperHalfSpace n → ℂ
  holo : IsHolomorphic toFun
  slash_eq : ∀ γ : symplecticGroup n ℤ, slash k (ofInt γ) toFun = toFun
  bdd : IsBoundedAtInfinity toFun

namespace SiegelModularForm

variable {k l : ℤ}

instance : FunLike (SiegelModularForm n k) (SiegelUpperHalfSpace n) ℂ where
  coe := toFun
  coe_injective := fun F G h => by cases F; cases G; congr

@[ext] theorem ext {F G : SiegelModularForm n k} (h : ∀ Z, F Z = G Z) : F = G :=
  DFunLike.ext F G h

/-- The transformation law `F(γ·Z) = det(C Z + D)^k · F(Z)`. -/
theorem map_smul (F : SiegelModularForm n k) (γ : symplecticGroup n ℤ)
    (Z : SiegelUpperHalfSpace n) : F (ofInt γ • Z) = j (ofInt γ).1 Z.1 ^ k * F Z := by
  have h := congrFun (F.slash_eq γ) Z
  have hj := j_ne_zero (ofInt γ).2 Z.2
  rw [slash_apply, _root_.zpow_neg] at h
  change F.toFun _ = _ * F.toFun Z
  rw [← h, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero k hj), one_mul]

theorem extend_add (F G : SiegelUpperHalfSpace n → ℂ) : extend (F + G) = extend F + extend G := by
  classical
  funext X
  by_cases h : IsSiegel (symPart (Matrix.of X))
  · simp [extend, h]; rfl
  · simp [extend, h]

theorem extend_smul (c : ℂ) (F : SiegelUpperHalfSpace n → ℂ) :
    extend (c • F) = c • extend F := by
  classical
  funext X
  by_cases h : IsSiegel (symPart (Matrix.of X))
  · simp [extend, h]; rfl
  · simp [extend, h]

theorem extend_mul (F G : SiegelUpperHalfSpace n → ℂ) : extend (F * G) = extend F * extend G := by
  classical
  funext X
  by_cases h : IsSiegel (symPart (Matrix.of X))
  · simp [extend, h]; rfl
  · simp [extend, h]

instance : Zero (SiegelModularForm n k) where
  zero :=
    { toFun := 0
      holo := by
        have : extend (0 : SiegelUpperHalfSpace n → ℂ) = 0 := by
          classical
          funext X
          by_cases h : IsSiegel (symPart (Matrix.of X))
          · simp [extend, h]; rfl
          · simp [extend, h]
        rw [IsHolomorphic, this]
        exact differentiableOn_const 0
      slash_eq := fun γ => by funext Z; simp [slash_apply]
      bdd := ⟨0, 0, fun Z _ => by simp⟩ }

instance : Add (SiegelModularForm n k) where
  add F G :=
    { toFun := F.toFun + G.toFun
      holo := by
        rw [IsHolomorphic, extend_add]
        exact F.holo.add G.holo
      slash_eq := fun γ => by rw [slash_add, F.slash_eq, G.slash_eq]
      bdd := F.bdd.add G.bdd }

instance : SMul ℂ (SiegelModularForm n k) where
  smul c F :=
    { toFun := c • F.toFun
      holo := by
        rw [IsHolomorphic, extend_smul]
        exact F.holo.const_smul c
      slash_eq := fun γ => by rw [slash_smul, F.slash_eq]
      bdd := by
        obtain ⟨c', B, h⟩ := F.bdd
        refine ⟨c', ‖c‖ * B, fun Z hZ => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (h Z hZ) (norm_nonneg c) }

/-- The product of forms of weights `k` and `l` has weight `k + l`. -/
noncomputable def mul (F : SiegelModularForm n k) (G : SiegelModularForm n l) :
    SiegelModularForm n (k + l) where
  toFun := F.toFun * G.toFun
  holo := by
    rw [IsHolomorphic, extend_mul]
    exact F.holo.mul G.holo
  slash_eq := fun γ => by rw [slash_mul_fun, F.slash_eq, G.slash_eq]
  bdd := F.bdd.mul G.bdd

/-- A constant is a Siegel modular form of weight `0`. -/
noncomputable def const (n : Type*) [Fintype n] [DecidableEq n] (c : ℂ) : SiegelModularForm n 0 where
  toFun := fun _ => c
  holo := by
    have h : ∀ X ∈ domain n, extend (fun _ : SiegelUpperHalfSpace n => c) X = c :=
      fun X hX => extend_apply hX
    exact (differentiableOn_const c).congr h
  slash_eq := fun γ => by funext Z; simp [slash_apply]
  bdd := ⟨0, ‖c‖, fun _ _ => le_rfl⟩

end SiegelModularForm

end TauTrack.Siegel
