module

public import TauTrack.Siegel.ThetaInversion
public import TauTrack.Siegel.ThetaHolomorphic
public import TauTrack.Siegel.Petersson
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.LevelOne
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.PathConnected

/-!
# The inversion of the theta series in degree `n`, on the whole Siegel upper half-space

For a unimodular lattice `L` of rank `2k` and `Z ∈ ℍ_n`,

  `Θ_L(−Z⁻¹) = (−i)^{nk} · det(Z)^k · Θ_L(Z)`     (`siegelTheta_inversion`),

and for an even unimodular lattice the factor `(−i)^{nk}` is `1` (`siegelTheta_inversion_even`).

The identity is known for `Z = iY` (`siegelTheta_inversion_imag`, from
`siegelTheta_inversion_smul`). For `Z = X + iY` both sides are holomorphic in `s` along
`Z_s = sX + iY` on the convex open set `{s : Y + Im(s)·X > 0}`, and they agree for `s = it`,
`t` real and small. The identity theorem in one variable gives the identity at `s = 1`.
-/

@[expose] public section

open Matrix Complex Module Filter Topology
open scoped Real RealInnerProductSpace ComplexOrder MatrixOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The imaginary axis -/

/-- A positive definite real matrix is `S Sᵀ` with `S` invertible (take `S = √Y`). -/
theorem exists_mul_transpose_of_posDef {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    ∃ S R : Matrix n n ℝ, R * S = 1 ∧ S * R = 1 ∧ S * Sᵀ = Y := by
  have hSS : CFC.sqrt Y * CFC.sqrt Y = Y := CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg
  have hSt : (CFC.sqrt Y)ᵀ = CFC.sqrt Y := by
    have h := (CFC.sqrt_nonneg Y).posSemidef.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hdet : IsUnit (CFC.sqrt Y).det := by
    have h : (CFC.sqrt Y).det * (CFC.sqrt Y).det = Y.det := by rw [← det_mul, hSS]
    exact isUnit_iff_ne_zero.mpr fun h0 => hY.det_pos.ne' (by rw [← h, h0, zero_mul])
  exact ⟨CFC.sqrt Y, (CFC.sqrt Y)⁻¹, nonsing_inv_mul _ hdet, mul_nonsing_inv _ hdet,
    by rw [hSt, hSS]⟩

theorem neg_inv_I_smul_cx {Y : Matrix n n ℝ} (hY : IsUnit Y.det) :
    -(I • cx Y)⁻¹ = I • cx Y⁻¹ := by
  have h : (I • cx Y)⁻¹ = -(I • cx Y⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← cx_mul,
      nonsing_inv_mul _ hY, cx_one, I_mul_I]
    simp
  rw [h, neg_neg]

/-- **Inversion on the imaginary axis**: `Θ_L(i Y⁻¹) = det(Y)^k · Θ_L(i Y)` for `L` unimodular
of rank `2k` and `Y` real positive definite. -/
theorem siegelTheta_inversion_imag {L : Submodule ℤ E} (hU : ZLattice.IsUnimodular L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    siegelTheta L (I • cx Y⁻¹) = ((Y.det ^ k : ℝ) : ℂ) * siegelTheta L (I • cx Y) := by
  obtain ⟨S, R, hRS, hSR, hSY⟩ := exists_mul_transpose_of_posDef hY
  have h := siegelTheta_inversion_smul hU hk hRS hSR UpperHalfPlane.I
  have hSI : ((ModularGroup.S • UpperHalfPlane.I : UpperHalfPlane) : ℂ) = I := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [UpperHalfPlane.coe_I]
  have hinv : Y⁻¹ = Rᵀ * R := by
    apply Matrix.inv_eq_left_inv
    rw [← hSY, Matrix.mul_assoc, ← Matrix.mul_assoc R, hRS, Matrix.one_mul, ← Matrix.transpose_mul,
      hSR, transpose_one]
  have hdet : |S.det| ^ (2 * k) = Y.det ^ k := by
    rw [← hSY, det_mul, det_transpose, pow_mul, sq_abs, ← sq]
  rw [hSI, UpperHalfPlane.coe_I, ← hinv, hSY, hdet] at h
  rw [h, ← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow, mul_one]

/-! ## The inversion `Z ↦ −Z⁻¹` on `ℍ_n` -/

theorem act_J (W : Matrix n n ℂ) : act (Matrix.J n ℝ) W = -W⁻¹ := by
  have h1 : cx (-1 : Matrix n n ℝ) = -1 := by ext i j; simp [cx, Matrix.one_apply]; split_ifs <;> simp
  simp [act, num, den, Matrix.J, h1]

theorem den_J (W : Matrix n n ℂ) : den (Matrix.J n ℝ) W = W := by
  simp [den, Matrix.J]

theorem IsSiegel.neg_inv {W : Matrix n n ℂ} (h : IsSiegel W) : IsSiegel (-W⁻¹) := by
  rw [← act_J]
  exact isSiegel_act (SymplecticGroup.J_mem n ℝ) h

theorem IsSiegel.det_ne_zero {W : Matrix n n ℂ} (h : IsSiegel W) : W.det ≠ 0 := by
  have h1 := isUnit_den (SymplecticGroup.J_mem n ℝ) h
  rw [den_J] at h1
  exact ((isUnit_iff_isUnit_det _).mp h1).ne_zero

theorem mem_domain_of_isSiegel {W : Matrix n n ℂ} (h : IsSiegel W) :
    (fun i j => W i j) ∈ domain n := by
  change IsSiegel (symPart W)
  rwa [symPart_of_isSymm h.1]

/-! ## Differentiability of determinants and inverses in one variable -/

theorem differentiableAt_det {M : ℂ → Matrix n n ℂ} {s : ℂ}
    (h : ∀ i j, DifferentiableAt ℂ (fun s => M s i j) s) :
    DifferentiableAt ℂ (fun s => (M s).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact DifferentiableAt.fun_finsetProd fun i _ => h (σ i) i

theorem differentiableAt_inv_apply {M : ℂ → Matrix n n ℂ} {s : ℂ}
    (h : ∀ i j, DifferentiableAt ℂ (fun s => M s i j) s) (hs : (M s).det ≠ 0) (i j : n) :
    DifferentiableAt ℂ (fun s => (M s)⁻¹ i j) s := by
  have he : (fun s => (M s)⁻¹ i j) =
      fun s => ((M s).det)⁻¹ * ((M s).updateRow j (Pi.single i 1)).det := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', Matrix.adjugate_apply,
      smul_eq_mul]
  rw [he]
  refine ((differentiableAt_det h).inv hs).mul (differentiableAt_det fun a b => ?_)
  by_cases hab : a = j
  · subst hab
    simp
  · simpa [Matrix.updateRow_ne hab] using h a b

/-! ## The path `Z_s = s · Re Z + i · Im Z` -/

/-- The path `s ↦ s · Re Z + i · Im Z` through `Z` (at `s = 1`) and `i · Im Z` (at `s = 0`). -/
noncomputable def pathM (Z : Matrix n n ℂ) (s : ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => s * ((Z i j).re : ℂ) + I * ((Z i j).im : ℂ)

theorem pathM_one (Z : Matrix n n ℂ) : pathM Z 1 = Z := by
  ext i j
  simp [pathM, mul_comm I]

theorem pathM_isSymm {Z : Matrix n n ℂ} (hZ : Z.IsSymm) (s : ℂ) : (pathM Z s).IsSymm := by
  ext i j
  simp only [pathM, transpose_apply, of_apply]
  rw [hZ.apply i j]

theorem pathM_map_im (Z : Matrix n n ℂ) (s : ℂ) :
    (pathM Z s).map Complex.im = s.im • Z.map Complex.re + Z.map Complex.im := by
  ext i j
  simp [pathM]

theorem pathM_mul_I (Z : Matrix n n ℂ) (t : ℝ) :
    pathM Z (t * I) = I • cx (t • Z.map Complex.re + Z.map Complex.im) := by
  ext i j
  simp [pathM, cx]
  ring

/-- The parameters `s` for which `Z_s` lies in `ℍ_n`. -/
def pathSet (Z : Matrix n n ℂ) : Set ℂ := {s | IsSiegel (pathM Z s)}

theorem mem_pathSet_iff {Z : Matrix n n ℂ} (hZ : Z.IsSymm) {s : ℂ} :
    s ∈ pathSet Z ↔ (s.im • Z.map Complex.re + Z.map Complex.im).PosDef := by
  change IsSiegel (pathM Z s) ↔ _
  rw [IsSiegel, pathM_map_im]
  exact ⟨fun h => h.2, fun h => ⟨pathM_isSymm hZ s, h⟩⟩

theorem differentiableAt_pathM_apply (Z : Matrix n n ℂ) (s : ℂ) (i j : n) :
    DifferentiableAt ℂ (fun s => pathM Z s i j) s := by
  simp only [pathM, of_apply]
  fun_prop

theorem differentiable_pathM (Z : Matrix n n ℂ) :
    Differentiable ℂ fun s => (fun i j => pathM Z s i j : n → n → ℂ) :=
  differentiable_pi.mpr fun i => differentiable_pi.mpr fun j s =>
    differentiableAt_pathM_apply Z s i j

theorem isOpen_pathSet {Z : Matrix n n ℂ} (hZ : Z.IsSymm) : IsOpen (pathSet Z) := by
  have h : pathSet Z = (fun s => (fun i j => pathM Z s i j : n → n → ℂ)) ⁻¹' domain n := by
    ext s
    change IsSiegel (pathM Z s) ↔ IsSiegel (symPart (pathM Z s))
    rw [symPart_of_isSymm (pathM_isSymm hZ s)]
  rw [h]
  exact isOpen_domain.preimage (differentiable_pathM Z).continuous

theorem convex_pathSet {Z : Matrix n n ℂ} (hZ : Z.IsSymm) : Convex ℝ (pathSet Z) := by
  rw [convex_iff_forall_pos]
  intro s hs t ht a b ha hb hab
  rw [mem_pathSet_iff hZ] at hs ht ⊢
  have h : (a • s + b • t).im • Z.map Complex.re + Z.map Complex.im =
      a • (s.im • Z.map Complex.re + Z.map Complex.im) +
        b • (t.im • Z.map Complex.re + Z.map Complex.im) := by
    ext i j
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
    linear_combination (-(Z i j).im) * hab
  rw [h]
  exact (hs.smul ha).add (ht.smul hb)

/-! ## The inversion on `ℍ_n` -/

/-- **Inversion of the degree-`n` theta series**: for a unimodular lattice `L` of rank `2k` and
`Z` in the Siegel upper half-space, `Θ_L(−Z⁻¹) = (−i)^{nk} · det(Z)^k · Θ_L(Z)`. -/
theorem siegelTheta_inversion {L : Submodule ℤ E} (hU : ZLattice.IsUnimodular L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {Z : Matrix n n ℂ} (hZ : IsSiegel Z) :
    siegelTheta L (-Z⁻¹) =
      (-I) ^ (Fintype.card n * k) * Z.det ^ k * siegelTheta L Z := by
  have := hU.isIntegral.discreteTopology
  let f : ℂ → ℂ := fun s => siegelTheta L (-(pathM Z s)⁻¹)
  let g : ℂ → ℂ := fun s =>
    (-I) ^ (Fintype.card n * k) * (pathM Z s).det ^ k * siegelTheta L (pathM Z s)
  have hopen := isOpen_pathSet hZ.1
  have hθ : ∀ W : Matrix n n ℂ, IsSiegel W →
      DifferentiableAt ℂ (fun X : n → n → ℂ => siegelTheta L (Matrix.of X)) (fun i j => W i j) :=
    fun W hW => (differentiableOn_siegelTheta L).differentiableAt
      (isOpen_domain.mem_nhds (mem_domain_of_isSiegel hW))
  have hf : DifferentiableOn ℂ f (pathSet Z) := by
    intro s hs
    have h1 : DifferentiableAt ℂ
        (fun s => (fun i j => (-(pathM Z s)⁻¹) i j : n → n → ℂ)) s := by
      refine differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => ?_
      simp only [Matrix.neg_apply]
      exact (differentiableAt_inv_apply (fun a b => differentiableAt_pathM_apply Z s a b)
        (IsSiegel.det_ne_zero hs) i j).neg
    have h2 : DifferentiableAt ℂ ((fun X : n → n → ℂ => siegelTheta L (Matrix.of X)) ∘
        fun s => (fun i j => (-(pathM Z s)⁻¹) i j : n → n → ℂ)) s :=
      DifferentiableAt.comp s (hθ _ (IsSiegel.neg_inv hs)) h1
    exact h2.differentiableWithinAt
  have hg : DifferentiableOn ℂ g (pathSet Z) := by
    intro s hs
    have h1 : DifferentiableAt ℂ (fun s => (fun i j => pathM Z s i j : n → n → ℂ)) s :=
      (differentiable_pathM Z).differentiableAt
    have h2 : DifferentiableAt ℂ (fun s => siegelTheta L (pathM Z s)) s := by
      change DifferentiableAt ℂ ((fun X : n → n → ℂ => siegelTheta L (Matrix.of X)) ∘
        fun s => (fun i j => pathM Z s i j : n → n → ℂ)) s
      exact DifferentiableAt.comp s (hθ _ hs) h1
    exact (((differentiableAt_const _).mul
      ((differentiableAt_det fun a b => differentiableAt_pathM_apply Z s a b).pow k)).mul
      h2).differentiableWithinAt
  have h0 : (0 : ℂ) ∈ pathSet Z := by
    rw [mem_pathSet_iff hZ.1]
    simpa using hZ.2
  have h1 : (1 : ℂ) ∈ pathSet Z := by
    change IsSiegel (pathM Z 1)
    rw [pathM_one]
    exact hZ
  have haxis : ∀ t : ℝ, (t * I : ℂ) ∈ pathSet Z → f (t * I) = g (t * I) := by
    intro t ht
    have hY : (t • Z.map Complex.re + Z.map Complex.im).PosDef := by
      simpa using (mem_pathSet_iff hZ.1).mp ht
    simp only [f, g]
    rw [pathM_mul_I, neg_inv_I_smul_cx hY.det_pos.ne'.isUnit, siegelTheta_inversion_imag hU hk hY,
      det_smul, det_cx, mul_pow, ← pow_mul, ← mul_assoc ((-I) ^ (Fintype.card n * k)), ← mul_pow,
      neg_mul, I_mul_I, neg_neg, one_pow, one_mul]
    push_cast
    rfl
  have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), f s = g s := by
    have hcont : Continuous fun t : ℝ => (t * I : ℂ) := by fun_prop
    have htend0 : Tendsto (fun t : ℝ => (t * I : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
      have h := hcont.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun t : ℝ => (t * I : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend0 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, f (t * I) = g (t * I) :=
      (htend0.eventually (hopen.mem_nhds h0)).mono fun t ht => haxis t ht
    exact htend.frequently hev.frequently
  have key := (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hopen) (convex_pathSet hZ.1).isPreconnected h0 hfreq
  have h := key h1
  simpa only [f, g, pathM_one] using h

/-- For an even unimodular lattice of rank `2k`: `Θ_L(−Z⁻¹) = det(Z)^k · Θ_L(Z)` on `ℍ_n`. This
is the transformation law of weight `k` under the symplectic matrix `J = (0 −1; 1 0)`. -/
theorem siegelTheta_inversion_even {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ZLattice.IsEven L) (hU : ZLattice.IsUnimodular L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {Z : Matrix n n ℂ} (hZ : IsSiegel Z) :
    siegelTheta L (act (Matrix.J n ℝ) Z) = Z.det ^ k * siegelTheta L Z := by
  obtain ⟨m, hm⟩ := hL.eight_dvd_finrank hU
  have hk4 : k = 4 * m := by omega
  have hone : (-I) ^ (Fintype.card n * k) = 1 := by
    rw [hk4, mul_comm 4 m, ← mul_assoc, mul_comm, pow_mul]
    have : (-I) ^ 4 = 1 := by
      rw [neg_pow, I_pow_four]; norm_num
    rw [this, one_pow]
  rw [act_J, siegelTheta_inversion hU hk hZ, hone, one_mul]

end TauTrack.Siegel
