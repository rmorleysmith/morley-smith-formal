module

public import TauTrack.Siegel.Theta
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
public import TauCeti.Algebra.Module.ZLattice.Determinant
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The inversion of the theta series in degree `n`, on scalar multiples of real matrices

For a unimodular lattice `L` of rank `2k`, an invertible real matrix `R` and `τ` in the upper
half-plane, with `Y = Rᵀ R`,

  `Θ_L(−τ⁻¹ · Y) = |det R|^{−2k} · (−i τ)^{nk} · Θ_L(τ · Y⁻¹)`.

With `Z = τ · Y⁻¹` this reads `Θ_L(−Z⁻¹) = det(−i Z)^k · Θ_L(Z)`.

The proof uses no new analysis. The tuples `Lⁿ` form a unimodular lattice in `Eⁿ`; the map
`x ↦ (∑_j R_{ij} x_j)_i` turns `tr(G(x) Y)` into a squared norm; so the degree-`n` series on
`τ · Y` is a degree-one theta series of a lattice in `Eⁿ`, to which TauCeti's inversion applies.

* `piLattice L`: the lattice `Lⁿ` in `PiLp 2 (n → E)`.
* `dual_piLattice`, `isUnimodular_piLattice`.
* `mix R`: the linear map `x ↦ (∑_j R_{ij} x_j)_i`; `det_mix : det (mix R) = (det R)^{dim E}`.
* `thetaSeries_comap_mix`: the degree-one theta series of `mix R (Lⁿ)` is `Θ_L(τ · Rᵀ R)`.
* `siegelTheta_inversion_smul`: the inversion formula above.
-/

@[expose] public section

open Matrix Complex Module
open scoped Real RealInnerProductSpace ComplexOrder MatrixOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The lattice `Lⁿ` -/

/-- The lattice `Lⁿ` of tuples of vectors of `L`, in the orthogonal sum of `n` copies of `E`. -/
def piLattice (L : Submodule ℤ E) : Submodule ℤ (PiLp 2 fun _ : n => E) where
  carrier := {x | ∀ i, x i ∈ L}
  add_mem' hx hy i := L.add_mem (hx i) (hy i)
  zero_mem' _ := L.zero_mem
  smul_mem' c _ hx i := L.smul_mem c (hx i)

theorem mem_piLattice {L : Submodule ℤ E} {x : PiLp 2 fun _ : n => E} :
    x ∈ piLattice L ↔ ∀ i, x i ∈ L := Iff.rfl

/-- The dual of `Lⁿ` is `(L^∨)ⁿ`. -/
theorem dual_piLattice (L : Submodule ℤ E) :
    ZLattice.dual (piLattice (n := n) L) = piLattice (ZLattice.dual L) := by
  ext x
  simp only [ZLattice.mem_dual, mem_piLattice, PiLp.inner_apply]
  refine ⟨fun h i y hy => ?_, fun h y hy => ?_⟩
  · obtain ⟨m, hm⟩ := h (WithLp.toLp 2 (Pi.single i y)) (fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hy
      · simp [hj])
    refine ⟨m, ?_⟩
    rw [← hm, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · choose m hm using fun i => h i (y i) (hy i)
    exact ⟨∑ i, m i, by simp [hm]⟩

theorem isUnimodular_piLattice {L : Submodule ℤ E} (h : ZLattice.IsUnimodular L) :
    ZLattice.IsUnimodular (piLattice (n := n) L) := by
  rw [ZLattice.isUnimodular_iff_eq_dual, dual_piLattice, ← ZLattice.isUnimodular_iff_eq_dual.mp h]

/-- Tuples of vectors of `L`, as elements of the lattice `Lⁿ`. -/
def piLatticeEquiv (L : Submodule ℤ E) : (n → L) ≃ piLattice (n := n) L where
  toFun x := ⟨WithLp.toLp 2 fun i => (x i : E), fun i => (x i).2⟩
  invFun y i := ⟨y.1 i, y.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The map `x ↦ (∑_j R_{ij} x_j)_i` -/

/-- The linear map `x ↦ (∑_j R_{ij} x_j)_i` on tuples of vectors. -/
noncomputable def mix (R : Matrix n n ℝ) :
    (PiLp 2 fun _ : n => E) →ₗ[ℝ] (PiLp 2 fun _ : n => E) where
  toFun x := WithLp.toLp 2 fun i => ∑ j, R i j • x j
  map_add' x y := by
    ext i; simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext i; simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem mix_apply (R : Matrix n n ℝ) (x : PiLp 2 fun _ : n => E) (i : n) :
    mix R x i = ∑ j, R i j • x j := rfl

theorem mix_mul (R S : Matrix n n ℝ) : mix (E := E) (R * S) = mix R ∘ₗ mix S := by
  ext x i
  simp only [mix_apply, LinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_comm

theorem mix_one : mix (E := E) (1 : Matrix n n ℝ) = LinearMap.id := by
  ext x i
  simp [Matrix.one_apply]

/-- The map `mix R` as a continuous linear equivalence, for an invertible `R`. -/
noncomputable def mixEquiv {R S : Matrix n n ℝ} (hRS : R * S = 1) (hSR : S * R = 1) :
    (PiLp 2 fun _ : n => E) ≃L[ℝ] (PiLp 2 fun _ : n => E) :=
  (LinearEquiv.ofLinearMap (mix R) (mix S) (by rw [← mix_mul, hRS, mix_one])
    (by rw [← mix_mul, hSR, mix_one])).toContinuousLinearEquiv

@[simp] theorem mixEquiv_apply {R S : Matrix n n ℝ} (hRS : R * S = 1) (hSR : S * R = 1)
    (x : PiLp 2 fun _ : n => E) : mixEquiv hRS hSR x = mix R x := rfl

@[simp] theorem mixEquiv_symm {R S : Matrix n n ℝ} (hRS : R * S = 1) (hSR : S * R = 1) :
    (mixEquiv (E := E) hRS hSR).symm = mixEquiv hSR hRS := rfl

/-- `⟪mix R x, y⟫ = ⟪x, mix Rᵀ y⟫`. -/
theorem inner_mix (R : Matrix n n ℝ) (x y : PiLp 2 fun _ : n => E) :
    ⟪mix R x, y⟫ = ⟪x, mix Rᵀ y⟫ := by
  simp only [PiLp.inner_apply, mix_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.transpose_apply, conj_trivial]
  exact Finset.sum_comm

/-- `‖mix R x‖² = tr(G(x) · Rᵀ R)`. -/
theorem norm_mix_sq {L : Submodule ℤ E} (R : Matrix n n ℝ) (x : n → L) :
    ‖mix R (piLatticeEquiv L x : PiLp 2 fun _ : n => E)‖ ^ 2 = (gramL x * (Rᵀ * R)).trace := by
  rw [← real_inner_self_eq_norm_sq, inner_mix, ← LinearMap.comp_apply, ← mix_mul]
  simp only [PiLp.inner_apply, mix_apply, inner_sum, inner_smul_right, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, gramL_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : ((piLatticeEquiv L x : PiLp 2 fun _ : n => E) i : E) = x i := rfl
  have hj : ((piLatticeEquiv L x : PiLp 2 fun _ : n => E) j : E) = x j := rfl
  rw [this, hj, Finset.mul_sum]
  have hsym : ∑ l, R l i * R l j = ∑ l, R l j * R l i :=
    Finset.sum_congr rfl fun l _ => mul_comm _ _
  simp only [Matrix.transpose_apply]
  rw [← Finset.mul_sum, hsym, mul_comm]

/-! ## The determinant of `mix R` -/

/-- Coordinates on tuples of vectors: first the coordinate of `E`, then the index of the tuple. -/
noncomputable def coordEquiv {d : Type*} [Fintype d] (b : Basis d ℝ E) :
    (PiLp 2 fun _ : n => E) ≃ₗ[ℝ] (d → n → ℝ) where
  toFun x a i := b.repr (x i) a
  invFun f := WithLp.toLp 2 fun i => b.equivFun.symm fun a => f a i
  map_add' x y := by ext a i; simp
  map_smul' c x := by ext a i; simp
  left_inv x := by
    ext i
    exact b.equivFun.symm_apply_apply (x i)
  right_inv f := by
    ext a i
    exact congrFun (b.equivFun.apply_symm_apply fun a => f a i) a

/-- `det (mix R) = (det R)^{dim E}`: in coordinates `mix R` is `dim E` copies of `R`. -/
theorem det_mix (R : Matrix n n ℝ) :
    LinearMap.det (mix (E := E) R) = R.det ^ finrank ℝ E := by
  let b := Module.finBasis ℝ E
  let Ψ := coordEquiv (n := n) b
  let P : (Fin (finrank ℝ E) → n → ℝ) →ₗ[ℝ] (Fin (finrank ℝ E) → n → ℝ) :=
    LinearMap.pi fun a => (Matrix.toLin' R).comp (LinearMap.proj a)
  have hconj : mix (E := E) R = (Ψ.symm : _ →ₗ[ℝ] _) ∘ₗ P ∘ₗ (Ψ.symm.symm : _ →ₗ[ℝ] _) := by
    refine LinearMap.ext fun x => Ψ.injective ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
    ext a i
    simp [Ψ, P, coordEquiv, Matrix.mulVec, dotProduct]
  rw [hconj, LinearMap.det_conj, LinearMap.det_pi]
  simp

/-! ## The degree-`n` series as a degree-one theta series -/

theorem trace_cx_mul_smul (G Y : Matrix n n ℝ) (c : ℂ) :
    (cx G * (c • cx Y)).trace = ((G * Y).trace : ℝ) * c := by
  rw [Matrix.mul_smul, Matrix.trace_smul, ← cx_mul, smul_eq_mul, mul_comm]
  congr 1
  simp [cx, Matrix.trace]

/-- The degree-one theta series of the lattice `mix R (Lⁿ)` is `Θ_L(τ · Rᵀ R)`. -/
theorem thetaSeries_comap_mix (L : Submodule ℤ E) {R S : Matrix n n ℝ} (hRS : R * S = 1)
    (hSR : S * R = 1) (τ : UpperHalfPlane) :
    ZLattice.thetaSeries
        (ZLattice.comap ℝ (piLattice (n := n) L) (mixEquiv (E := E) hSR hRS).toLinearMap) τ =
      siegelTheta L ((τ : ℂ) • cx (Rᵀ * R)) := by
  let e : (n → L) ≃ ZLattice.comap ℝ (piLattice (n := n) L)
      (mixEquiv (E := E) hSR hRS).toLinearMap :=
    (piLatticeEquiv L).trans
      (ZLattice.comap_equiv ℝ (piLattice (n := n) L) (mixEquiv (E := E) hSR hRS).toLinearEquiv).toEquiv
  rw [ZLattice.thetaSeries_apply, siegelTheta, ← e.tsum_eq]
  refine tsum_congr fun x => ?_
  have he : ((e x : PiLp 2 fun _ : n => E)) = mix R (piLatticeEquiv L x : PiLp 2 fun _ : n => E) :=
    rfl
  rw [he, norm_mix_sq, thetaTerm, trace_cx_mul_smul]
  congr 1
  ring

/-! ## The inversion -/

theorem finrank_tuple : finrank ℝ (PiLp 2 fun _ : n => E) = Fintype.card n * finrank ℝ E := by
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (n → E)), Module.finrank_pi_fintype]
  simp

/-- **Inversion of the degree-`n` theta series on scalar multiples of real matrices.** For a
unimodular lattice `L` of rank `2k`, real matrices `R`, `S` inverse to each other, and `τ ∈ ℍ`:

  `Θ_L(−τ⁻¹ · Rᵀ R) = |det S|^{2k} · (−i)^{nk} τ^{nk} · Θ_L(τ · S Sᵀ)`.

Here `S Sᵀ = (Rᵀ R)⁻¹`. With `Z = τ · S Sᵀ` the right side is `det(−i Z)^k · Θ_L(Z)`. -/
theorem siegelTheta_inversion_smul {L : Submodule ℤ E} (hU : ZLattice.IsUnimodular L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {R S : Matrix n n ℝ} (hRS : R * S = 1) (hSR : S * R = 1)
    (τ : UpperHalfPlane) :
    siegelTheta L (((ModularGroup.S • τ : UpperHalfPlane) : ℂ) • cx (Rᵀ * R)) =
      ((|S.det| ^ (2 * k) : ℝ) : ℂ) *
        ((-I) ^ (Fintype.card n * k) * (τ : ℂ) ^ (Fintype.card n * k)) *
        siegelTheta L ((τ : ℂ) • cx (S * Sᵀ)) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hUn := isUnimodular_piLattice (n := n) hU
  have := hUn.isIntegral.discreteTopology
  have : IsZLattice ℝ (piLattice (n := n) L) := ⟨hUn.span_eq_top⟩
  have hfin : finrank ℝ (PiLp 2 fun _ : n => E) = 2 * (Fintype.card n * k) := by
    rw [finrank_tuple, hk]; ring
  have hRSt : Rᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, hSR, Matrix.transpose_one]
  have hSRt : Sᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  -- the dual of `mix R (Lⁿ)` is `mix Sᵀ (Lⁿ)`
  have hdual : ZLattice.dual
      (ZLattice.comap ℝ (piLattice (n := n) L) (mixEquiv (E := E) hSR hRS).toLinearMap) =
      ZLattice.comap ℝ (piLattice (n := n) L) (mixEquiv (E := E) hRSt hSRt).toLinearMap := by
    rw [ZLattice.dual_comap_continuousLinearEquiv, dual_piLattice, hU.dual_eq]
    ext y
    have hadj : ContinuousLinearMap.adjoint
        (((mixEquiv (E := E) hSR hRS).symm : (PiLp 2 fun _ : n => E) ≃L[ℝ] _) :
          (PiLp 2 fun _ : n => E) →L[ℝ] _) y = mix Rᵀ y := by
      refine ext_inner_left ℝ fun x => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ← inner_mix]
      rfl
    simp only [ZLattice.comap, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      ContinuousLinearMap.coe_coe, hadj]
    rfl
  have hcov : ZLattice.covolume
      (ZLattice.comap ℝ (piLattice (n := n) L) (mixEquiv (E := E) hSR hRS).toLinearMap) =
      (|S.det| ^ (2 * k))⁻¹ := by
    have h := ZLattice.covolume_comap_continuousLinearEquiv (piLattice (n := n) L)
      (mixEquiv (E := E) hSR hRS) MeasureTheory.volume
    rw [h, hUn.covolume_eq_one, mul_one]
    congr 1
    have : (mixEquiv (E := E) hSR hRS).toLinearMap = mix S := rfl
    rw [this, det_mix, hk, abs_pow]
  have key := ZLattice.thetaSeries_S_smul
    (ZLattice.comap ℝ (piLattice (n := n) L) (mixEquiv (E := E) hSR hRS).toLinearMap) hfin τ
  rw [thetaSeries_comap_mix, hdual, thetaSeries_comap_mix, hcov] at key
  rw [key, Matrix.transpose_transpose]
  push_cast
  rw [inv_inv]

end TauTrack.Siegel
