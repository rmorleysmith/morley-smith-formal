module

public import TauTrack.Siegel.DegreeOne
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.Algebra.Module.ZLattice.Summable
public import TauCeti.Algebra.Module.ZLattice.OrthSum
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# The theta series of a lattice in degree `n`

For a lattice `L` in a Euclidean space and a tuple `x = (x_i)_{i ∈ n}` of vectors of `L`, write
`G(x) = (⟪x_i, x_j⟫)` for the Gram matrix. The theta series of `L` in degree `n` is

  `Θ_L^{(n)}(Z) = ∑_{x ∈ Lⁿ} exp(π i · tr(G(x) Z))`.

* `siegelTheta L Z`: the series, as a function of a complex matrix `Z`.
* `summable_norm_thetaTerm`: absolute convergence when `Im Z` is positive definite.
* `norm_siegelTheta_le`: a bound depending only on `c`, on the region `Im Z ≥ c · 1`.
* `siegelTheta_add_int`: for an even lattice, `Θ(Z + S) = Θ(Z)` for `S` symmetric integral.
* `siegelTheta_conj_int`: `Θ(U Z Uᵀ) = Θ(Z)` for `U` in `GL(n, ℤ)`.
* `siegelTheta_fromBlocks`: `Θ^{(n+m)}(diag(Z₁, Z₂)) = Θ^{(n)}(Z₁) · Θ^{(m)}(Z₂)`.
* `siegelTheta_orthSum`: `Θ_{L ⊕ M}(Z) = Θ_L(Z) · Θ_M(Z)` in every degree.
* `siegelTheta_m1`: in degree one this is the theta series `ZLattice.thetaSeries`.
-/

@[expose] public section

open Matrix Complex
open scoped Real RealInnerProductSpace ComplexOrder MatrixOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The series -/

/-- The Gram matrix `(⟪x_i, x_j⟫)` of a tuple of lattice vectors. -/
noncomputable def gramL {L : Submodule ℤ E} (x : n → L) : Matrix n n ℝ :=
  gram ℝ fun i => (x i : E)

@[simp] theorem gramL_apply {L : Submodule ℤ E} (x : n → L) (i j : n) :
    gramL x i j = ⟪(x i : E), (x j : E)⟫ := rfl

theorem posSemidef_gramL {L : Submodule ℤ E} (x : n → L) : (gramL x).PosSemidef :=
  posSemidef_gram ℝ _

theorem trace_gramL {L : Submodule ℤ E} (x : n → L) : (gramL x).trace = ∑ i, ‖(x i : E)‖ ^ 2 := by
  simp [Matrix.trace]

/-- The term `exp(π i · tr(G(x) Z))` of the theta series. -/
noncomputable def thetaTerm {L : Submodule ℤ E} (x : n → L) (Z : Matrix n n ℂ) : ℂ :=
  cexp (π * I * (cx (gramL x) * Z).trace)

/-- The theta series of `L` in degree `n`: `Θ(Z) = ∑_{x ∈ Lⁿ} exp(π i · tr(G(x) Z))`. -/
noncomputable def siegelTheta (L : Submodule ℤ E) (Z : Matrix n n ℂ) : ℂ :=
  ∑' x : n → L, thetaTerm x Z

/-! ## Convergence -/

theorem im_trace_cx_mul (G : Matrix n n ℝ) (Z : Matrix n n ℂ) :
    ((cx G * Z).trace).im = (G * Z.map Complex.im).trace := by
  simp [Matrix.trace, Matrix.mul_apply, cx]

theorem norm_thetaTerm {L : Submodule ℤ E} (x : n → L) (Z : Matrix n n ℂ) :
    ‖thetaTerm x Z‖ = Real.exp (-π * (gramL x * Z.map Complex.im).trace) := by
  rw [thetaTerm, Complex.norm_exp, ← im_trace_cx_mul]
  congr 1
  simp [mul_assoc]

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef {G P : Matrix n n ℝ} (hG : G.PosSemidef)
    (hP : P.PosSemidef) : 0 ≤ (G * P).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  have h : (G * (star B * B)).trace = (B * G * Bᴴ).trace := by
    rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h]
  exact (hG.mul_mul_conjTranspose_same B).trace_nonneg

/-- On the region `Im Z ≥ c · 1`: `tr(G(x) · Im Z) ≥ c · ∑ ‖x_i‖²`. -/
theorem le_trace_gramL_mul {L : Submodule ℤ E} (x : n → L) {Y : Matrix n n ℝ} {c : ℝ}
    (hY : (Y - c • (1 : Matrix n n ℝ)).PosSemidef) :
    c * ∑ i, ‖(x i : E)‖ ^ 2 ≤ (gramL x * Y).trace := by
  have h := trace_mul_nonneg_of_posSemidef (posSemidef_gramL x) hY
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_gramL, smul_eq_mul] at h
  linarith

/-- The Gaussian majorant of the terms on the region `Im Z ≥ c · 1`. -/
theorem norm_thetaTerm_le {L : Submodule ℤ E} (x : n → L) {Z : Matrix n n ℂ} {c : ℝ}
    (hZ : (Z.map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef) :
    ‖thetaTerm x Z‖ ≤ ∏ i, Real.exp (-(π * c) * ‖(0 : E) + (x i : E)‖ ^ 2) := by
  rw [norm_thetaTerm, ← Real.exp_sum, Real.exp_le_exp]
  have h := le_trace_gramL_mul x hZ
  simp only [zero_add, ← Finset.mul_sum]
  nlinarith [Real.pi_pos]

/-- A product of summable nonnegative families is summable over the product index. -/
theorem summable_pi_prod {α : Type*} {f : n → α → ℝ} (h0 : ∀ i a, 0 ≤ f i a)
    (hf : ∀ i, Summable (f i)) : Summable fun x : n → α => ∏ i, f i (x i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' a, f i a)
    (fun x => Finset.prod_nonneg fun i _ => h0 i (x i)) fun s => ?_
  calc ∑ x ∈ s, ∏ i, f i (x i)
      ≤ ∑ x ∈ Fintype.piFinset fun i => s.image fun x => x i, ∏ i, f i (x i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_)
          fun x _ _ => Finset.prod_nonneg fun i _ => h0 i (x i)
        exact Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hx
    _ = ∏ i, ∑ a ∈ s.image fun x => x i, f i a := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' a, f i a := by
        apply Finset.prod_le_prod₀
        · exact fun i _ => Finset.sum_nonneg fun a _ => h0 i a
        · exact fun i _ => (hf i).sum_le_tsum _ fun a _ => h0 i a

variable [FiniteDimensional ℝ E]

/-- The Gaussian majorant is summable over `Lⁿ`. -/
theorem summable_majorant (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable fun x : n → L => ∏ i, Real.exp (-(π * c) * ‖(0 : E) + (x i : E)‖ ^ 2) := by
  have h := ZLattice.summable_exp_neg_mul_norm_add_sq L (mul_pos Real.pi_pos hc) 0
  exact summable_pi_prod (f := fun _ (v : L) => Real.exp (-(π * c) * ‖(0 : E) + (v : E)‖ ^ 2))
    (fun _ _ => (Real.exp_pos _).le) fun _ => h

/-- A positive definite real matrix dominates a positive multiple of the identity. -/
theorem exists_pos_posDef_sub {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (Y - c • (1 : Matrix n n ℝ)).PosDef := by
  have hsa : ∀ c : ℝ, Y - c • (1 : Matrix n n ℝ) ∈ selfAdjoint (Matrix n n ℝ) := fun c => by
    rw [selfAdjoint.mem_iff, star_sub, star_smul, star_one]
    congr 1
    exact hY.isHermitian
  let g : ℝ → selfAdjoint (Matrix n n ℝ) := fun c => ⟨Y - c • (1 : Matrix n n ℝ), hsa c⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have ho : IsOpen (g ⁻¹' {A : selfAdjoint (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef}) :=
    Matrix.isOpen_setOfPred_posDef_selfAdjoint.preimage hg
  have h0 : (0 : ℝ) ∈ g ⁻¹' {A : selfAdjoint (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef} := by
    simpa [g] using hY
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨ε / 2, half_pos hε, ?_⟩
  have : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact hball this

theorem exists_pos_posSemidef_sub {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (Y - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, h⟩ := exists_pos_posDef_sub hY
  exact ⟨c, hc, h.posSemidef⟩

/-- The theta series converges absolutely when `Im Z` is positive definite. -/
theorem summable_norm_thetaTerm (L : Submodule ℤ E) [DiscreteTopology L] {Z : Matrix n n ℂ}
    (hZ : (Z.map Complex.im).PosDef) : Summable fun x : n → L => ‖thetaTerm x Z‖ := by
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub hZ
  exact .of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_thetaTerm_le x hP)
    (summable_majorant L hc)

theorem summable_thetaTerm (L : Submodule ℤ E) [DiscreteTopology L] {Z : Matrix n n ℂ}
    (hZ : (Z.map Complex.im).PosDef) : Summable fun x : n → L => thetaTerm x Z :=
  (summable_norm_thetaTerm L hZ).of_norm

/-- On the region `Im Z ≥ c · 1` with `c > 0` the theta series is bounded by a constant that
depends only on `c`. -/
theorem norm_siegelTheta_le (L : Submodule ℤ E) [DiscreteTopology L] {Z : Matrix n n ℂ} {c : ℝ}
    (hc : 0 < c) (hZ : (Z.map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef) :
    ‖siegelTheta L Z‖ ≤
      ∑' x : n → L, ∏ i, Real.exp (-(π * c) * ‖(0 : E) + (x i : E)‖ ^ 2) :=
  tsum_of_norm_bounded (summable_majorant L hc).hasSum fun x => norm_thetaTerm_le x hZ

/-! ## Translation by a symmetric integral matrix -/

/-- A sum `∑ B_ij g_ij` with `B`, `g` symmetric integral and `g` even on the diagonal is even. -/
theorem even_sum_mul_of_isSymm {B g : Matrix n n ℤ} (hB : B.IsSymm) (hg : g.IsSymm)
    (hd : ∀ i, Even (g i i)) : Even (∑ i, ∑ j, B i j * g i j) := by
  rw [← Finset.sum_product', even_iff_two_dvd]
  suffices key : ((∑ p ∈ Finset.univ ×ˢ Finset.univ, B p.1 p.2 * g p.1 p.2 : ℤ) : ZMod 2) = 0 by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp key
  rw [Int.cast_sum]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp hswap => hp ?_)
    (fun p _ => by simp) (fun p _ => by simp)
  · have e : B p.swap.1 p.swap.2 * g p.swap.1 p.swap.2 = B p.1 p.2 * g p.1 p.2 := by
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [← hB.apply, ← hg.apply]
    rw [e]
    exact CharTwo.add_self_eq_zero _
  · have hp' : p.2 = p.1 := congrArg Prod.fst hswap
    rw [hp']
    obtain ⟨r, hr⟩ := hd p.1
    rw [hr, Int.cast_mul, Int.cast_add, CharTwo.add_self_eq_zero, mul_zero]

/-- For an even lattice the Gram matrix of a tuple is integral, symmetric and even on the
diagonal. -/
theorem exists_int_gramL {L : Submodule ℤ E} (hL : ZLattice.IsEven L) (x : n → L) :
    ∃ g : Matrix n n ℤ, g.IsSymm ∧ (∀ i, Even (g i i)) ∧ gramL x = g.map (Int.cast : ℤ → ℝ) := by
  have hint := ZLattice.isIntegral_iff.mp hL.isIntegral
  choose g hg using fun i j => hint (x i) (x i).2 (x j) (x j).2
  refine ⟨Matrix.of g, ?_, fun i => ?_, ?_⟩
  · ext i j
    have h1 := hg i j
    have h2 := hg j i
    rw [real_inner_comm] at h2
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact_mod_cast h2.symm.trans h1
  · obtain ⟨r, hr⟩ := ZLattice.isEven_iff.mp hL (x i) (x i).2
    have h1 := hg i i
    rw [real_inner_self_eq_norm_sq, hr] at h1
    have : g i i = 2 * r := by exact_mod_cast h1.symm
    exact ⟨r, by simp only [Matrix.of_apply]; omega⟩
  · ext i j
    simp [hg i j]

/-- For an even lattice, each term is unchanged by `Z ↦ Z + S`, `S` symmetric integral. -/
theorem thetaTerm_add_int {L : Submodule ℤ E} (hL : ZLattice.IsEven L) (x : n → L)
    (Z : Matrix n n ℂ) {S : Matrix n n ℤ} (hS : S.IsSymm) :
    thetaTerm x (Z + S.map (Int.cast : ℤ → ℂ)) = thetaTerm x Z := by
  obtain ⟨g, hg, hd, hG⟩ := exists_int_gramL hL x
  obtain ⟨r, hr⟩ := even_sum_mul_of_isSymm hS hg hd
  have htr : (cx (gramL x) * S.map (Int.cast : ℤ → ℂ)).trace = ((r + r : ℤ) : ℂ) := by
    rw [← hr, hG]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, cx, Matrix.map_apply,
      Int.cast_sum, Int.cast_mul, Complex.ofReal_intCast]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [← hg.apply j i, mul_comm]
  rw [thetaTerm, thetaTerm, Matrix.mul_add, Matrix.trace_add, htr, mul_add, Complex.exp_add]
  have : cexp (π * I * ((r + r : ℤ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨r, by push_cast; ring⟩
  rw [this, mul_one]

/-- **Translation.** For an even lattice, `Θ(Z + S) = Θ(Z)` for `S` symmetric integral. -/
theorem siegelTheta_add_int {L : Submodule ℤ E} (hL : ZLattice.IsEven L) (Z : Matrix n n ℂ)
    {S : Matrix n n ℤ} (hS : S.IsSymm) :
    siegelTheta L (Z + S.map (Int.cast : ℤ → ℂ)) = siegelTheta L Z :=
  tsum_congr fun x => thetaTerm_add_int hL x Z hS

/-! ## Change of basis by `GL(n, ℤ)` -/

/-- The tuple `x U`, with `(x U)_j = ∑_i U_ij x_i`. -/
def tupleMul {L : Submodule ℤ E} (x : n → L) (U : Matrix n n ℤ) : n → L :=
  fun j => ∑ i, U i j • x i

theorem tupleMul_mul {L : Submodule ℤ E} (x : n → L) (U V : Matrix n n ℤ) :
    tupleMul (tupleMul x U) V = tupleMul x (U * V) := by
  funext j
  simp only [tupleMul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem tupleMul_one {L : Submodule ℤ E} (x : n → L) : tupleMul x 1 = x := by
  funext j
  simp [tupleMul, Matrix.one_apply, ite_smul]

/-- For `U V = V U = 1`, right multiplication by `U` is a bijection of `Lⁿ`. -/
def tupleEquiv (L : Submodule ℤ E) {U V : Matrix n n ℤ} (hUV : U * V = 1) (hVU : V * U = 1) :
    (n → L) ≃ (n → L) where
  toFun x := tupleMul x U
  invFun x := tupleMul x V
  left_inv x := by
    change tupleMul (tupleMul x U) V = x
    rw [tupleMul_mul, hUV, tupleMul_one]
  right_inv x := by
    change tupleMul (tupleMul x V) U = x
    rw [tupleMul_mul, hVU, tupleMul_one]

theorem gramL_tupleMul {L : Submodule ℤ E} (x : n → L) (U : Matrix n n ℤ) :
    gramL (tupleMul x U) =
      (U.map (Int.cast : ℤ → ℝ))ᵀ * gramL x * U.map (Int.cast : ℤ → ℝ) := by
  ext j l
  simp only [gramL_apply, tupleMul, Submodule.coe_sum, Submodule.coe_smul,
    ← Int.cast_smul_eq_zsmul ℝ, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conj_trivial, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cx_map_intCast (U : Matrix n n ℤ) :
    cx (U.map (Int.cast : ℤ → ℝ)) = U.map (Int.cast : ℤ → ℂ) := by
  ext i j; simp [cx]

theorem thetaTerm_tupleMul {L : Submodule ℤ E} (x : n → L) (U : Matrix n n ℤ)
    (Z : Matrix n n ℂ) :
    thetaTerm (tupleMul x U) Z =
      thetaTerm x (U.map (Int.cast : ℤ → ℂ) * Z * (U.map (Int.cast : ℤ → ℂ))ᵀ) := by
  rw [thetaTerm, thetaTerm, gramL_tupleMul, cx_mul, cx_mul, cx_transpose, cx_map_intCast]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **Change of basis.** `Θ(U Z Uᵀ) = Θ(Z)` for `U` in `GL(n, ℤ)`. -/
theorem siegelTheta_conj_int (L : Submodule ℤ E) {U V : Matrix n n ℤ} (hUV : U * V = 1)
    (hVU : V * U = 1) (Z : Matrix n n ℂ) :
    siegelTheta L (U.map (Int.cast : ℤ → ℂ) * Z * (U.map (Int.cast : ℤ → ℂ))ᵀ) =
      siegelTheta L Z := by
  unfold siegelTheta
  rw [← (tupleEquiv L hUV hVU).tsum_eq fun x => thetaTerm x Z]
  exact tsum_congr fun x => (thetaTerm_tupleMul x U Z).symm

/-! ## The product formula on block diagonal matrices -/

theorem thetaTerm_fromBlocks {L : Submodule ℤ E} (x : n → L) (y : m → L) (Z₁ : Matrix n n ℂ)
    (Z₂ : Matrix m m ℂ) :
    thetaTerm (Sum.elim x y) (Matrix.fromBlocks Z₁ 0 0 Z₂) = thetaTerm x Z₁ * thetaTerm y Z₂ := by
  rw [thetaTerm, thetaTerm, thetaTerm, ← Complex.exp_add, ← mul_add]
  congr 2
  simp [Matrix.trace, Matrix.mul_apply, cx, Fintype.sum_sum_type]

/-- **The product formula.** On block diagonal matrices the theta series of degree `n + m` is
the product of the theta series of degrees `n` and `m`:
`Θ(diag(Z₁, Z₂)) = Θ(Z₁) · Θ(Z₂)`. -/
theorem siegelTheta_fromBlocks (L : Submodule ℤ E) [DiscreteTopology L] {Z₁ : Matrix n n ℂ}
    {Z₂ : Matrix m m ℂ} (h₁ : (Z₁.map Complex.im).PosDef) (h₂ : (Z₂.map Complex.im).PosDef) :
    siegelTheta L (Matrix.fromBlocks Z₁ 0 0 Z₂) = siegelTheta L Z₁ * siegelTheta L Z₂ := by
  unfold siegelTheta
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_thetaTerm L h₁) (summable_norm_thetaTerm L h₂),
    ← (Equiv.sumArrowEquivProdArrow n m L).symm.tsum_eq]
  exact tsum_congr fun p => thetaTerm_fromBlocks p.1 p.2 Z₁ Z₂

/-! ## Orthogonal sums of lattices -/

/-- **Orthogonal sums.** The theta series of an orthogonal direct sum of lattices is the product
of the theta series of the summands, in every degree: `Θ_{L ⊕ M}(Z) = Θ_L(Z) · Θ_M(Z)`. -/
theorem siegelTheta_orthSum {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (L : Submodule ℤ E) [DiscreteTopology L] (M : Submodule ℤ F)
    [DiscreteTopology M] {Z : Matrix n n ℂ} (hZ : (Z.map Complex.im).PosDef) :
    siegelTheta (ZLattice.orthSum L M) Z = siegelTheta L Z * siegelTheta M Z := by
  unfold siegelTheta
  let e : (n → L) × (n → M) ≃ (n → ZLattice.orthSum L M) :=
    (Equiv.arrowProdEquivProdArrow n (fun _ => L) (fun _ => M)).symm.trans
      (Equiv.piCongrRight fun _ => (ZLattice.orthSumEquivProd L M).symm.toEquiv)
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_thetaTerm L hZ)
    (summable_norm_thetaTerm M hZ), ← e.tsum_eq]
  refine tsum_congr fun p => ?_
  have hG : gramL (e p) = gramL p.1 + gramL p.2 := by
    ext i j
    simp [e, WithLp.prod_inner_apply]
  rw [thetaTerm, thetaTerm, thetaTerm, hG, cx_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.exp_add]

/-! ## Degree one -/

/-- In degree one the series is the theta series of the lattice. -/
theorem siegelTheta_m1 (L : Submodule ℤ E) (τ : UpperHalfPlane) :
    siegelTheta L (DegreeOne.m1 (τ : ℂ)) = ZLattice.thetaSeries L τ := by
  unfold siegelTheta
  rw [ZLattice.thetaSeries_apply, ← (Equiv.funUnique (Fin 1) L).symm.tsum_eq]
  refine tsum_congr fun v => ?_
  simp only [thetaTerm, Matrix.trace, Matrix.mul_apply, cx, Matrix.diag_apply, Matrix.map_apply,
    gramL_apply, DegreeOne.m1_apply, Finset.univ_unique, Finset.sum_singleton,
    real_inner_self_eq_norm_sq]
  congr 1
  simp [mul_assoc]

end TauTrack.Siegel
