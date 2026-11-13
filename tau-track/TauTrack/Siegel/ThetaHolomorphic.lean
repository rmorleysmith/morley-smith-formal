module

public import TauTrack.Siegel.Theta
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The theta series of a lattice in degree `n` is holomorphic and bounded at infinity

* `differentiableOn_siegelTheta`: `X ↦ Θ_L(X)` is complex differentiable on the open set of
  square matrices whose symmetric part lies in `ℍ_n`.
* `isHolomorphic_siegelTheta`, `isBoundedAtInfinity_siegelTheta`: the two analytic conditions in
  the definition of a Siegel modular form, for `Z ↦ Θ_L(Z)`.

The series is differentiated term by term (Mathlib `hasFDerivAt_tsum_of_isPreconnected`); the
derivative of the term of index `x` is the term times `π i · tr(G(x) ·)`, of norm at most
`π · |n| · t · exp(-π c t)` with `t = ∑ ‖x_i‖²`, on a region `Im Z ≥ c · 1`.
-/

@[expose] public section

open Matrix Complex
open scoped Real RealInnerProductSpace ComplexOrder MatrixOrder

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The series only sees the symmetric part -/

theorem gramL_transpose {L : Submodule ℤ E} (x : n → L) : (gramL x)ᵀ = gramL x := by
  ext i j; simp [real_inner_comm]

theorem thetaTerm_symPart {L : Submodule ℤ E} (x : n → L) (X : Matrix n n ℂ) :
    thetaTerm x (symPart X) = thetaTerm x X := by
  have h : (cx (gramL x) * Xᵀ).trace = (cx (gramL x) * X).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← cx_transpose, gramL_transpose, Matrix.trace_mul_comm]
  rw [thetaTerm, thetaTerm, symPart, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add,
    Matrix.trace_add, h, smul_eq_mul]
  congr 1
  ring

theorem siegelTheta_symPart (L : Submodule ℤ E) (X : Matrix n n ℂ) :
    siegelTheta L (symPart X) = siegelTheta L X :=
  tsum_congr fun x => thetaTerm_symPart x X

/-! ## The linear functional `X ↦ tr(G X)` -/

/-- `X ↦ tr(G X)` as a continuous linear functional on `n → n → ℂ`. -/
noncomputable def trL (G : Matrix n n ℝ) : (n → n → ℂ) →L[ℂ] ℂ :=
  ∑ i, ∑ j, (G i j : ℂ) •
    ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj j : (n → n → ℂ) →L[ℂ] (n → ℂ)))

theorem trL_apply' (G : Matrix n n ℝ) (X : n → n → ℂ) :
    trL G X = ∑ i, ∑ j, (G i j : ℂ) * X j i := by
  simp [trL]

theorem trL_apply (G : Matrix n n ℝ) (X : n → n → ℂ) :
    trL G X = (cx G * Matrix.of X).trace := by
  simp [trL_apply', Matrix.trace, Matrix.mul_apply, cx]

theorem norm_trL_le (G : Matrix n n ℝ) : ‖trL G‖ ≤ ∑ i, ∑ j, |G i j| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) fun X => ?_
  rw [trL_apply', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (X j) i).trans (norm_le_pi_norm X j))
    (abs_nonneg _)

theorem sum_abs_gramL_le {L : Submodule ℤ E} (x : n → L) :
    ∑ i, ∑ j, |gramL x i j| ≤ Fintype.card n * ∑ i, ‖(x i : E)‖ ^ 2 := by
  have h : ∀ i j, |gramL x i j| ≤ (‖(x i : E)‖ ^ 2 + ‖(x j : E)‖ ^ 2) / 2 := fun i j => by
    have h1 := abs_real_inner_le_norm (x i : E) (x j : E)
    rw [gramL_apply]
    nlinarith [sq_nonneg (‖(x i : E)‖ - ‖(x j : E)‖)]
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j).trans (le_of_eq ?_)
  simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-! ## The terms as functions on `n → n → ℂ` -/

/-- The term of index `x`, as a function on `n → n → ℂ`. -/
noncomputable def tf {L : Submodule ℤ E} (x : n → L) (X : n → n → ℂ) : ℂ :=
  cexp (π * I * trL (gramL x) X)

theorem tf_eq {L : Submodule ℤ E} (x : n → L) (X : n → n → ℂ) :
    tf x X = thetaTerm x (Matrix.of X) := by
  rw [tf, trL_apply, thetaTerm]

theorem hasFDerivAt_tf {L : Submodule ℤ E} (x : n → L) (X : n → n → ℂ) :
    HasFDerivAt (tf x) (tf x X • ((π * I : ℂ) • trL (gramL x))) X :=
  (((trL (gramL x)).hasFDerivAt).const_mul (π * I : ℂ)).cexp

theorem prod_exp_eq {L : Submodule ℤ E} (x : n → L) (a : ℝ) :
    ∏ i, Real.exp (-a * ‖(0 : E) + (x i : E)‖ ^ 2) = Real.exp (-a * ∑ i, ‖(x i : E)‖ ^ 2) := by
  rw [← Real.exp_sum, Finset.mul_sum]
  simp

theorem norm_tf_le {L : Submodule ℤ E} (x : n → L) {X : n → n → ℂ} {c : ℝ}
    (hX : ((symPart (Matrix.of X)).map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef) :
    ‖tf x X‖ ≤ Real.exp (-(π * c) * ∑ i, ‖(x i : E)‖ ^ 2) := by
  rw [tf_eq, ← thetaTerm_symPart, ← prod_exp_eq]
  exact norm_thetaTerm_le x hX

/-- `t · exp(-2bt) ≤ b⁻¹ · exp(-bt)`. -/
theorem mul_exp_neg_le {b : ℝ} (hb : 0 < b) (t : ℝ) :
    t * Real.exp (-(2 * b) * t) ≤ b⁻¹ * Real.exp (-b * t) := by
  have h1 : b * t + 1 ≤ Real.exp (b * t) := Real.add_one_le_exp _
  have h2 : Real.exp (-(2 * b) * t) = Real.exp (-b * t) * Real.exp (-(b * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(b * t)) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-(b * t)) := Real.exp_pos _
  have h5 : t * Real.exp (-(b * t)) ≤ b⁻¹ := by
    have : b * t * Real.exp (-(b * t)) ≤ Real.exp (b * t) * Real.exp (-(b * t)) :=
      mul_le_mul_of_nonneg_right (by linarith) h4.le
    rw [mul_comm (Real.exp (b * t)), h3] at this
    rw [← one_div, le_div_iff₀ hb]
    linarith
  rw [h2]
  calc t * (Real.exp (-b * t) * Real.exp (-(b * t)))
      = (t * Real.exp (-(b * t))) * Real.exp (-b * t) := by ring
    _ ≤ b⁻¹ * Real.exp (-b * t) := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le

theorem norm_fderiv_tf_le {L : Submodule ℤ E} (x : n → L) {X : n → n → ℂ} {c : ℝ} (hc : 0 < c)
    (hX : ((symPart (Matrix.of X)).map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef) :
    ‖tf x X • ((π * I : ℂ) • trL (gramL x))‖ ≤
      (π * Fintype.card n * (π * (c / 2))⁻¹) *
        ∏ i, Real.exp (-(π * (c / 2)) * ‖(0 : E) + (x i : E)‖ ^ 2) := by
  set t := ∑ i, ‖(x i : E)‖ ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => by positivity
  have h1 := norm_tf_le x hX
  have h2 : ‖trL (gramL x)‖ ≤ Fintype.card n * t :=
    (norm_trL_le _).trans (sum_abs_gramL_le x)
  have h3 := mul_exp_neg_le (b := π * (c / 2)) (by positivity) t
  have h4 : -(2 * (π * (c / 2))) * t = -(π * c) * t := by ring
  rw [h4] at h3
  rw [prod_exp_eq, norm_smul, norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hn : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  calc ‖tf x X‖ * (π * ‖trL (gramL x)‖)
      ≤ Real.exp (-(π * c) * t) * (π * (Fintype.card n * t)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 Real.pi_pos.le) (by positivity)
          (Real.exp_pos _).le
    _ = π * Fintype.card n * (t * Real.exp (-(π * c) * t)) := by ring
    _ ≤ π * Fintype.card n * ((π * (c / 2))⁻¹ * Real.exp (-(π * (c / 2)) * t)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-! ## Holomorphy -/

variable [FiniteDimensional ℝ E]

/-- The theta series is complex differentiable on the set of square matrices whose symmetric
part lies in `ℍ_n`. -/
theorem differentiableOn_siegelTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    DifferentiableOn ℂ (fun X : n → n → ℂ => siegelTheta L (Matrix.of X)) (domain n) := by
  intro X₀ hX₀
  obtain ⟨c, hc, hP⟩ := exists_pos_posDef_sub hX₀.2
  let g : (n → n → ℂ) → selfAdjoint (Matrix n n ℝ) := fun X => imSym X - c • 1
  have hg : Continuous g := continuous_imSym.sub continuous_const
  have ho : IsOpen (g ⁻¹' {A : selfAdjoint (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef}) :=
    Matrix.isOpen_setOfPred_posDef_selfAdjoint.preimage hg
  have hmem : ∀ X, X ∈ g ⁻¹' {A : selfAdjoint (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef} ↔
      ((symPart (Matrix.of X)).map Complex.im - c • (1 : Matrix n n ℝ)).PosDef := fun X => by
    simp [g, imSym]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho X₀ ((hmem X₀).mpr hP)
  have hfun : (fun X : n → n → ℂ => siegelTheta L (Matrix.of X)) = fun X => ∑' x : n → L, tf x X := by
    funext X
    exact tsum_congr fun x => (tf_eq x X).symm
  rw [hfun]
  have hf0 : Summable fun x : n → L => tf x X₀ := by
    have h := summable_thetaTerm L hX₀.2
    refine h.congr fun x => ?_
    rw [tf_eq, thetaTerm_symPart]
  exact (hasFDerivAt_tsum_of_isPreconnected
    ((summable_majorant L (half_pos hc)).mul_left (π * Fintype.card n * (π * (c / 2))⁻¹))
    Metric.isOpen_ball (convex_ball X₀ r).isPreconnected
    (fun x X _ => hasFDerivAt_tf x X)
    (fun x X hX => norm_fderiv_tf_le x hc ((hmem X).mp (hball hX)).posSemidef)
    (Metric.mem_ball_self hr) hf0 (Metric.mem_ball_self hr)).differentiableAt.differentiableWithinAt

/-- `Z ↦ Θ_L(Z)` is holomorphic on `ℍ_n`. -/
theorem isHolomorphic_siegelTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    IsHolomorphic fun Z : SiegelUpperHalfSpace n => siegelTheta L Z.1 := by
  refine (differentiableOn_siegelTheta L).congr fun X hX => ?_
  rw [extend_apply hX]
  exact siegelTheta_symPart L _

/-- `Z ↦ Θ_L(Z)` is bounded at infinity. -/
theorem isBoundedAtInfinity_siegelTheta (L : Submodule ℤ E) [DiscreteTopology L] :
    IsBoundedAtInfinity fun Z : SiegelUpperHalfSpace n => siegelTheta L Z.1 :=
  ⟨1, _, fun _ hZ => norm_siegelTheta_le L one_pos hZ⟩

end TauTrack.Siegel
