module

public import TauTrack.Cohomology.IntegralStructure
public import TauCeti.NumberTheory.ModularForms.BinaryForms
import Mathlib.Tactic

/-!
# The invariant pairing on binary forms and the pairing on parabolic cohomology

Over a field `K` of characteristic zero.

**The invariant pairing** `invariantPairing K w` on binary forms of degree `w` is the inverse of
TauCeti's `binaryFormDual` (a functional `φ` goes to the form whose value at `(x, y)` is
`φ((xY − yX)^w)`). So it is the pairing with the reproducing property

  `⟨P, (xY − yX)^w⟩ = P(x, y)`    (`invariantPairing_linearFormPow`).

* `invariantPairing_binaryFormRep`: `⟨P ∣ M, Q⟩ = ⟨P, Q ∣ adj M⟩` for every integer matrix `M`.
* `invariantPairing_SL`: `⟨P ∣ γ, Q ∣ γ⟩ = ⟨P, Q⟩` for `γ ∈ SL(2, ℤ)`.
* `invariantPairing_basis`: `⟨X^i Y^{w−i}, X^k Y^{w−k}⟩ = (−1)^k / C(w, k)` if `i + k = w`, else `0`.
* `invariantPairing_symm`: `⟨Q, P⟩ = (−1)^w ⟨P, Q⟩`.
* `invariantPairing_eq_zero`: it is nondegenerate.

**The bracket** `bracket K w P Q = ⟨P ∣ T − P ∣ T⁻¹, Q⟩`.

* `bracket_antisymm`: for `w` even, `{Q, P} = −{P, Q}`.
* `bracket_eisenstein`: for a period polynomial `Q`, `{Q, X^w − Y^w} = Q(1, 1) − Q(−1, 1) = 0`.

**The pairing on parabolic cohomology** `parabolicPairing hw` on `W_w ⧸ ⟨X^w − Y^w⟩`:
the bracket descends (`parabolicPairing_mk`), and it is antisymmetric
(`parabolicPairing_antisymm`).
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

variable {K : Type*} [Field K] [CharZero K] {w : ℕ}

/-! ## The invariant pairing on binary forms -/

instance instFiniteBinaryForms : Module.Finite K (homogeneousSubmodule (Fin 2) K w) :=
  Module.Finite.of_basis (TauCeti.binaryFormMonomialBasis K w)

theorem binaryFormDual_injective_field :
    Function.Injective (TauCeti.binaryFormDual K w) :=
  TauCeti.binaryFormDual_injective fun _ hj =>
    isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne')

variable (K w) in
/-- TauCeti's map from functionals to binary forms is an isomorphism in characteristic zero. -/
noncomputable def binaryFormDualEquiv :
    Module.Dual K (homogeneousSubmodule (Fin 2) K w) ≃ₗ[K] homogeneousSubmodule (Fin 2) K w :=
  LinearMap.linearEquivOfInjective (TauCeti.binaryFormDual K w) binaryFormDual_injective_field
    Subspace.dual_finrank_eq

variable (K w) in
/-- **The `SL₂`-invariant pairing on binary forms of degree `w`.** -/
noncomputable def invariantPairing :
    homogeneousSubmodule (Fin 2) K w →ₗ[K] homogeneousSubmodule (Fin 2) K w →ₗ[K] K :=
  (binaryFormDualEquiv K w).symm.toLinearMap

/-- The pairing is the inverse of `binaryFormDual`. -/
theorem binaryFormDual_invariantPairing (P : homogeneousSubmodule (Fin 2) K w) :
    TauCeti.binaryFormDual K w (invariantPairing K w P) = P :=
  (binaryFormDualEquiv K w).apply_symm_apply P

/-- **The reproducing property**: `⟨P, (xY − yX)^w⟩ = P(x, y)`. -/
theorem invariantPairing_linearFormPow (P : homogeneousSubmodule (Fin 2) K w) (v : Fin 2 → K) :
    invariantPairing K w P (TauCeti.linearFormPow K w (v 0) (v 1)) =
      eval v (P : MvPolynomial (Fin 2) K) := by
  rw [← TauCeti.eval_binaryFormDual, binaryFormDual_invariantPairing]

/-- **Nondegeneracy.** -/
theorem invariantPairing_eq_zero {P : homogeneousSubmodule (Fin 2) K w}
    (h : invariantPairing K w P = 0) : P = 0 := by
  rw [← binaryFormDual_invariantPairing P, h, map_zero]

/-- **Adjointness**: `⟨P ∣ M, Q⟩ = ⟨P, Q ∣ adj M⟩`. -/
theorem invariantPairing_binaryFormRep (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P Q : homogeneousSubmodule (Fin 2) K w) :
    invariantPairing K w (TauCeti.binaryFormRep K w (op M) P) Q =
      invariantPairing K w P (TauCeti.binaryFormRep K w (op (adjugate M)) Q) := by
  have h : invariantPairing K w (TauCeti.binaryFormRep K w (op M) P) =
      (invariantPairing K w P) ∘ₗ TauCeti.binaryFormAdjugateRep K w M := by
    apply binaryFormDual_injective_field
    rw [binaryFormDual_invariantPairing, ← TauCeti.binaryFormRep_binaryFormDual,
      binaryFormDual_invariantPairing]
  rw [h, LinearMap.comp_apply, TauCeti.binaryFormAdjugateRep_apply]

/-- **Invariance under `SL(2, ℤ)`**: `⟨P ∣ γ, Q ∣ γ⟩ = ⟨P, Q⟩`. -/
theorem invariantPairing_SL (γ : SL(2, ℤ)) (P Q : homogeneousSubmodule (Fin 2) K w) :
    invariantPairing K w (TauCeti.binaryFormRep K w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)
        (TauCeti.binaryFormRep K w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) Q) =
      invariantPairing K w P Q := by
  rw [invariantPairing_binaryFormRep, ← TauCeti.binaryFormRep_op_mul_apply]
  have h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * adjugate (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [mul_adjugate, γ.det_coe, one_smul]
  rw [h, op_one, map_one, one_apply_eq_self]

omit [CharZero K] in
/-- The coefficients of the form attached to a functional. -/
theorem repr_binaryFormDual (φ : homogeneousSubmodule (Fin 2) K w →ₗ[K] K) (j : Fin (w + 1)) :
    (TauCeti.binaryFormMonomialBasis K w).repr (TauCeti.binaryFormDual K w φ) j =
      (-1 : K) ^ (w - j) * (w.choose j : K) *
        φ (TauCeti.binaryFormMonomialBasis K w (Fin.rev j)) := by
  rw [TauCeti.binaryFormDual_apply, Module.Basis.repr_sum_self]

omit [CharZero K] in
theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : K) ^ k) * ((-1 : K) ^ k) = 1 := by
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]

/-- **The pairing on monomials**: `⟨X^i Y^{w−i}, X^k Y^{w−k}⟩` is `(−1)^k / C(w, k)` if
`i + k = w` and `0` otherwise. -/
theorem invariantPairing_basis (i k : Fin (w + 1)) :
    invariantPairing K w (TauCeti.binaryFormMonomialBasis K w i)
        (TauCeti.binaryFormMonomialBasis K w k) =
      if i = Fin.rev k then (-1 : K) ^ (k : ℕ) / (w.choose k : K) else 0 := by
  have hk : (k : ℕ) ≤ w := Nat.lt_succ_iff.mp k.2
  have h1 : w - (Fin.rev k : ℕ) = k := by rw [Fin.val_rev]; omega
  have h2 : w.choose (Fin.rev k : ℕ) = w.choose k := by
    rw [Fin.val_rev, show w + 1 - (k + 1) = w - k by omega, Nat.choose_symm hk]
  have hc : (w.choose k : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have hs := neg_one_pow_mul_self (K := K) (k : ℕ)
  have h := repr_binaryFormDual (invariantPairing K w (TauCeti.binaryFormMonomialBasis K w i))
    (Fin.rev k)
  rw [binaryFormDual_invariantPairing, Module.Basis.repr_self, Finsupp.single_apply, Fin.rev_rev,
    h1, h2] at h
  by_cases hi : i = Fin.rev k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)] at h ⊢
    rw [eq_div_iff hc]
    linear_combination (-(-1 : K) ^ (k : ℕ)) * h + (invariantPairing K w
      (TauCeti.binaryFormMonomialBasis K w i) (TauCeti.binaryFormMonomialBasis K w k) *
      (w.choose k : K)) * hs.symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)] at h ⊢
    have h3 : (-1 : K) ^ (k : ℕ) * (w.choose k : K) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc
    exact (mul_eq_zero.mp h.symm).resolve_left h3

/-- **Symmetry**: `⟨Q, P⟩ = (−1)^w ⟨P, Q⟩`. -/
theorem invariantPairing_symm (P Q : homogeneousSubmodule (Fin 2) K w) :
    invariantPairing K w Q P = (-1 : K) ^ w * invariantPairing K w P Q := by
  have key : (invariantPairing K w).flip = (-1 : K) ^ w • invariantPairing K w := by
    refine (TauCeti.binaryFormMonomialBasis K w).ext fun i =>
      (TauCeti.binaryFormMonomialBasis K w).ext fun k => ?_
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, smul_eq_mul, invariantPairing_basis]
    by_cases h : i = Fin.rev k
    · have hk : k = Fin.rev i := by rw [h, Fin.rev_rev]
      have hkw : (k : ℕ) ≤ w := Nat.lt_succ_iff.mp k.2
      have hi : (i : ℕ) = w - k := by rw [h, Fin.val_rev]; omega
      have hc : w.choose (i : ℕ) = w.choose k := by rw [hi, Nat.choose_symm hkw]
      have hw : (-1 : K) ^ w = (-1 : K) ^ (i : ℕ) * (-1 : K) ^ (k : ℕ) := by
        rw [← pow_add, hi, Nat.sub_add_cancel hkw]
      have hs := neg_one_pow_mul_self (K := K) (k : ℕ)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true hk), hc, hw]
      have hc0 : (w.choose k : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hkw).ne'
      rw [div_eq_iff hc0]
      have e : (-1 : K) ^ (i : ℕ) * (-1 : K) ^ (k : ℕ) * ((-1 : K) ^ (k : ℕ) / (w.choose k : K)) *
          (w.choose k : K) = (-1 : K) ^ (i : ℕ) * ((-1 : K) ^ (k : ℕ) * (-1 : K) ^ (k : ℕ)) := by
        field_simp
      rw [e, hs, mul_one]
    · have hk : ¬ k = Fin.rev i := fun hk => h (by rw [hk, Fin.rev_rev])
      rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false hk), mul_zero]
  have := LinearMap.congr_fun (LinearMap.congr_fun key P) Q
  simpa using this

/-! ## The bracket -/

variable (K w) in
/-- **The bracket** `{P, Q} = ⟨P ∣ T − P ∣ T⁻¹, Q⟩` on binary forms. -/
noncomputable def bracket :
    homogeneousSubmodule (Fin 2) K w →ₗ[K] homogeneousSubmodule (Fin 2) K w →ₗ[K] K :=
  (invariantPairing K w).comp
    (TauCeti.binaryFormRep K w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) -
      TauCeti.binaryFormRep K w (op ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))

theorem bracket_apply (P Q : homogeneousSubmodule (Fin 2) K w) :
    bracket K w P Q =
      invariantPairing K w (TauCeti.binaryFormRep K w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P) Q -
        invariantPairing K w
          (TauCeti.binaryFormRep K w (op ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) Q := by
  simp [bracket]

/-- **The bracket is antisymmetric** for `w` even. -/
theorem bracket_antisymm (hw : Even w) (P Q : homogeneousSubmodule (Fin 2) K w) :
    bracket K w Q P = -bracket K w P Q := by
  have h1 : adjugate (T : Matrix (Fin 2) (Fin 2) ℤ) = ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    (Matrix.SpecialLinearGroup.coe_inv T).symm
  have h2 : adjugate ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (T : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_inv, inv_inv]
  rw [bracket_apply, bracket_apply, invariantPairing_binaryFormRep, invariantPairing_binaryFormRep,
    h1, h2, invariantPairing_symm (Q := Q), invariantPairing_symm (Q := Q), hw.neg_one_pow]
  ring

/-! ## Evaluation of the action, and period polynomials at `(1, 1)` and `(−1, 1)` -/

omit [CharZero K] in
theorem eval_binaryFormRep (M : Matrix (Fin 2) (Fin 2) ℤ) (Q : homogeneousSubmodule (Fin 2) K w)
    (x y : K) :
    eval ![x, y] (TauCeti.binaryFormRep K w (op M) Q : MvPolynomial (Fin 2) K) =
      eval ![(M 0 0 : K) * x + (M 0 1 : K) * y, (M 1 0 : K) * x + (M 1 1 : K) * y]
        (Q : MvPolynomial (Fin 2) K) := by
  rw [TauCeti.coe_binaryFormRep_apply, MvPolynomial.eval_linearSubst]
  have hv : (M.map (Int.cast : ℤ → K)) *ᵥ ![x, y] =
      ![(M 0 0 : K) * x + (M 0 1 : K) * y, (M 1 0 : K) * x + (M 1 1 : K) * y] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv]

omit [CharZero K] in
theorem eval_add_eval_S {Q : homogeneousSubmodule (Fin 2) K w}
    (hQ : Q ∈ TauCeti.periodPolynomials K w) (x y : K) :
    eval ![x, y] (Q : MvPolynomial (Fin 2) K) + eval ![-y, x] (Q : MvPolynomial (Fin 2) K) = 0 := by
  have h := congrArg (fun P : homogeneousSubmodule (Fin 2) K w =>
    eval ![x, y] (P : MvPolynomial (Fin 2) K)) (TauCeti.mem_periodPolynomials_iff.mp hQ).1
  simp only [Submodule.coe_add, map_add, eval_binaryFormRep, Submodule.coe_zero, map_zero] at h
  simpa [ModularGroup.coe_S] using h

omit [CharZero K] in
theorem eval_add_eval_U {Q : homogeneousSubmodule (Fin 2) K w}
    (hQ : Q ∈ TauCeti.periodPolynomials K w) (x y : K) :
    eval ![x, y] (Q : MvPolynomial (Fin 2) K) + eval ![x - y, x] (Q : MvPolynomial (Fin 2) K) +
      eval ![-y, x - y] (Q : MvPolynomial (Fin 2) K) = 0 := by
  have h := congrArg (fun P : homogeneousSubmodule (Fin 2) K w =>
    eval ![x, y] (P : MvPolynomial (Fin 2) K)) (TauCeti.mem_periodPolynomials_iff.mp hQ).2
  simp only [Submodule.coe_add, map_add, eval_binaryFormRep, Submodule.coe_zero, map_zero] at h
  have hU : ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hU] at h
  convert h using 2 <;> simp <;> ring_nf

omit [CharZero K] in
/-- A period polynomial vanishes at `(1, 1)`. -/
theorem eval_one_one {Q : homogeneousSubmodule (Fin 2) K w}
    (hQ : Q ∈ TauCeti.periodPolynomials K w) :
    eval ![1, 1] (Q : MvPolynomial (Fin 2) K) = 0 := by
  have hU := eval_add_eval_U hQ 1 0
  have hS := eval_add_eval_S hQ 1 0
  simp only [sub_zero, neg_zero] at hU hS
  linear_combination hU - hS

omit [CharZero K] in
/-- A period polynomial vanishes at `(−1, 1)`. -/
theorem eval_neg_one_one {Q : homogeneousSubmodule (Fin 2) K w}
    (hQ : Q ∈ TauCeti.periodPolynomials K w) :
    eval ![-1, 1] (Q : MvPolynomial (Fin 2) K) = 0 := by
  have hS := eval_add_eval_S hQ 1 1
  rw [eval_one_one hQ, zero_add] at hS
  exact hS

omit [CharZero K] in
/-- `X^w − Y^w = (0·Y − 1·X)^w − (1·Y − 0·X)^w` for `w` even. -/
theorem eisensteinPeriodPolynomial_eq (hw : Even w) :
    TauCeti.eisensteinPeriodPolynomial K w =
      TauCeti.linearFormPow K w 0 1 - TauCeti.linearFormPow K w 1 0 := by
  apply Subtype.ext
  simp [TauCeti.coe_eisensteinPeriodPolynomial, hw.neg_pow]

/-- **The Eisenstein polynomial is orthogonal to the period polynomials**:
`{Q, X^w − Y^w} = Q(1, 1) − Q(−1, 1) = 0`. -/
theorem bracket_eisenstein (hw : Even w) {Q : homogeneousSubmodule (Fin 2) K w}
    (hQ : Q ∈ TauCeti.periodPolynomials K w) :
    bracket K w Q (TauCeti.eisensteinPeriodPolynomial K w) = 0 := by
  have h01 := invariantPairing_linearFormPow (K := K) (w := w)
  have e1 : ∀ R : homogeneousSubmodule (Fin 2) K w,
      invariantPairing K w R (TauCeti.linearFormPow K w 0 1) =
        eval ![0, 1] (R : MvPolynomial (Fin 2) K) := fun R => by
    simpa using invariantPairing_linearFormPow R ![0, 1]
  have e2 : ∀ R : homogeneousSubmodule (Fin 2) K w,
      invariantPairing K w R (TauCeti.linearFormPow K w 1 0) =
        eval ![1, 0] (R : MvPolynomial (Fin 2) K) := fun R => by
    simpa using invariantPairing_linearFormPow R ![1, 0]
  rw [bracket_apply, eisensteinPeriodPolynomial_eq hw, map_sub, map_sub, e1, e1, e2, e2,
    eval_binaryFormRep, eval_binaryFormRep, eval_binaryFormRep, eval_binaryFormRep]
  simp only [ModularGroup.coe_T, ModularGroup.coe_T_inv]
  have h1 := eval_one_one hQ
  have h2 := eval_neg_one_one hQ
  simp [h1, h2]

/-! ## The pairing on period polynomials and on parabolic cohomology -/

variable (K w) in
/-- The bracket restricted to period polynomials. -/
noncomputable def periodPairing : PeriodSpace K w →ₗ[K] PeriodSpace K w →ₗ[K] K :=
  (bracket K w).compl₁₂ (periodIncl K w) (periodIncl K w)

theorem periodPairing_apply (P Q : PeriodSpace K w) :
    periodPairing K w P Q = bracket K w (periodIncl K w P) (periodIncl K w Q) :=
  rfl

theorem periodPairing_antisymm (hw : Even w) (P Q : PeriodSpace K w) :
    periodPairing K w Q P = -periodPairing K w P Q :=
  bracket_antisymm hw _ _

omit [CharZero K] in
theorem periodIncl_mem (P : PeriodSpace K w) : periodIncl K w P ∈ TauCeti.periodPolynomials K w :=
  (periodSpaceEquiv K w P).2

/-- `X^w − Y^w` is in the right radical of the pairing on period polynomials. -/
theorem periodPairing_eisenstein_right (hw : Even w) (P : PeriodSpace K w) :
    periodPairing K w P ((periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) = 0 :=
  bracket_eisenstein hw (periodIncl_mem P)

/-- `X^w − Y^w` is in the left radical of the pairing on period polynomials. -/
theorem periodPairing_eisenstein_left (hw : Even w) (Q : PeriodSpace K w) :
    periodPairing K w ((periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) Q = 0 := by
  rw [periodPairing_antisymm hw, periodPairing_eisenstein_right, neg_zero]

/-- **The pairing on parabolic cohomology** `W_w ⧸ ⟨X^w − Y^w⟩`. -/
noncomputable def parabolicPairing (hw : Even w) :
    (PeriodSpace K w ⧸ K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) →ₗ[K]
      (PeriodSpace K w ⧸ K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) →ₗ[K] K :=
  ((K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)).liftQ
    ((K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)).liftQ (periodPairing K w) (by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact LinearMap.ext fun Q => periodPairing_eisenstein_left hw Q)).flip (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact periodPairing_eisenstein_right hw P)).flip

@[simp]
theorem parabolicPairing_mk (hw : Even w) (P Q : PeriodSpace K w) :
    parabolicPairing hw (Submodule.Quotient.mk P) (Submodule.Quotient.mk Q) =
      periodPairing K w P Q :=
  rfl

/-- **The pairing on parabolic cohomology is antisymmetric.** -/
theorem parabolicPairing_antisymm (hw : Even w)
    (x y : PeriodSpace K w ⧸ K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) :
    parabolicPairing hw y x = -parabolicPairing hw x y := by
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [parabolicPairing_mk, parabolicPairing_mk, periodPairing_antisymm hw]

end TauTrack.Cohomology
