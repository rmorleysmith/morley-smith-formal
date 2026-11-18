module

public import TauTrack.Cohomology.LatticePairing
import Mathlib.Tactic

/-!
# The pairing on `H¹_par(SL(2, ℤ), V₁₀)`: the two period polynomials of `Δ`

Over a field `K` of characteristic zero, in degree `w = 10`:

* `deltaEven K = X²Y²(X² − Y²)³` and
  `deltaOdd K = 43545600 · (4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹)`
  are period polynomials (`deltaEven_mem`, `deltaOdd_mem`). They are the even and odd period
  polynomials of `Δ` up to scalars (numerically; not proved here). `deltaOdd` is defined as an
  integer combination of tenth powers of linear forms, so that the reproducing property of the
  invariant pairing computes brackets with it.
* `bracket_deltaEven_deltaOdd`: `{deltaEven, deltaOdd} = −6 · 43545600`.
* `parabolicPairing_ten_nondegenerate`: **the pairing on `H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)` is
  nondegenerate.**
* `latticePairing_delta`: on the lattice, the integral pairing of the two classes is
  `10! · (−6 · 43545600)`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

variable (K : Type*) [Field K] [CharZero K]

/-- `X²Y²(X² − Y²)³`, a binary form of degree `10`. -/
noncomputable def deltaEven : homogeneousSubmodule (Fin 2) K 10 :=
  ⟨X 0 ^ 2 * X 1 ^ 2 * (X 0 ^ 2 - X 1 ^ 2) ^ 3,
    ((isHomogeneous_X_pow 0 2).mul (isHomogeneous_X_pow 1 2)).mul
      (((isHomogeneous_X_pow 0 2).sub (isHomogeneous_X_pow 1 2)).pow 3)⟩

/-- `43545600 · (4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹)`, written as an integer combination of
tenth powers of the linear forms `Y ∓ tX`, `t = 1, …, 5`. -/
noncomputable def deltaOdd : homogeneousSubmodule (Fin 2) K 10 :=
  (-18456438 : K) • (TauCeti.linearFormPow K 10 1 1 - TauCeti.linearFormPow K 10 1 (-1)) +
    (7193472 : K) • (TauCeti.linearFormPow K 10 1 2 - TauCeti.linearFormPow K 10 1 (-2)) +
    (-1947753 : K) • (TauCeti.linearFormPow K 10 1 3 - TauCeti.linearFormPow K 10 1 (-3)) +
    (334912 : K) • (TauCeti.linearFormPow K 10 1 4 - TauCeti.linearFormPow K 10 1 (-4)) +
    (-27203 : K) • (TauCeti.linearFormPow K 10 1 5 - TauCeti.linearFormPow K 10 1 (-5))

omit [CharZero K] in
theorem coe_deltaEven :
    (deltaEven K : MvPolynomial (Fin 2) K) = X 0 ^ 2 * X 1 ^ 2 * (X 0 ^ 2 - X 1 ^ 2) ^ 3 :=
  rfl

omit [CharZero K] in
theorem coe_deltaOdd :
    (deltaOdd K : MvPolynomial (Fin 2) K) =
      43545600 * (4 * X 0 ^ 9 * X 1 - 25 * X 0 ^ 7 * X 1 ^ 3 + 42 * X 0 ^ 5 * X 1 ^ 5 -
        25 * X 0 ^ 3 * X 1 ^ 7 + 4 * X 0 * X 1 ^ 9) := by
  simp only [deltaOdd, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub,
    TauCeti.coe_linearFormPow, smul_eq_C_mul, map_neg, map_one, map_ofNat]
  ring

omit [CharZero K] in
theorem coe_T_mul_S :
    ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {K}

omit [CharZero K] in
/-- The action of an explicit integer matrix on a polynomial in `X`, `Y`. -/
theorem coe_binaryFormRep_explicit {w : ℕ} (a b c d : ℤ) (P : homogeneousSubmodule (Fin 2) K w) :
    (TauCeti.binaryFormRep K w (op !![a, b; c, d]) P : MvPolynomial (Fin 2) K) =
      aeval (fun i : Fin 2 => if i = 0 then (C (a : K) * X 0 + C (b : K) * X 1 : MvPolynomial (Fin 2) K)
        else C (c : K) * X 0 + C (d : K) * X 1) (P : MvPolynomial (Fin 2) K) := by
  rw [TauCeti.coe_binaryFormRep_apply, MvPolynomial.linearSubst_eq_aeval]
  have hf : (fun i : Fin 2 => ∑ j, C ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K) i j) * (X j : MvPolynomial (Fin 2) K)) =
      fun i : Fin 2 => if i = 0 then (C (a : K) * X 0 + C (b : K) * X 1 : MvPolynomial (Fin 2) K)
        else C (c : K) * X 0 + C (d : K) * X 1 := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hf]

variable (K)

omit [CharZero K] in
theorem deltaEven_mem : deltaEven K ∈ TauCeti.periodPolynomials K 10 := by
  rw [TauCeti.mem_periodPolynomials_iff, coe_T_mul_S, ModularGroup.coe_S]
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · simp only [Submodule.coe_add, coe_binaryFormRep_explicit, coe_deltaEven, Submodule.coe_zero,
      map_mul, map_pow, map_sub, aeval_X]
    simp
    ring
  · simp only [Submodule.coe_add, coe_binaryFormRep_explicit, coe_deltaEven, Submodule.coe_zero,
      map_mul, map_pow, map_sub, aeval_X]
    simp
    ring

omit [CharZero K] in
theorem deltaOdd_mem : deltaOdd K ∈ TauCeti.periodPolynomials K 10 := by
  rw [TauCeti.mem_periodPolynomials_iff, coe_T_mul_S, ModularGroup.coe_S]
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · simp only [Submodule.coe_add, coe_binaryFormRep_explicit, coe_deltaOdd, Submodule.coe_zero,
      map_mul, map_pow, map_sub, map_add, map_ofNat, aeval_X]
    simp
    ring
  · simp only [Submodule.coe_add, coe_binaryFormRep_explicit, coe_deltaOdd, Submodule.coe_zero,
      map_mul, map_pow, map_sub, map_add, map_ofNat, aeval_X]
    simp
    ring

omit [CharZero K] in
theorem eval_deltaEven (x y : K) :
    eval ![x, y] (deltaEven K : MvPolynomial (Fin 2) K) = x ^ 2 * y ^ 2 * (x ^ 2 - y ^ 2) ^ 3 := by
  simp [coe_deltaEven]

/-- `⟨deltaEven ∣ T − deltaEven ∣ T⁻¹, (Y − tX)^{10}⟩`, by the reproducing property. -/
theorem pairing_deltaEven_linearFormPow (t : K) :
    invariantPairing K 10
        ((TauCeti.binaryFormRep K 10 (op (T : Matrix (Fin 2) (Fin 2) ℤ)) -
          TauCeti.binaryFormRep K 10 (op ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
            (deltaEven K))
        (TauCeti.linearFormPow K 10 1 t) =
      (1 + t) ^ 2 * t ^ 2 * ((1 + t) ^ 2 - t ^ 2) ^ 3 -
        (1 - t) ^ 2 * t ^ 2 * ((1 - t) ^ 2 - t ^ 2) ^ 3 := by
  have h := invariantPairing_linearFormPow
    ((TauCeti.binaryFormRep K 10 (op (T : Matrix (Fin 2) (Fin 2) ℤ)) -
      TauCeti.binaryFormRep K 10 (op ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
        (deltaEven K)) ![1, t]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, LinearMap.sub_apply, Submodule.coe_sub, map_sub, eval_binaryFormRep, eval_binaryFormRep,
    eval_deltaEven, eval_deltaEven]
  simp only [ModularGroup.coe_T, ModularGroup.coe_T_inv]
  simp
  ring

/-- **`{deltaEven, deltaOdd} = −6 · 43545600`.** -/
theorem bracket_deltaEven_deltaOdd :
    bracket K 10 (deltaEven K) (deltaOdd K) = -261273600 := by
  rw [bracket, LinearMap.comp_apply]
  simp only [deltaOdd, map_add, map_sub, map_smul, smul_eq_mul, pairing_deltaEven_linearFormPow]
  norm_num

/-! ## Nondegeneracy on `H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)` -/

/-- The class of `X²Y²(X² − Y²)³` in `H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)`. -/
noncomputable def deltaEvenClass : PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide) :=
  Submodule.Quotient.mk ((periodSpaceEquiv ℂ 10).symm ⟨deltaEven ℂ, deltaEven_mem ℂ⟩)

/-- The class of `43545600 · (4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹)`. -/
noncomputable def deltaOddClass : PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide) :=
  Submodule.Quotient.mk ((periodSpaceEquiv ℂ 10).symm ⟨deltaOdd ℂ, deltaOdd_mem ℂ⟩)

theorem parabolicPairing_deltaClasses :
    parabolicPairing (K := ℂ) (w := 10) (by decide) deltaEvenClass deltaOddClass = -261273600 := by
  rw [deltaEvenClass, deltaOddClass, parabolicPairing_mk, periodPairing_apply]
  exact bracket_deltaEven_deltaOdd ℂ

theorem parabolicPairing_self {w : ℕ} (hw : Even w) (x : PeriodSpace ℂ w ⧸ eisensteinLine hw) :
    parabolicPairing (K := ℂ) hw x x = 0 := by
  have h := parabolicPairing_antisymm (K := ℂ) hw x x
  linear_combination (1 / 2 : ℂ) * h

theorem parabolicPairing_deltaClasses' :
    parabolicPairing (K := ℂ) (w := 10) (by decide) deltaOddClass deltaEvenClass = 261273600 := by
  rw [parabolicPairing_antisymm, parabolicPairing_deltaClasses, neg_neg]

/-- The two classes are linearly independent. -/
theorem linearIndependent_deltaClasses :
    LinearIndependent ℂ ![deltaEvenClass, deltaOddClass] := by
  have hc := parabolicPairing_deltaClasses
  have hc' := parabolicPairing_deltaClasses'
  have huu := parabolicPairing_self (w := 10) (by decide) deltaEvenClass
  have hvv := parabolicPairing_self (w := 10) (by decide) deltaOddClass
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun z => parabolicPairing (K := ℂ) (w := 10) (by decide) z deltaOddClass) hab
  have h2 := congrArg (fun z => parabolicPairing (K := ℂ) (w := 10) (by decide) z deltaEvenClass) hab
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hc, hc',
    huu, hvv, map_zero, LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h1 h2
  refine ⟨?_, ?_⟩
  · have : a * (-261273600 : ℂ) = 0 := h1
    simpa using this
  · have : b * (261273600 : ℂ) = 0 := h2
    simpa using this

/-- **The two classes span `H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)`.** -/
theorem exists_deltaClasses_coords (x : PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide)) :
    ∃ a b : ℂ, a • deltaEvenClass + b • deltaOddClass = x := by
  have htop : Submodule.span ℂ (Set.range ![deltaEvenClass, deltaOddClass]) = ⊤ :=
    linearIndependent_deltaClasses.span_eq_top_of_card_eq_finrank'
      (by rw [finrank_parabolic_ten]; rfl)
  have hmem : x ∈ Submodule.span ℂ (Set.range ![deltaEvenClass, deltaOddClass]) := by
    rw [htop]
    trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hmem
  exact hmem

/-- **The pairing on `H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)` is nondegenerate.** -/
theorem parabolicPairing_ten_nondegenerate
    (x : PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide))
    (hx : ∀ y, parabolicPairing (K := ℂ) (w := 10) (by decide) x y = 0) : x = 0 := by
  have hc := parabolicPairing_deltaClasses
  have hc' := parabolicPairing_deltaClasses'
  have huu := parabolicPairing_self (w := 10) (by decide) deltaEvenClass
  have hvv := parabolicPairing_self (w := 10) (by decide) deltaOddClass
  obtain ⟨a, b, rfl⟩ := exists_deltaClasses_coords x
  have h1 := hx deltaOddClass
  have h2 := hx deltaEvenClass
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hc, hc',
    huu, hvv, mul_zero, add_zero, zero_add] at h1 h2
  have ha : a = 0 := by
    have : a * (-261273600 : ℂ) = 0 := h1
    simpa using this
  have hb : b = 0 := by
    have : b * (261273600 : ℂ) = 0 := h2
    simpa using this
  rw [ha, hb, zero_smul, zero_smul, add_zero]

/-! ## On the lattice -/

/-- `X²Y²(X² − Y²)³` with integer coefficients. -/
noncomputable def deltaEvenInt : homogeneousSubmodule (Fin 2) ℤ 10 :=
  ⟨X 0 ^ 2 * X 1 ^ 2 * (X 0 ^ 2 - X 1 ^ 2) ^ 3,
    ((isHomogeneous_X_pow 0 2).mul (isHomogeneous_X_pow 1 2)).mul
      (((isHomogeneous_X_pow 0 2).sub (isHomogeneous_X_pow 1 2)).pow 3)⟩

/-- `43545600 · (4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹)` with integer coefficients. -/
noncomputable def deltaOddInt : homogeneousSubmodule (Fin 2) ℤ 10 :=
  (-18456438 : ℤ) • (TauCeti.linearFormPow ℤ 10 1 1 - TauCeti.linearFormPow ℤ 10 1 (-1)) +
    (7193472 : ℤ) • (TauCeti.linearFormPow ℤ 10 1 2 - TauCeti.linearFormPow ℤ 10 1 (-2)) +
    (-1947753 : ℤ) • (TauCeti.linearFormPow ℤ 10 1 3 - TauCeti.linearFormPow ℤ 10 1 (-3)) +
    (334912 : ℤ) • (TauCeti.linearFormPow ℤ 10 1 4 - TauCeti.linearFormPow ℤ 10 1 (-4)) +
    (-27203 : ℤ) • (TauCeti.linearFormPow ℤ 10 1 5 - TauCeti.linearFormPow ℤ 10 1 (-5))

theorem coeffMap_deltaEvenInt : coeffMap 10 deltaEvenInt = deltaEven ℂ := by
  apply Subtype.ext
  rw [coe_coeffMap]
  simp [deltaEvenInt, coe_deltaEven]

theorem coeffMap_linearFormPow (x y : ℤ) :
    coeffMap 10 (TauCeti.linearFormPow ℤ 10 x y) = TauCeti.linearFormPow ℂ 10 (x : ℂ) (y : ℂ) := by
  apply Subtype.ext
  rw [coe_coeffMap]
  simp

theorem coeffMap_deltaOddInt : coeffMap 10 deltaOddInt = deltaOdd ℂ := by
  simp only [deltaOddInt, deltaOdd, map_add, map_sub, map_zsmul, coeffMap_linearFormPow,
    ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

/-- The class of `X²Y²(X² − Y²)³` in the lattice. -/
noncomputable def deltaEvenLattice : ParabolicLattice 10 (by decide) :=
  Submodule.Quotient.mk ((periodSpaceEquiv ℤ 10).symm ⟨deltaEvenInt,
    coeffMap_mem_periodPolynomials_iff.mp (coeffMap_deltaEvenInt ▸ deltaEven_mem ℂ)⟩)

/-- The class of `43545600 · (4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹)` in the lattice. -/
noncomputable def deltaOddLattice : ParabolicLattice 10 (by decide) :=
  Submodule.Quotient.mk ((periodSpaceEquiv ℤ 10).symm ⟨deltaOddInt,
    coeffMap_mem_periodPolynomials_iff.mp (coeffMap_deltaOddInt ▸ deltaOdd_mem ℂ)⟩)

theorem latticeMap_deltaEvenLattice :
    latticeMap (w := 10) (by decide) deltaEvenLattice = deltaEvenClass := by
  rw [deltaEvenLattice, latticeMap_mk, deltaEvenClass]
  congr 1
  apply (periodSpaceEquiv ℂ 10).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_periodSpaceMap]
  exact coeffMap_deltaEvenInt

theorem latticeMap_deltaOddLattice :
    latticeMap (w := 10) (by decide) deltaOddLattice = deltaOddClass := by
  rw [deltaOddLattice, latticeMap_mk, deltaOddClass]
  congr 1
  apply (periodSpaceEquiv ℂ 10).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_periodSpaceMap]
  exact coeffMap_deltaOddInt

/-- **The lattice pairing of the two classes**: `10! · (−6 · 43545600)`. In particular the
integral form on the rank-two lattice `H¹_par(SL(2, ℤ), V₁₀)` is not zero. -/
theorem latticePairing_delta :
    latticePairing (w := 10) (by decide) deltaEvenLattice deltaOddLattice =
      -261273600 * (Nat.factorial 10 : ℤ) := by
  have h := latticePairing_cast (w := 10) (by decide) deltaEvenLattice deltaOddLattice
  rw [latticeMap_deltaEvenLattice, latticeMap_deltaOddLattice, parabolicPairing_deltaClasses] at h
  have h' : ((latticePairing (w := 10) (by decide) deltaEvenLattice deltaOddLattice : ℤ) : ℂ) =
      ((-261273600 * (Nat.factorial 10 : ℤ) : ℤ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast h'

end TauTrack.Cohomology
