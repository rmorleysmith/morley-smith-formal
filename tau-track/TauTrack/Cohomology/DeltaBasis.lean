module

public import TauTrack.Cohomology.DeltaLattice
import Mathlib.Tactic

/-!
# A basis of the lattice `H¹_par(SL(2, ℤ), V₁₀)` and the Gram matrix of its pairing

`L₁₀ = W₁₀(ℤ) ⧸ ℤ (X¹⁰ − Y¹⁰)` is the lattice of `TauTrack.Cohomology.ParabolicLattice`.

* `deltaOddPrim = 4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹` (integer coefficients), with class
  `deltaOddPrimLattice`; `deltaEvenLattice` is the class of `X²Y²(X² − Y²)³`.
* `exists_lattice_coords`: **every vector of `L₁₀` is an integer combination of the two
  classes.** Proof: over `ℂ` the two classes span; the coefficients of `X⁸Y²`, `X⁹Y` and `X⁷Y³`
  are integers on the lattice and read off the two coordinates (`4` and `25` are coprime).
* `deltaLatticeBasis`: the two classes are a `ℤ`-basis of `L₁₀`.
* `latticePairing_deltaBasis`: **the Gram matrix**: in this basis
  `latticePairing x y = −6 · 10! · (x₀ y₁ − x₁ y₀)`. So the pairing divided by `10!` is `6` times
  the standard symplectic form, of determinant `36`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

/-! ## Coordinates -/

/-- Extension of coefficients on the coordinates in the monomial basis. -/
theorem repr_coeffMap {w : ℕ} (P : homogeneousSubmodule (Fin 2) ℤ w) (j : Fin (w + 1)) :
    (TauCeti.binaryFormMonomialBasis ℂ w).repr (coeffMap w P) j =
      (((TauCeti.binaryFormMonomialBasis ℤ w).repr P j : ℤ) : ℂ) := by
  have e : (AddMonoidHom.mk'
        (fun P => (TauCeti.binaryFormMonomialBasis ℂ w).repr (coeffMap w P) j)
        (fun a b => by simp)).toIntLinearMap =
      (AddMonoidHom.mk'
        (fun P => (((TauCeti.binaryFormMonomialBasis ℤ w).repr P j : ℤ) : ℂ))
        (fun a b => by simp)).toIntLinearMap :=
    (TauCeti.binaryFormMonomialBasis ℤ w).ext fun i => by
      simp [coeffMap_basis, Finsupp.single_apply]
  exact LinearMap.congr_fun e P

/-- `X¹⁰ − Y¹⁰` in the monomial basis. -/
theorem eisensteinPeriodPolynomial_ten :
    TauCeti.eisensteinPeriodPolynomial ℂ 10 =
      TauCeti.binaryFormMonomialBasis ℂ 10 10 - TauCeti.binaryFormMonomialBasis ℂ 10 0 := by
  apply Subtype.ext
  simp [TauCeti.coe_eisensteinPeriodPolynomial, TauCeti.coe_binaryFormMonomialBasis]

/-- The coefficient of `X^j Y^{10−j}`, `j ≠ 0, 10`, as a functional on
`H¹_par(SL(2, ℤ), V₁₀ ⊗ ℂ)`. -/
noncomputable def coordQuot (j : Fin 11) (hj : j ≠ 0 ∧ j ≠ 10) :
    (PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide)) →ₗ[ℂ] ℂ :=
  (eisensteinLine (w := 10) (by decide)).liftQ
    (((TauCeti.binaryFormMonomialBasis ℂ 10).coord j).comp (periodIncl ℂ 10)) (by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.comp_apply]
      change (TauCeti.binaryFormMonomialBasis ℂ 10).coord j
        (TauCeti.eisensteinPeriodPolynomial ℂ 10) = 0
      rw [eisensteinPeriodPolynomial_ten]
      simp [hj.1.symm, hj.2.symm])

theorem coordQuot_latticeMap_mk (j : Fin 11) (hj : j ≠ 0 ∧ j ≠ 10) (Q : PeriodSpace ℤ 10) :
    coordQuot j hj (latticeMap (w := 10) (by decide) (Submodule.Quotient.mk Q)) =
      (((TauCeti.binaryFormMonomialBasis ℤ 10).repr (periodIncl ℤ 10 Q) j : ℤ) : ℂ) := by
  rw [latticeMap_mk, coordQuot, Submodule.liftQ_apply, LinearMap.comp_apply,
    periodIncl_periodSpaceMap, Module.Basis.coord_apply, repr_coeffMap]

/-! ## The two integral period polynomials in the monomial basis -/

/-- `4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹` with integer coefficients. -/
noncomputable def deltaOddPrim : homogeneousSubmodule (Fin 2) ℤ 10 :=
  (4 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 9 -
    (25 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 7 +
    (42 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 5 -
    (25 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 3 +
    (4 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 1

theorem deltaOddInt_eq : deltaOddInt = (43545600 : ℤ) • deltaOddPrim := by
  apply Subtype.ext
  simp only [deltaOddInt, deltaOddPrim, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    TauCeti.coe_linearFormPow, TauCeti.coe_binaryFormMonomialBasis, zsmul_eq_mul]
  simp
  ring

theorem deltaEvenInt_eq :
    deltaEvenInt = TauCeti.binaryFormMonomialBasis ℤ 10 8 -
      (3 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 6 +
      (3 : ℤ) • TauCeti.binaryFormMonomialBasis ℤ 10 4 -
      TauCeti.binaryFormMonomialBasis ℤ 10 2 := by
  apply Subtype.ext
  simp only [deltaEvenInt, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    TauCeti.coe_binaryFormMonomialBasis, zsmul_eq_mul]
  simp
  ring

theorem coeffMap_deltaOddPrim_mem :
    coeffMap 10 deltaOddPrim ∈ TauCeti.periodPolynomials ℂ 10 := by
  have h : (43545600 : ℂ) • coeffMap 10 deltaOddPrim = deltaOdd ℂ := by
    rw [← coeffMap_deltaOddInt, deltaOddInt_eq, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
    norm_num
  have h2 : coeffMap 10 deltaOddPrim = (43545600 : ℂ)⁻¹ • deltaOdd ℂ := by
    rw [← h, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (deltaOdd_mem ℂ)

/-- The class of `4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹` in the lattice. -/
noncomputable def deltaOddPrimLattice : ParabolicLattice 10 (by decide) :=
  Submodule.Quotient.mk ((periodSpaceEquiv ℤ 10).symm ⟨deltaOddPrim,
    coeffMap_mem_periodPolynomials_iff.mp coeffMap_deltaOddPrim_mem⟩)

theorem deltaOddLattice_eq : deltaOddLattice = (43545600 : ℤ) • deltaOddPrimLattice := by
  rw [deltaOddLattice, deltaOddPrimLattice, ← Submodule.Quotient.mk_smul, ← map_zsmul]
  congr 2
  exact Subtype.ext deltaOddInt_eq

/-! ## Coordinates of the two classes -/

theorem coordQuot_deltaEvenClass (j : Fin 11) (hj : j ≠ 0 ∧ j ≠ 10) :
    coordQuot j hj deltaEvenClass =
      (((TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaEvenInt j : ℤ) : ℂ) := by
  rw [← latticeMap_deltaEvenLattice, deltaEvenLattice, coordQuot_latticeMap_mk]
  rfl

theorem coordQuot_latticeMap_deltaOddPrimLattice (j : Fin 11) (hj : j ≠ 0 ∧ j ≠ 10) :
    coordQuot j hj (latticeMap (w := 10) (by decide) deltaOddPrimLattice) =
      (((TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaOddPrim j : ℤ) : ℂ) := by
  rw [deltaOddPrimLattice, coordQuot_latticeMap_mk]
  rfl

theorem deltaOddClass_eq :
    deltaOddClass = (43545600 : ℂ) • latticeMap (w := 10) (by decide) deltaOddPrimLattice := by
  rw [← latticeMap_deltaOddLattice, deltaOddLattice_eq, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  norm_num

/-! ## The classes span the lattice -/

/-- **Every vector of `L₁₀` is an integer combination of the two classes.** -/
theorem exists_lattice_coords (x : ParabolicLattice 10 (by decide)) :
    ∃ m n : ℤ, x = m • deltaEvenLattice + n • deltaOddPrimLattice := by
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, b, hab⟩ := exists_deltaClasses_coords
    (latticeMap (w := 10) (by decide) (Submodule.Quotient.mk Q))
  rw [deltaOddClass_eq, smul_smul] at hab
  -- the three coordinates
  have h8 := congrArg (coordQuot 8 (by decide)) hab
  have h9 := congrArg (coordQuot 9 (by decide)) hab
  have h7 := congrArg (coordQuot 7 (by decide)) hab
  simp only [map_add, map_smul, smul_eq_mul, coordQuot_deltaEvenClass,
    coordQuot_latticeMap_deltaOddPrimLattice, coordQuot_latticeMap_mk] at h8 h9 h7
  have e8 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaEvenInt 8 = 1 := by
    rw [deltaEvenInt_eq]; simp
  have e9 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaEvenInt 9 = 0 := by
    rw [deltaEvenInt_eq]; simp
  have e7 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaEvenInt 7 = 0 := by
    rw [deltaEvenInt_eq]; simp
  have o8 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaOddPrim 8 = 0 := by
    simp [deltaOddPrim]
  have o9 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaOddPrim 9 = 4 := by
    simp [deltaOddPrim]
  have o7 : (TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaOddPrim 7 = -25 := by
    simp [deltaOddPrim]
  rw [e8, o8] at h8
  rw [e9, o9] at h9
  rw [e7, o7] at h7
  set n8 := (TauCeti.binaryFormMonomialBasis ℤ 10).repr (periodIncl ℤ 10 Q) 8
  set n9 := (TauCeti.binaryFormMonomialBasis ℤ 10).repr (periodIncl ℤ 10 Q) 9
  set n7 := (TauCeti.binaryFormMonomialBasis ℤ 10).repr (periodIncl ℤ 10 Q) 7
  have ha : a = (n8 : ℂ) := by
    push_cast at h8
    linear_combination h8
  have hb : b * 43545600 = ((-n7 - 6 * n9 : ℤ) : ℂ) := by
    push_cast at h9 h7 ⊢
    linear_combination (-1 : ℂ) * h7 - 6 * h9
  refine ⟨n8, -n7 - 6 * n9, ?_⟩
  apply latticeMap_injective (w := 10) (by decide) (by decide)
  rw [map_add, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
    latticeMap_deltaEvenLattice, ← hab, ha, hb]

/-! ## The basis and the Gram matrix -/

theorem latticePairing_self {w : ℕ} (hw : Even w) (x : ParabolicLattice w hw) :
    latticePairing hw x x = 0 := by
  have h := latticePairing_antisymm hw x x
  omega

/-- `latticePairing (X²Y²(X² − Y²)³, 4X⁹Y − ⋯) = −6 · 10!`. -/
theorem latticePairing_deltaEven_deltaOddPrim :
    latticePairing (w := 10) (by decide) deltaEvenLattice deltaOddPrimLattice =
      -6 * (Nat.factorial 10 : ℤ) := by
  have h := latticePairing_delta
  rw [deltaOddLattice_eq, map_zsmul, smul_eq_mul] at h
  have h10 : (Nat.factorial 10 : ℤ) = 3628800 := by decide
  rw [h10] at h ⊢
  omega

theorem latticePairing_deltaOddPrim_deltaEven :
    latticePairing (w := 10) (by decide) deltaOddPrimLattice deltaEvenLattice =
      6 * (Nat.factorial 10 : ℤ) := by
  rw [latticePairing_antisymm, latticePairing_deltaEven_deltaOddPrim]
  ring

theorem linearIndependent_deltaLattice :
    LinearIndependent ℤ ![deltaEvenLattice, deltaOddPrimLattice] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun z => latticePairing (w := 10) (by decide) z deltaOddPrimLattice) hab
  have h2 := congrArg (fun z => latticePairing (w := 10) (by decide) z deltaEvenLattice) hab
  have h10 : (Nat.factorial 10 : ℤ) = 3628800 := by decide
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    latticePairing_deltaEven_deltaOddPrim, latticePairing_deltaOddPrim_deltaEven,
    latticePairing_self, map_zero, LinearMap.zero_apply, mul_zero, add_zero, zero_add, h10]
    at h1 h2
  constructor <;> omega

/-- **The two classes are a `ℤ`-basis of the lattice `H¹_par(SL(2, ℤ), V₁₀)`.** -/
noncomputable def deltaLatticeBasis : Module.Basis (Fin 2) ℤ (ParabolicLattice 10 (by decide)) :=
  Module.Basis.mk linearIndependent_deltaLattice (by
    intro x _
    obtain ⟨m, n, rfl⟩ := exists_lattice_coords x
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair]
    exact ⟨m, n, rfl⟩)

theorem deltaLatticeBasis_zero : deltaLatticeBasis 0 = deltaEvenLattice := by
  simp [deltaLatticeBasis]

theorem deltaLatticeBasis_one : deltaLatticeBasis 1 = deltaOddPrimLattice := by
  simp [deltaLatticeBasis]

/-- **The Gram matrix of the pairing on `L₁₀`**: in the basis of the two classes,
`latticePairing x y = −6 · 10! · (x₀ y₁ − x₁ y₀)`. -/
theorem latticePairing_deltaBasis (x y : ParabolicLattice 10 (by decide)) :
    latticePairing (w := 10) (by decide) x y =
      -6 * (Nat.factorial 10 : ℤ) *
        (deltaLatticeBasis.repr x 0 * deltaLatticeBasis.repr y 1 -
          deltaLatticeBasis.repr x 1 * deltaLatticeBasis.repr y 0) := by
  conv_lhs => rw [← deltaLatticeBasis.sum_repr x, ← deltaLatticeBasis.sum_repr y]
  simp only [Fin.sum_univ_two, deltaLatticeBasis_zero, deltaLatticeBasis_one, map_add, map_zsmul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, latticePairing_self,
    latticePairing_deltaEven_deltaOddPrim, latticePairing_deltaOddPrim_deltaEven]
  ring

/-- **In weight 12 the Hecke operators are self-adjoint for the lattice pairing** (they are
scalars). -/
theorem latticePairing_heckeLattice_ten (n : ℕ) [NeZero n] (x y : ParabolicLattice 10 (by decide)) :
    latticePairing (w := 10) (by decide) (heckeLattice (w := 10) (by decide) (by decide) n x) y =
      latticePairing (w := 10) (by decide) x
        (heckeLattice (w := 10) (by decide) (by decide) n y) := by
  rw [heckeLattice_ten, heckeLattice_ten, map_zsmul, map_zsmul, LinearMap.smul_apply]

end TauTrack.Cohomology
