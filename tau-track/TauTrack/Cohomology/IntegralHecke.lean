module

public import TauTrack.Cohomology.IntegralStructure
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Tactic

/-!
# The Hecke operators preserve the lattice `H¹_par(SL(2, ℤ), V_w)`

Popa–Zagier's period relation (A) has a solution `ξ` with integer coefficients (TauCeti's
`exists_periodRelation ℤ`). Extending its coefficients to `ℂ` gives a solution over `ℂ`
(`periodRelation_cmapAlg`), and the action of `ξ` on binary forms commutes with extension of
coefficients (`periodAction_cmapAlg`). Since `Tₙ` on `H¹_par` is the action of any solution
(`heckeParabolic_mk`):

* `heckeParabolic_latticeMap`: **`Tₙ` maps the lattice into itself.**
* `heckeLattice`: the resulting endomorphism of the lattice, with
  `latticeMap_heckeLattice : latticeMap (Tₙ v) = Tₙ (latticeMap v)`.
* `charpoly_heckeParabolic`: **the characteristic polynomial of `Tₙ` on `H¹_par` has integer
  coefficients.**
* `heckeLattice_ten`: on the rank-two lattice for `w = 10`, `Tₙ` is multiplication by `τ(n)`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup MonoidAlgebra
open scoped MatrixGroups ModularForm
open TauCeti.TraceFormulaMatrixModule

namespace TauTrack.Cohomology

/-! ## Extension of coefficients on group-ring elements -/

/-- Extension of coefficients `ℤ[X] → ℂ[X]`. -/
noncomputable def cmapAlg (X : Type*) : ℤ[X] →+ ℂ[X] :=
  AddMonoidHom.mk' (MonoidAlgebra.map (Int.castAddHom ℂ)) (MonoidAlgebra.map_add _)

theorem cmapAlg_single {X : Type*} (x : X) (r : ℤ) :
    cmapAlg X (single x r) = single x (r : ℂ) :=
  MonoidAlgebra.map_single _ _ _

/-- Extension of coefficients commutes with a permutation action. -/
theorem cmapAlg_ofMulAction {G X : Type*} [Monoid G] [MulAction G X] (g : G) (ξ : ℤ[X]) :
    cmapAlg X (Representation.ofMulAction ℤ G X g ξ) =
      Representation.ofMulAction ℂ G X g (cmapAlg X ξ) := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single m r =>
    rw [Representation.ofMulAction_single, cmapAlg_single, cmapAlg_single,
      Representation.ofMulAction_single]

theorem cmapAlg_upperTriangularSum (n : ℤ) :
    cmapAlg _ (upperTriangularSum ℤ n) = upperTriangularSum ℂ n := by
  rw [upperTriangularSum_def, upperTriangularSum_def, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cmapAlg_single, Int.cast_one]

/-- **An integral solution of the period relation (A) is a complex solution.** -/
theorem periodRelation_cmapAlg {n : ℤ} {ξ : ℤ[TauCeti.TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℤ n ξ) : PeriodRelation ℂ n (cmapAlg _ ξ) := by
  rw [periodRelation_iff] at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨cmapAlg _ y, ?_⟩
  have h1 := congrArg (cmapAlg _) hy
  simp only [LinearMap.sub_apply, one_apply_eq_self, map_sub, cmapAlg_ofMulAction,
    cmapAlg_upperTriangularSum] at h1 ⊢
  exact h1

variable {w : ℕ}

/-- **The action on binary forms commutes with extension of coefficients.** -/
theorem periodAction_cmapAlg (hw : Even w) {n : ℤ} (ξ : ℤ[TauCeti.TraceFormulaMatrixModule n])
    (P : homogeneousSubmodule (Fin 2) ℤ w) :
    periodAction (R := ℂ) hw (cmapAlg _ ξ) (coeffMap w P) =
      coeffMap w (periodAction (R := ℤ) hw ξ P) := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, map_add]
  | single m r =>
    induction m using TauCeti.TraceFormulaMatrixModule.induction with
    | h A =>
      rw [cmapAlg_single, periodAction_single, periodAction_single, LinearMap.smul_apply,
        LinearMap.smul_apply, binaryFormAction_mk, binaryFormAction_mk, map_zsmul,
        coeffMap_binaryFormRep, Int.cast_smul_eq_zsmul]

/-! ## The lattice is stable -/

theorem coeffMap_injective : Function.Injective (coeffMap w) := by
  intro P Q h
  apply Subtype.ext
  have h1 := congrArg (Subtype.val) h
  rw [coe_coeffMap, coe_coeffMap] at h1
  exact MvPolynomial.map_injective _ Int.cast_injective h1

/-- A binary form with integer coefficients is a period polynomial if and only if it is one
over `ℂ`. -/
theorem coeffMap_mem_periodPolynomials_iff {P : homogeneousSubmodule (Fin 2) ℤ w} :
    coeffMap w P ∈ TauCeti.periodPolynomials ℂ w ↔ P ∈ TauCeti.periodPolynomials ℤ w := by
  refine ⟨fun h => ?_, coeffMap_mem_periodPolynomials⟩
  rw [← ker_periodRelMap, LinearMap.mem_ker] at h ⊢
  rw [← coeffMap_periodRelMap] at h
  have hinj : Function.Injective ((coeffMap w).prodMap (coeffMap w)) :=
    Function.Injective.prodMap coeffMap_injective coeffMap_injective
  exact hinj (h.trans (map_zero _).symm)

/-- **The Hecke operators preserve the lattice**: `Tₙ` of a lattice vector is a lattice
vector. -/
theorem heckeParabolic_latticeMap (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    (v : ParabolicLattice w hw) :
    ∃ v' : ParabolicLattice w hw,
      heckeParabolic hw hw0 n (latticeMap hw v) = latticeMap hw v' := by
  obtain ⟨ξ, hξ⟩ := exists_periodRelation ℤ (n : ℤ)
  have hξℂ := periodRelation_cmapAlg hξ
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- the image of `Q` under the integral action is again an integral period polynomial
  have hmem : periodAction (R := ℤ) hw ξ (periodIncl ℤ w Q) ∈ TauCeti.periodPolynomials ℤ w := by
    rw [← coeffMap_mem_periodPolynomials_iff, ← periodAction_cmapAlg]
    exact hξℂ.periodAction_mem_periodPolynomials hw n
      (coeffMap_mem_periodPolynomials (periodSpaceEquiv ℤ w Q).2)
  refine ⟨Submodule.Quotient.mk ((periodSpaceEquiv ℤ w).symm ⟨_, hmem⟩), ?_⟩
  rw [latticeMap_mk, latticeMap_mk]
  have h1 := heckeParabolic_mk hw hw0 n hξℂ (periodSpaceEquiv ℂ w (periodSpaceMap w Q))
  rw [LinearEquiv.symm_apply_apply] at h1
  rw [h1]
  congr 1
  apply (periodSpaceEquiv ℂ w).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact periodAction_cmapAlg hw ξ (periodIncl ℤ w Q)

/-! ## The Hecke operators on the lattice -/

/-- The lattice embeds in its complexification. -/
theorem latticeMap_injective (hw : Even w) (hw0 : w ≠ 0) :
    Function.Injective (latticeMap hw) := by
  have := free_parabolicLattice hw hw0
  intro x y h
  have h1 : (isBaseChange_latticeMap hw).equiv ((1 : ℂ) ⊗ₜ[ℤ] x) =
      (isBaseChange_latticeMap hw).equiv ((1 : ℂ) ⊗ₜ[ℤ] y) := by
    rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, one_smul, one_smul, h]
  have h2 := (isBaseChange_latticeMap hw).equiv.injective h1
  exact Module.Flat.tensorProduct_mk_injective ℤ (ParabolicLattice w hw) ℂ (by simpa using h2)

/-- **The Hecke operator `Tₙ` on the lattice.** -/
noncomputable def heckeLattice (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n] :
    ParabolicLattice w hw →ₗ[ℤ] ParabolicLattice w hw :=
  AddMonoidHom.toIntLinearMap <| AddMonoidHom.mk'
    (fun v => (heckeParabolic_latticeMap hw hw0 n v).choose) fun u v => by
      apply latticeMap_injective hw hw0
      have huv := (heckeParabolic_latticeMap hw hw0 n (u + v)).choose_spec
      have hu := (heckeParabolic_latticeMap hw hw0 n u).choose_spec
      have hv := (heckeParabolic_latticeMap hw hw0 n v).choose_spec
      calc latticeMap hw (heckeParabolic_latticeMap hw hw0 n (u + v)).choose
          = heckeParabolic hw hw0 n (latticeMap hw (u + v)) := huv.symm
        _ = heckeParabolic hw hw0 n (latticeMap hw u) +
              heckeParabolic hw hw0 n (latticeMap hw v) := by rw [map_add, map_add]
        _ = latticeMap hw (heckeParabolic_latticeMap hw hw0 n u).choose +
              latticeMap hw (heckeParabolic_latticeMap hw hw0 n v).choose :=
          congrArg₂ (· + ·) hu hv
        _ = _ := (map_add _ _ _).symm

/-- **The Hecke operator on the lattice is the restriction of the one on `H¹_par`.** -/
theorem latticeMap_heckeLattice (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    (v : ParabolicLattice w hw) :
    latticeMap hw (heckeLattice hw hw0 n v) = heckeParabolic hw hw0 n (latticeMap hw v) :=
  (heckeParabolic_latticeMap hw hw0 n v).choose_spec.symm

instance instFinitePeriodSpaceComplex : Module.Finite ℂ (PeriodSpace ℂ w) := by
  have : Module.Finite ℂ (homogeneousSubmodule (Fin 2) ℂ w) :=
    Module.Finite.of_basis (TauCeti.binaryFormMonomialBasis ℂ w)
  exact Module.Finite.of_injective (periodIncl ℂ w) (periodIncl_injective ℂ w)

/-- **The characteristic polynomial of `Tₙ` on `H¹_par` has integer coefficients**: it is the
characteristic polynomial of `Tₙ` on the lattice. -/
theorem charpoly_heckeParabolic (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n] :
    (heckeParabolic hw hw0 n).charpoly =
      (@LinearMap.charpoly ℤ (ParabolicLattice w hw) _ _ _ (free_parabolicLattice hw hw0)
        inferInstance (heckeLattice hw hw0 n)).map (Int.castRingHom ℂ) := by
  have := free_parabolicLattice hw hw0
  have hconj : heckeParabolic hw hw0 n =
      (isBaseChange_latticeMap hw).equiv.conj ((heckeLattice hw hw0 n).baseChange ℂ) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (isBaseChange_latticeMap hw).equiv.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    induction y using TensorProduct.inductionOn with
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        latticeMap_heckeLattice]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  rw [hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange]
  rfl

/-- **On the rank-two lattice `H¹_par(SL(2, ℤ), V₁₀)`, `Tₙ` is multiplication by the integer
`τ(n)`.** -/
theorem heckeLattice_ten (n : ℕ) [NeZero n] (v : ParabolicLattice 10 (by decide)) :
    heckeLattice (w := 10) (by decide) (by decide) n v = ramanujanTau n • v := by
  apply latticeMap_injective (w := 10) (by decide) (by decide)
  rw [latticeMap_heckeLattice, heckeParabolic_ten, map_zsmul, Int.cast_smul_eq_zsmul]

end TauTrack.Cohomology
