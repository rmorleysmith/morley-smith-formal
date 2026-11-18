module

public import TauTrack.Cohomology.HodgeHecke
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import Mathlib.RingTheory.Flat.IsBaseChange
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
import Mathlib.Tactic

/-!
# The integral structure on `H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`

The integral period polynomials modulo `X^w − Y^w`,
`parabolicLattice w = W_w(ℤ) ⧸ ℤ (X^w − Y^w)`, map to `W_w(ℂ) ⧸ ℂ (X^w − Y^w)` by extending
coefficients (`latticeMap`).

* `isBaseChange_coeffMap`: binary forms over `ℂ` are the base change of binary forms over `ℤ`.
* `isBaseChange_periodMap`: the same for period polynomials (kernels commute with flat base
  change).
* `isBaseChange_latticeMap`: **`W_w(ℂ) ⧸ ℂ (X^w − Y^w) = ℂ ⊗_ℤ parabolicLattice w`**.
* `latticeConjugation_eq`: the conjugation attached to this lattice is conjugation of
  coefficients (`parabolicConjugation`).
* `parabolicIntegralHodgeStructure`: **the Hodge structure of weight `k − 1` on the lattice**, in
  TauCeti's sense (`TauCeti.Hodge.HodgeStructure`).
* `free_parabolicLattice`, `finrank_parabolicLattice_eq`: the lattice is free of rank
  `2 dim S_k` (`X^w − Y^w` is primitive); for `w = 10` the rank is two.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups ModularForm TensorProduct
open TauCeti.Hodge

namespace TauTrack.Cohomology

/-! ## A base change criterion -/

/-- A linear map that sends a basis to a basis is a base change. -/
theorem isBaseChange_of_basis {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (b : Module.Basis ι R M) (b' : Module.Basis ι S N) (f : M →ₗ[R] N)
    (h : ∀ i, f (b i) = b' i) : IsBaseChange S f := by
  refine IsBaseChange.of_equiv ((b.baseChange S).equiv b' (Equiv.refl ι)) fun x => ?_
  have hf : (((b.baseChange S).equiv b' (Equiv.refl ι)).toLinearMap.restrictScalars R) ∘ₗ
      (TensorProduct.mk R S M 1) = f := by
    refine b.ext fun i => ?_
    rw [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, ← Module.Basis.baseChange_apply, Module.Basis.equiv_apply, h]
    rfl
  exact LinearMap.congr_fun hf x

/-- If `f` sends a basis to a basis, then `f × f` is a base change. -/
theorem isBaseChange_prodMap_of_basis {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (b : Module.Basis ι R M) (b' : Module.Basis ι S N) (f : M →ₗ[R] N)
    (h : ∀ i, f (b i) = b' i) : IsBaseChange S (f.prodMap f) := by
  refine isBaseChange_of_basis (b.prod b) (b'.prod b') _ ?_
  rintro (i | i)
  · rw [Module.Basis.prod_apply, Module.Basis.prod_apply]
    simp [h]
  · rw [Module.Basis.prod_apply, Module.Basis.prod_apply]
    simp [h]

variable {w : ℕ}

/-! ## Binary forms -/

variable (w) in
/-- Extension of coefficients from `ℤ` to `ℂ` on binary forms of degree `w`. -/
noncomputable def coeffMap :
    homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] homogeneousSubmodule (Fin 2) ℂ w where
  toFun := TauCeti.mapHomogeneousSubmodule (Int.castRingHom ℂ) w
  map_add' := map_add _
  map_smul' a p := by
    rw [map_smulₛₗ, RingHom.id_apply, eq_intCast, Int.cast_smul_eq_zsmul]

@[simp]
theorem coe_coeffMap (P : homogeneousSubmodule (Fin 2) ℤ w) :
    (coeffMap w P : MvPolynomial (Fin 2) ℂ) =
      map (Int.castRingHom ℂ) (P : MvPolynomial (Fin 2) ℤ) :=
  TauCeti.coe_mapHomogeneousSubmodule_apply (Int.castRingHom ℂ) P

/-- **Binary forms over `ℂ` are the base change of binary forms over `ℤ`.** -/
theorem isBaseChange_coeffMap : IsBaseChange ℂ (coeffMap w) :=
  isBaseChange_of_basis (TauCeti.binaryFormMonomialBasis ℤ w)
    (TauCeti.binaryFormMonomialBasis ℂ w) (coeffMap w) fun j =>
    TauCeti.mapHomogeneousSubmodule_binaryFormMonomialBasis (Int.castRingHom ℂ) j

/-- Extension of coefficients commutes with substitution by an integer matrix. -/
theorem map_linearSubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    map (Int.castRingHom ℂ) (MvPolynomial.linearSubst (M.map (Int.castRingHom ℤ)) P) =
      MvPolynomial.linearSubst (M.map (Int.castRingHom ℂ)) (map (Int.castRingHom ℂ) P) := by
  have h : (map (Int.castRingHom ℂ)).comp
      (MvPolynomial.linearSubst (M.map (Int.castRingHom ℤ))).toRingHom =
      (MvPolynomial.linearSubst (M.map (Int.castRingHom ℂ))).toRingHom.comp
        (map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [MvPolynomial.linearSubst_eq_aeval]
  exact DFunLike.congr_fun h P

/-- Extension of coefficients commutes with the action of integer matrices. -/
theorem coeffMap_binaryFormRep (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) ℤ w) :
    coeffMap w (TauCeti.binaryFormRep ℤ w (op M) P) =
      TauCeti.binaryFormRep ℂ w (op M) (coeffMap w P) := by
  apply Subtype.ext
  rw [coe_coeffMap, TauCeti.coe_binaryFormRep_apply, TauCeti.coe_binaryFormRep_apply,
    coe_coeffMap]
  exact map_linearSubst M P

/-! ## Period polynomials -/

/-- The map whose kernel is `W_w`: `P ↦ (P + P ∣ S, P + P ∣ U + P ∣ U²)`. -/
noncomputable def periodRelMap (R : Type*) [CommRing R] (w : ℕ) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R]
      homogeneousSubmodule (Fin 2) R w × homogeneousSubmodule (Fin 2) R w :=
  (LinearMap.id + TauCeti.binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))).prod
    (LinearMap.id + TauCeti.binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
      (TauCeti.binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).comp
        (TauCeti.binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))))

theorem ker_periodRelMap (R : Type*) [CommRing R] (w : ℕ) :
    LinearMap.ker (periodRelMap R w) = TauCeti.periodPolynomials R w := by
  ext P
  rw [periodRelMap, LinearMap.ker_prod, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
    TauCeti.mem_periodPolynomials_iff]
  rfl

theorem exact_subtype_periodRelMap (R : Type*) [CommRing R] (w : ℕ) :
    Function.Exact (TauCeti.periodPolynomials R w).subtype (periodRelMap R w) := by
  rw [LinearMap.exact_iff, ker_periodRelMap, Submodule.range_subtype]

theorem coeffMap_periodRelMap (P : homogeneousSubmodule (Fin 2) ℤ w) :
    (coeffMap w).prodMap (coeffMap w) (periodRelMap ℤ w P) = periodRelMap ℂ w (coeffMap w P) := by
  refine Prod.ext ?_ ?_
  · change coeffMap w (P + TauCeti.binaryFormRep ℤ w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P) =
      coeffMap w P + TauCeti.binaryFormRep ℂ w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) (coeffMap w P)
    rw [map_add, coeffMap_binaryFormRep]
  · change coeffMap w (P +
        TauCeti.binaryFormRep ℤ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P +
        TauCeti.binaryFormRep ℤ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          (TauCeti.binaryFormRep ℤ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P)) =
      coeffMap w P +
        TauCeti.binaryFormRep ℂ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          (coeffMap w P) +
        TauCeti.binaryFormRep ℂ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          (TauCeti.binaryFormRep ℂ w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
            (coeffMap w P))
    rw [map_add, map_add, coeffMap_binaryFormRep, coeffMap_binaryFormRep, coeffMap_binaryFormRep]

theorem coeffMap_mem_periodPolynomials {P : homogeneousSubmodule (Fin 2) ℤ w}
    (hP : P ∈ TauCeti.periodPolynomials ℤ w) : coeffMap w P ∈ TauCeti.periodPolynomials ℂ w := by
  rw [← ker_periodRelMap, LinearMap.mem_ker] at hP ⊢
  rw [← coeffMap_periodRelMap, hP, map_zero]

/-- The inclusion of the period polynomials in the binary forms. -/
noncomputable def periodIncl (R : Type*) [CommRing R] (w : ℕ) :
    PeriodSpace R w →ₗ[R] homogeneousSubmodule (Fin 2) R w :=
  (TauCeti.periodPolynomials R w).subtype.comp (periodSpaceEquiv R w).toLinearMap

theorem periodIncl_injective (R : Type*) [CommRing R] (w : ℕ) :
    Function.Injective (periodIncl R w) :=
  (Submodule.subtype_injective _).comp (periodSpaceEquiv R w).injective

theorem range_periodIncl (R : Type*) [CommRing R] (w : ℕ) :
    LinearMap.range (periodIncl R w) = TauCeti.periodPolynomials R w := by
  rw [periodIncl, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

theorem exact_periodIncl_periodRelMap (R : Type*) [CommRing R] (w : ℕ) :
    Function.Exact (periodIncl R w) (periodRelMap R w) := by
  rw [LinearMap.exact_iff, ker_periodRelMap, range_periodIncl]

variable (w) in
/-- Extension of coefficients on period polynomials. -/
noncomputable def periodSpaceMap : PeriodSpace ℤ w →ₗ[ℤ] PeriodSpace ℂ w :=
  AddMonoidHom.toIntLinearMap <| AddMonoidHom.mk'
    (fun P => (periodSpaceEquiv ℂ w).symm
      ⟨coeffMap w (periodIncl ℤ w P), coeffMap_mem_periodPolynomials (periodSpaceEquiv ℤ w P).2⟩)
    fun P Q => by
      rw [← map_add]
      congr 1
      apply Subtype.ext
      simp only [map_add, Submodule.coe_add]

theorem periodIncl_periodSpaceMap (P : PeriodSpace ℤ w) :
    periodIncl ℂ w (periodSpaceMap w P) = coeffMap w (periodIncl ℤ w P) :=
  rfl

/-- **Period polynomials over `ℂ` are the base change of period polynomials over `ℤ`.** -/
theorem isBaseChange_periodSpaceMap : IsBaseChange ℂ (periodSpaceMap w) := by
  have hprod : IsBaseChange ℂ ((coeffMap w).prodMap (coeffMap w)) :=
    isBaseChange_prodMap_of_basis (TauCeti.binaryFormMonomialBasis ℤ w)
      (TauCeti.binaryFormMonomialBasis ℂ w) (coeffMap w) fun j =>
      TauCeti.mapHomogeneousSubmodule_binaryFormMonomialBasis (Int.castRingHom ℂ) j
  have comm₁ : (coeffMap w).comp (periodIncl ℤ w) =
      ((periodIncl ℂ w).restrictScalars ℤ).comp (periodSpaceMap w) :=
    LinearMap.ext fun P => (periodIncl_periodSpaceMap P).symm
  have comm₂ : ((coeffMap w).prodMap (coeffMap w)).comp (periodRelMap ℤ w) =
      ((periodRelMap ℂ w).restrictScalars ℤ).comp (coeffMap w) :=
    LinearMap.ext fun P => coeffMap_periodRelMap P
  exact IsBaseChange.of_left_exact ℂ (periodSpaceMap w) (coeffMap w)
    ((coeffMap w).prodMap (coeffMap w)) comm₁ comm₂ isBaseChange_coeffMap hprod
    (exact_periodIncl_periodRelMap ℤ w) (periodIncl_injective ℤ w)
    (exact_periodIncl_periodRelMap ℂ w) (periodIncl_injective ℂ w)

/-! ## The lattice -/

/-- `X^w − Y^w` as an integral period polynomial. -/
noncomputable def eisensteinPeriodInt (w : ℕ) (hw : Even w) : PeriodSpace ℤ w :=
  (periodSpaceEquiv ℤ w).symm ⟨TauCeti.eisensteinPeriodPolynomial ℤ w,
    (TauCeti.mem_evenPeriodPolynomials_iff.mp
      (TauCeti.mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw)).1⟩

/-- **The lattice `H¹_par(SL(2, ℤ), V_w)`** in the period-polynomial model:
integral period polynomials modulo `X^w − Y^w`. -/
abbrev ParabolicLattice (w : ℕ) (hw : Even w) : Type :=
  PeriodSpace ℤ w ⧸ ℤ ∙ eisensteinPeriodInt w hw

theorem coe_periodSpaceMap (P : PeriodSpace ℤ w) :
    ((periodSpaceEquiv ℂ w (periodSpaceMap w P) : TauCeti.periodPolynomials ℂ w) :
        homogeneousSubmodule (Fin 2) ℂ w) =
      coeffMap w ((periodSpaceEquiv ℤ w P : TauCeti.periodPolynomials ℤ w) :
        homogeneousSubmodule (Fin 2) ℤ w) :=
  rfl

theorem periodSpaceMap_eisensteinPeriodInt (hw : Even w) :
    periodSpaceMap w (eisensteinPeriodInt w hw) =
      (periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw) := by
  apply (periodSpaceEquiv ℂ w).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_periodSpaceMap, coe_coeffMap]
  simp [eisensteinPeriodInt, eisensteinPeriod, TauCeti.coe_eisensteinPeriodPolynomial]

theorem periodSpaceMap_mem_eisensteinLine (hw : Even w) {P : PeriodSpace ℤ w}
    (hP : P ∈ ℤ ∙ eisensteinPeriodInt w hw) :
    periodSpaceMap w P ∈ (eisensteinLine hw).restrictScalars ℤ := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hP
  rw [map_smul, periodSpaceMap_eisensteinPeriodInt, Submodule.restrictScalars_mem,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The map from the lattice to the complex cohomology.** -/
noncomputable def latticeMap (hw : Even w) :
    ParabolicLattice w hw →ₗ[ℤ] PeriodSpace ℂ w ⧸ eisensteinLine hw :=
  (ℤ ∙ eisensteinPeriodInt w hw).mapQ ((eisensteinLine hw).restrictScalars ℤ) (periodSpaceMap w)
    fun _ hP => periodSpaceMap_mem_eisensteinLine hw hP

@[simp]
theorem latticeMap_mk (hw : Even w) (P : PeriodSpace ℤ w) :
    latticeMap hw (Submodule.Quotient.mk P) = Submodule.Quotient.mk (periodSpaceMap w P) :=
  rfl

/-- **`W_w(ℂ) ⧸ ℂ (X^w − Y^w)` is the complexification of the lattice.** -/
theorem isBaseChange_latticeMap (hw : Even w) : IsBaseChange ℂ (latticeMap hw) := by
  refine IsBaseChange.of_right_exact ℂ (Algebra.linearMap ℤ ℂ) (periodSpaceMap w) (latticeMap hw)
    (f := LinearMap.toSpanSingleton ℤ _ (eisensteinPeriodInt w hw))
    (g := (ℤ ∙ eisensteinPeriodInt w hw).mkQ)
    (f' := LinearMap.toSpanSingleton ℂ _
      ((periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw)))
    (g' := (eisensteinLine hw).mkQ) ?_ ?_ (IsBaseChange.linearMap ℤ ℂ) isBaseChange_periodSpaceMap
    ?_ (Submodule.mkQ_surjective _) ?_ (Submodule.mkQ_surjective _)
  · ext
    simp [periodSpaceMap_eisensteinPeriodInt]
  · ext P
    rfl
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, LinearMap.range_toSpanSingleton]
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, LinearMap.range_toSpanSingleton]

/-! ## The conjugation and the Hodge structure -/

/-- Conjugation of coefficients fixes forms with integer coefficients. -/
theorem binaryConj_coeffMap (P : homogeneousSubmodule (Fin 2) ℤ w) :
    binaryConj w (coeffMap w P) = coeffMap w P := by
  apply Subtype.ext
  rw [coe_binaryConj, coe_coeffMap, MvPolynomial.map_map]
  have h : (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ := by
    ext a
    simp
  rw [h]

/-- The conjugation on `H¹_par` fixes the lattice. -/
theorem parabolicConjugation_latticeMap (hw : Even w) (v : ParabolicLattice w hw) :
    (parabolicConjugation hw).toEquiv (latticeMap hw v) = latticeMap hw v := by
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [latticeMap_mk, parabolicConjugation, Conjugation.quotient_toEquiv_mk]
  congr 1
  apply (periodSpaceEquiv ℂ w).injective
  apply Subtype.ext
  rw [coe_periodConjugation, coe_periodSpaceMap]
  exact binaryConj_coeffMap _

/-- **The conjugation attached to the lattice is conjugation of coefficients.** -/
theorem latticeConjugation_eq (hw : Even w) :
    latticeConjugation (isBaseChange_latticeMap hw) = parabolicConjugation hw := by
  have h := latticeConj_unique (isBaseChange_latticeMap hw)
    (parabolicConjugation hw).toEquiv.toLinearMap (parabolicConjugation_latticeMap hw)
  have he : (latticeConjugation (isBaseChange_latticeMap hw)).toEquiv =
      (parabolicConjugation hw).toEquiv := by
    ext x
    rw [latticeConjugation_toEquiv_apply, ← h]
    rfl
  cases h₁ : latticeConjugation (isBaseChange_latticeMap hw) with
  | mk e₁ i₁ =>
    cases h₂ : parabolicConjugation hw with
    | mk e₂ i₂ =>
      rw [h₁, h₂] at he
      cases he
      rfl

/-- **The integral Hodge structure of weight `k − 1 = w + 1`** on the lattice
`H¹_par(SL(2, ℤ), V_w)`, in TauCeti's sense. -/
noncomputable def parabolicIntegralHodgeStructure (hw : Even w) (hw0 : w ≠ 0) :
    HodgeStructure (isBaseChange_latticeMap hw) ((w : ℤ) + 1) :=
  cast (congrArg (fun ω => HodgeStructureOn (PeriodSpace ℂ w ⧸ eisensteinLine hw) ω ((w : ℤ) + 1))
    (latticeConjugation_eq hw).symm) (parabolicHodgeStructure hw hw0)

/-! ## The lattice is free of rank `2 dim S_k` -/

instance instFinitePeriodSpaceInt : Module.Finite ℤ (PeriodSpace ℤ w) := by
  have : Module.Finite ℤ (homogeneousSubmodule (Fin 2) ℤ w) :=
    Module.Finite.of_basis (TauCeti.binaryFormMonomialBasis ℤ w)
  exact Module.Finite.of_injective (periodIncl ℤ w) (periodIncl_injective ℤ w)

/-- The coefficient of `X^w`, as a linear functional on integral period polynomials. -/
noncomputable def leadCoeff (w : ℕ) : PeriodSpace ℤ w →ₗ[ℤ] ℤ :=
  ((MvPolynomial.lcoeff ℤ (Finsupp.single (0 : Fin 2) w)).comp
    (homogeneousSubmodule (Fin 2) ℤ w).subtype).comp (periodIncl ℤ w)

theorem leadCoeff_eisensteinPeriodInt (hw : Even w) (hw0 : w ≠ 0) :
    leadCoeff w (eisensteinPeriodInt w hw) = 1 := by
  change ((TauCeti.eisensteinPeriodPolynomial ℤ w : homogeneousSubmodule (Fin 2) ℤ w) :
      MvPolynomial (Fin 2) ℤ).coeff (Finsupp.single (0 : Fin 2) w) = 1
  have hne : ¬ Finsupp.single (1 : Fin 2) w = Finsupp.single (0 : Fin 2) w := by
    intro h
    have h0 := DFunLike.congr_fun h (0 : Fin 2)
    simp at h0
    exact hw0 h0.symm
  rw [TauCeti.coe_eisensteinPeriodPolynomial, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow,
    MvPolynomial.coeff_X_pow]
  simp [hne]

/-- **The lattice is torsion-free**: `X^w − Y^w` is primitive among the integral period
polynomials. -/
theorem isTorsionFree_parabolicLattice (hw : Even w) (hw0 : w ≠ 0) :
    Module.IsTorsionFree ℤ (ParabolicLattice w hw) := by
  have : Module.Free ℤ (homogeneousSubmodule (Fin 2) ℤ w) :=
    Module.Free.of_basis (TauCeti.binaryFormMonomialBasis ℤ w)
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_singleton] at hx
  obtain ⟨m, hm⟩ := hx
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  refine ⟨leadCoeff w P, ?_⟩
  have h1 : m = n * leadCoeff w P := by
    have h := congrArg (leadCoeff w) hm
    rw [map_zsmul, map_zsmul, leadCoeff_eisensteinPeriodInt hw hw0] at h
    simpa using h
  apply periodIncl_injective ℤ w
  have h2 : n • periodIncl ℤ w (leadCoeff w P • eisensteinPeriodInt w hw) =
      n • periodIncl ℤ w P := by
    rw [← map_zsmul, ← map_zsmul, smul_smul, ← h1, hm]
  exact smul_right_injective _ hn h2

/-- **The lattice is a free `ℤ`-module.** -/
theorem free_parabolicLattice (hw : Even w) (hw0 : w ≠ 0) :
    Module.Free ℤ (ParabolicLattice w hw) := by
  have := isTorsionFree_parabolicLattice hw hw0
  infer_instance

/-- **The rank of the lattice is the complex dimension of the cohomology.** -/
theorem finrank_parabolicLattice (hw : Even w) (hw0 : w ≠ 0) :
    Module.finrank ℤ (ParabolicLattice w hw) =
      Module.finrank ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) := by
  have := free_parabolicLattice hw hw0
  rw [← (isBaseChange_latticeMap hw).equiv.finrank_eq, Module.finrank_baseChange]

/-- **The lattice has rank `2 dim S_k`.** -/
theorem finrank_parabolicLattice_eq (hw : Even w) (hw0 : w ≠ 0) :
    Module.finrank ℤ (ParabolicLattice w hw) =
      2 * Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  rw [finrank_parabolicLattice hw hw0, finrank_parabolic hw hw0]

/-- **For `w = 10` the lattice has rank two**: with its Hodge structure of type
`(11, 0) + (0, 11)` and the Hecke action by `τ(n)`, this is the integral Hodge realisation
of `Δ`. -/
theorem finrank_parabolicLattice_ten :
    Module.finrank ℤ (ParabolicLattice 10 (by decide)) = 2 := by
  rw [finrank_parabolicLattice (by decide) (by decide)]
  exact finrank_parabolic_ten

end TauTrack.Cohomology
