module

public import TauTrack.Cohomology.PeriodCocycleIff
public import TauTrack.Cohomology.EisensteinCoboundary
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# Parabolic cohomology of `SL(2, ℤ)` with coefficients in binary forms

Let `V_w` be the binary forms of degree `w` with the right action of `SL(2, ℤ)`.

* `Cochain R w`: the functions `SL(2, ℤ) → V_w`.
* `cocycles R w`: the 1-cocycles `φ(γδ) = φ(γ) ∣ δ + φ(δ)`.
* `coboundaryMap R w`: `v ↦ (γ ↦ v ∣ γ − v)`.
* `parabolicCocycles R w`: the cocycles whose value at `T` is `v ∣ T − v` for some `v`, that is,
  whose restriction to the stabiliser of the cusp `∞` is a coboundary.
* `ParabolicH1 R w`: parabolic cocycles modulo coboundaries.

Every parabolic class contains a cocycle with `φ(T) = 0`, and such cocycles are the period
polynomials (`PeriodCocycleIff.lean`). So there is a surjection

  `periodToH1 : W_w → ParabolicH1 R w`  (`periodToH1_surjective`),

whose kernel consists of the `v ∣ S − v` with `v ∣ T = v` (`periodToH1_eq_zero_iff`). Over a
field of characteristic zero the forms fixed by `T` are the multiples of `Y^w`
(`eq_smul_yPow_of_act_T`), so the kernel is the line of `X^w − Y^w` (`ker_periodToH1`) and

  `parabolicH1Equiv : W_w ⧸ ⟨X^w − Y^w⟩ ≃ ParabolicH1 K w`.

Implementation note. `Cochain R w` and `PeriodSpace R w` are definitions, not abbreviations, with
their module structure declared once. With the bare types (submodules of submodules of
`MvPolynomial`) Lean's unifier does not find the quotient-module instances.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

variable {R : Type*} [CommRing R] {w : ℕ}

theorem act_smul (c : R) (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    act (c • P) γ = c • act P γ := map_smul _ c P

/-! ## Cocycles, coboundaries, parabolic cocycles -/

/-- The 1-cochains: functions `SL(2, ℤ) → V_w`. -/
def Cochain (R : Type*) [CommRing R] (w : ℕ) : Type _ :=
  SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w

noncomputable instance : AddCommGroup (Cochain R w) :=
  inferInstanceAs (AddCommGroup (SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w))

noncomputable instance : Module R (Cochain R w) :=
  inferInstanceAs (Module R (SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w))

namespace Cochain

theorem add_apply (φ ψ : Cochain R w) (γ : SL(2, ℤ)) : (φ + ψ) γ = φ γ + ψ γ := rfl

theorem sub_apply (φ ψ : Cochain R w) (γ : SL(2, ℤ)) : (φ - ψ) γ = φ γ - ψ γ := rfl

theorem smul_apply (c : R) (φ : Cochain R w) (γ : SL(2, ℤ)) : (c • φ) γ = c • φ γ := rfl

theorem zero_apply (γ : SL(2, ℤ)) : (0 : Cochain R w) γ = 0 := rfl

end Cochain

variable (R w) in
/-- The module of 1-cocycles of `SL(2, ℤ)` with values in binary forms of degree `w`. -/
noncomputable def cocycles : Submodule R (Cochain R w) where
  carrier := {φ | IsCocycle φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ δ => by
    simp only [Cochain.add_apply]
    rw [hφ.map_mul, hψ.map_mul, act_add]
    abel⟩
  zero_mem' := ⟨fun γ δ => by simp only [Cochain.zero_apply, act_zero, add_zero]⟩
  smul_mem' c φ hφ := ⟨fun γ δ => by
    simp only [Cochain.smul_apply]
    rw [hφ.map_mul, act_smul, smul_add]⟩

theorem mem_cocycles {φ : Cochain R w} :
    φ ∈ cocycles R w ↔ IsCocycle φ := Iff.rfl

variable (R w) in
/-- The coboundary map `v ↦ (γ ↦ v ∣ γ − v)`. -/
noncomputable def coboundaryMap : homogeneousSubmodule (Fin 2) R w →ₗ[R] Cochain R w where
  toFun v := fun γ => act v γ - v
  map_add' v v' := by
    funext γ
    change act (v + v') γ - (v + v') = (act v γ - v) + (act v' γ - v')
    rw [act_add]
    abel
  map_smul' c v := by
    funext γ
    change act (c • v) γ - c • v = c • (act v γ - v)
    rw [act_smul, smul_sub]

theorem coboundaryMap_apply (v : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    coboundaryMap R w v γ = act v γ - v := rfl

theorem isCocycle_coboundaryMap (v : homogeneousSubmodule (Fin 2) R w) :
    IsCocycle (coboundaryMap R w v) := IsCocycle.coboundary v

variable (R w) in
/-- The parabolic cocycles: those whose value at `T` is `v ∣ T − v` for some `v`. -/
noncomputable def parabolicCocycles : Submodule R (Cochain R w) where
  carrier := {φ | IsCocycle φ ∧ ∃ v, φ T = act v T - v}
  add_mem' := by
    rintro φ ψ ⟨hφ, v, hv⟩ ⟨hψ, v', hv'⟩
    refine ⟨(cocycles R w).add_mem hφ hψ, v + v', ?_⟩
    simp only [Cochain.add_apply, hv, hv', act_add]
    abel
  zero_mem' := ⟨(cocycles R w).zero_mem, 0, by
    simp only [Cochain.zero_apply, act_zero, sub_zero]⟩
  smul_mem' := by
    rintro c φ ⟨hφ, v, hv⟩
    refine ⟨(cocycles R w).smul_mem c hφ, c • v, ?_⟩
    simp only [Cochain.smul_apply, hv, act_smul, smul_sub]

theorem coboundaryMap_mem_parabolicCocycles (v : homogeneousSubmodule (Fin 2) R w) :
    coboundaryMap R w v ∈ parabolicCocycles R w :=
  ⟨isCocycle_coboundaryMap v, v, rfl⟩

variable (R w) in
/-- The coboundaries, as a submodule of the parabolic cocycles. -/
noncomputable def parabolicCoboundaries : Submodule R (parabolicCocycles R w) :=
  LinearMap.range ((coboundaryMap R w).codRestrict (parabolicCocycles R w)
    coboundaryMap_mem_parabolicCocycles)

/-- **The parabolic cohomology** `H¹_par(SL(2, ℤ), V_w)`: parabolic cocycles modulo
coboundaries. -/
abbrev ParabolicH1 (R : Type*) [CommRing R] (w : ℕ) : Type _ :=
  parabolicCocycles R w ⧸ parabolicCoboundaries R w

/-! ## From period polynomials to parabolic classes -/

/-- The cocycle with `φ(T) = 0` and `φ(S) = P`, for a period polynomial `P`. -/
noncomputable def cocycleOfPeriod (hw : Even w) (P : TauCeti.periodPolynomials R w) :
    SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w :=
  Classical.choose (exists_cocycle_of_mem_periodPolynomials (hasPresentation _) hw P.2)

theorem cocycleOfPeriod_spec (hw : Even w) (P : TauCeti.periodPolynomials R w) :
    IsCocycle (cocycleOfPeriod hw P) ∧ cocycleOfPeriod hw P T = 0 ∧
      cocycleOfPeriod hw P S = P :=
  Classical.choose_spec (exists_cocycle_of_mem_periodPolynomials (hasPresentation _) hw P.2)

theorem cocycleOfPeriod_eq (hw : Even w) (P : TauCeti.periodPolynomials R w)
    {φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w} (hφ : IsCocycle φ) (hT : φ T = 0)
    (hS : φ S = P) : cocycleOfPeriod hw P = φ := by
  obtain ⟨h1, h2, h3⟩ := cocycleOfPeriod_spec hw P
  exact IsCocycle.eq_of_map_S_eq h1 hφ h2 hT (h3.trans hS.symm)

/-- `P ↦ φ_P`, as a linear map into the parabolic cocycles. -/
noncomputable def periodToCocycle (hw : Even w) :
    TauCeti.periodPolynomials R w →ₗ[R] parabolicCocycles R w where
  toFun P := ⟨cocycleOfPeriod hw P, (cocycleOfPeriod_spec hw P).1, 0, by
    rw [(cocycleOfPeriod_spec hw P).2.1, act_zero, sub_zero]⟩
  map_add' P Q := by
    apply Subtype.ext
    obtain ⟨p1, p2, p3⟩ := cocycleOfPeriod_spec hw P
    obtain ⟨q1, q2, q3⟩ := cocycleOfPeriod_spec hw Q
    change cocycleOfPeriod hw (P + Q) = cocycleOfPeriod hw P + cocycleOfPeriod hw Q
    exact cocycleOfPeriod_eq hw (P + Q)
      ((cocycles R w).add_mem (x := cocycleOfPeriod hw P) (y := cocycleOfPeriod hw Q) p1 q1)
      (by rw [Pi.add_apply, p2, q2, add_zero])
      (by rw [Pi.add_apply, p3, q3, Submodule.coe_add])
  map_smul' c P := by
    apply Subtype.ext
    obtain ⟨p1, p2, p3⟩ := cocycleOfPeriod_spec hw P
    change cocycleOfPeriod hw (c • P) = c • cocycleOfPeriod hw P
    exact cocycleOfPeriod_eq hw (c • P)
      ((cocycles R w).smul_mem (x := cocycleOfPeriod hw P) c p1)
      (by rw [Pi.smul_apply, p2, smul_zero])
      (by rw [Pi.smul_apply, p3, Submodule.coe_smul])

theorem coe_periodToCocycle (hw : Even w) (P : TauCeti.periodPolynomials R w) :
    (periodToCocycle hw P : Cochain R w) = cocycleOfPeriod hw P := rfl

/-- The class of a period polynomial in parabolic cohomology. -/
noncomputable def periodToH1 (hw : Even w) :
    TauCeti.periodPolynomials R w →ₗ[R] ParabolicH1 R w :=
  (parabolicCoboundaries R w).mkQ ∘ₗ periodToCocycle hw

/-- **Every parabolic class is the class of a period polynomial.** Subtract the coboundary of
`v`, where `φ(T) = v ∣ T − v`; the result vanishes at `T`. -/
theorem periodToH1_surjective [Invertible (2 : R)] (hw : Even w) :
    Function.Surjective (periodToH1 (R := R) hw) := by
  intro x
  obtain ⟨⟨φ, hφ, v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hψ : IsCocycle (φ - coboundaryMap R w v) :=
    (cocycles R w).sub_mem hφ (isCocycle_coboundaryMap v)
  have hψT : (φ - coboundaryMap R w v) T = 0 := by
    rw [Cochain.sub_apply, coboundaryMap_apply, hv, sub_self]
  have hP := hψ.map_S_mem_periodPolynomials hw hψT
  refine ⟨⟨(φ - coboundaryMap R w v) S, hP⟩, ?_⟩
  rw [periodToH1, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  refine ⟨-v, Subtype.ext ?_⟩
  have e2 : ((periodToCocycle hw ⟨(φ - coboundaryMap R w v) S, hP⟩ : parabolicCocycles R w) :
      Cochain R w) = φ - coboundaryMap R w v :=
    cocycleOfPeriod_eq hw ⟨(φ - coboundaryMap R w v) S, hP⟩ hψ hψT rfl
  rw [Submodule.coe_sub, e2]
  change coboundaryMap R w (-v) = φ - coboundaryMap R w v - φ
  rw [map_neg]
  abel

/-- **The kernel of `W_w → H¹_par`**: the `v ∣ S − v` with `v` fixed by `T`. -/
theorem periodToH1_eq_zero_iff (hw : Even w) (P : TauCeti.periodPolynomials R w) :
    periodToH1 hw P = 0 ↔
      ∃ v : homogeneousSubmodule (Fin 2) R w, act v T = v ∧
        (P : homogeneousSubmodule (Fin 2) R w) = act v S - v := by
  rw [periodToH1, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨p1, p2, p3⟩ := cocycleOfPeriod_spec hw P
  constructor
  · rintro ⟨v, hv⟩
    have h : coboundaryMap R w v = cocycleOfPeriod hw P := congrArg Subtype.val hv
    refine ⟨v, ?_, ?_⟩
    · have hT := congrFun h T
      rw [coboundaryMap_apply, p2, sub_eq_zero] at hT
      exact hT
    · have hS := congrFun h S
      rw [coboundaryMap_apply, p3] at hS
      exact hS.symm
  · rintro ⟨v, hvT, hvS⟩
    refine ⟨v, Subtype.ext ?_⟩
    change coboundaryMap R w v = cocycleOfPeriod hw P
    exact (cocycleOfPeriod_eq hw P (isCocycle_coboundaryMap v)
      (by rw [coboundaryMap_apply, hvT, sub_self]) (by rw [coboundaryMap_apply, hvS])).symm

/-! ## Forms fixed by `T` -/

section TInvariants

variable {K : Type*} [Field K]

variable (K) in
/-- Dehomogenization `P(X, Y) ↦ P(x, 1)`, into polynomials in one variable. -/
noncomputable def dehom : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, 1]

/-- `dehom` factors through TauCeti's `dehomogenize 1`. -/
theorem dehom_eq_comp :
    dehom K = (MvPolynomial.aeval fun _ : Fin 1 => (Polynomial.X : Polynomial K)).comp
      (TauCeti.dehomogenize (1 : Fin 2)) := by
  have hins : (Fin.insertNth (1 : Fin 2) (1 : MvPolynomial (Fin 1) K) X :
      Fin 2 → MvPolynomial (Fin 1) K) = ![X 0, 1] := by
    funext i
    fin_cases i
    · exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin 1) K) (1 : Fin 2)
        1 X 0
    · exact Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin 1) K) (1 : Fin 2) 1 X
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [dehom, hins]

theorem aeval_fin_one_injective :
    Function.Injective
      (MvPolynomial.aeval (R := K) fun _ : Fin 1 => (Polynomial.X : Polynomial K)) := by
  have h : (Polynomial.aeval (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)).comp
      (MvPolynomial.aeval (R := K) fun _ : Fin 1 => (Polynomial.X : Polynomial K)) =
      AlgHom.id K (MvPolynomial (Fin 1) K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp
  exact Function.LeftInverse.injective fun p => by
    simpa using DFunLike.congr_fun h p

/-- `dehom` is injective on forms of a fixed degree. -/
theorem dehom_injOn (w : ℕ) :
    Set.InjOn (dehom K) {p : MvPolynomial (Fin 2) K | p.IsHomogeneous w} := by
  intro p hp q hq h
  rw [dehom_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply] at h
  exact TauCeti.dehomogenize_injOn (1 : Fin 2) w hp hq (aeval_fin_one_injective h)

/-- The substitution `X ↦ X + Y` becomes `x ↦ x + 1`. -/
theorem dehom_linearSubst_T (P : MvPolynomial (Fin 2) K) :
    dehom K (linearSubst ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K)) P) =
      (dehom K P).comp (Polynomial.X + 1) := by
  have h : (dehom K).comp
        (linearSubst ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K))) =
      (Polynomial.aeval (Polynomial.X + 1 : Polynomial K)).comp (dehom K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [dehom, Fin.sum_univ_two, ModularGroup.coe_T]
  rw [Polynomial.comp_eq_aeval]
  exact DFunLike.congr_fun h P

/-- A polynomial with `q(x + 1) = q(x)` over a field of characteristic zero is constant. -/
theorem eq_C_of_comp_X_add_one [CharZero K] {q : Polynomial K}
    (h : q.comp (Polynomial.X + 1) = q) : q = Polynomial.C (q.eval 0) := by
  have hn : ∀ n : ℕ, q.eval (n : K) = q.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := congrArg (Polynomial.eval (n : K)) h
      rw [Polynomial.eval_comp] at h1
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at h1
      rw [Nat.cast_succ, h1, ih]
  have h0 : q - Polynomial.C (q.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono ?_
    rintro _ ⟨n, rfl⟩
    simp [Polynomial.IsRoot, hn n]
  exact sub_eq_zero.mp h0

/-- **The binary forms fixed by `T` are the multiples of `Y^w`** (characteristic zero). -/
theorem eq_smul_yPow_of_act_T [CharZero K] {v : homogeneousSubmodule (Fin 2) K w}
    (h : act v T = v) : ∃ c : K, v = c • yPow K w := by
  have h1 : dehom K (v : MvPolynomial (Fin 2) K) =
      (dehom K (v : MvPolynomial (Fin 2) K)).comp (Polynomial.X + 1) := by
    rw [← dehom_linearSubst_T, ← TauCeti.coe_binaryFormRep_apply]
    exact congrArg (fun u : homogeneousSubmodule (Fin 2) K w =>
      dehom K (u : MvPolynomial (Fin 2) K)) h.symm
  have h2 := eq_C_of_comp_X_add_one h1.symm
  refine ⟨(dehom K (v : MvPolynomial (Fin 2) K)).eval 0, Subtype.ext ?_⟩
  apply dehom_injOn w v.2 (Submodule.smul_mem _ _ (yPow K w).2)
  rw [h2]
  simp [dehom, yPow, Algebra.smul_def]

end TInvariants

/-! ## The parabolic cohomology is `W_w` modulo the Eisenstein line -/

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The Eisenstein period polynomial `X^w − Y^w`, as an element of `W_w` (for `w` even). -/
noncomputable def eisensteinPeriod (K : Type*) [Field K] (w : ℕ) (hw : Even w) :
    TauCeti.periodPolynomials K w :=
  ⟨TauCeti.eisensteinPeriodPolynomial K w,
    (TauCeti.mem_evenPeriodPolynomials_iff.mp
      (TauCeti.mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw)).1⟩

/-- **The kernel of `W_w → H¹_par` is the line of `X^w − Y^w`.** -/
theorem ker_periodToH1 (hw : Even w) :
    LinearMap.ker (periodToH1 (R := K) hw) = K ∙ eisensteinPeriod K w hw := by
  have key : ∀ c : K, act (c • yPow K w) S - c • yPow K w =
      c • TauCeti.eisensteinPeriodPolynomial K w := by
    intro c
    have h := congrArg (fun φ : Cochain K w => φ S) (map_smul (coboundaryMap K w) c (yPow K w))
    rw [← eisensteinCocycle_S]
    exact h
  ext P
  rw [LinearMap.mem_ker, periodToH1_eq_zero_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨v, hvT, hvS⟩
    obtain ⟨c, rfl⟩ := eq_smul_yPow_of_act_T hvT
    refine ⟨c, Subtype.ext ?_⟩
    rw [hvS, key]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨c • yPow K w, by rw [act_smul, act_T_Y_pow], ?_⟩
    rw [key]
    rfl

/-- The period polynomials `W_w`, as a type with its module structure declared once (see the
implementation note at the top of the file). -/
def PeriodSpace (R : Type*) [CommRing R] (w : ℕ) : Type _ := TauCeti.periodPolynomials R w

noncomputable instance : AddCommGroup (PeriodSpace R w) :=
  inferInstanceAs (AddCommGroup (TauCeti.periodPolynomials R w))

noncomputable instance : Module R (PeriodSpace R w) :=
  inferInstanceAs (Module R (TauCeti.periodPolynomials R w))

/-- `PeriodSpace R w` is `W_w`. -/
noncomputable def periodSpaceEquiv (R : Type*) [CommRing R] (w : ℕ) :
    PeriodSpace R w ≃ₗ[R] TauCeti.periodPolynomials R w :=
  LinearEquiv.refl R _

/-- **Parabolic cohomology is the period polynomials modulo the Eisenstein line**:
`W_w ⧸ ⟨X^w − Y^w⟩ ≃ H¹_par(SL(2, ℤ), V_w)`. -/
noncomputable def parabolicH1Equiv (hw : Even w) :
    (PeriodSpace K w ⧸ K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw)) ≃ₗ[K]
      ParabolicH1 K w :=
  haveI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hker : LinearMap.ker (periodToH1 (R := K) hw ∘ₗ (periodSpaceEquiv K w).toLinearMap) =
      K ∙ (periodSpaceEquiv K w).symm (eisensteinPeriod K w hw) := by
    ext P
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ker_periodToH1,
      Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    exact Iff.rfl
  (Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((periodToH1 (R := K) hw ∘ₗ (periodSpaceEquiv K w).toLinearMap).quotKerEquivOfSurjective
      ((periodToH1_surjective hw).comp (periodSpaceEquiv K w).surjective))

theorem parabolicH1Equiv_mk (hw : Even w) (P : PeriodSpace K w) :
    parabolicH1Equiv hw (Submodule.Quotient.mk P) = periodToH1 hw (periodSpaceEquiv K w P) :=
  rfl

end Field

end TauTrack.Cohomology
