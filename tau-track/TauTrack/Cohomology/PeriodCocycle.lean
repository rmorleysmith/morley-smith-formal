module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Basic
public import TauCeti.NumberTheory.Modular.Relations
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic

/-!
# Period polynomials are values of parabolic cocycles

Let `V_w` be the binary forms of degree `w` over a commutative ring `R`, with the right action
`P ∣ γ` of `SL(2, ℤ)` (TauCeti's `binaryFormRep`). A **1-cocycle** is a map `φ : SL(2, ℤ) → V_w`
with

  `φ(γ δ) = φ(γ) ∣ δ + φ(δ)`.

It is **parabolic** (for the cusp `∞`) if `φ(T) = 0`.

* `IsCocycle.map_S_mem_periodPolynomials`: for `w` even and `2` invertible, the value `φ(S)` of a
  parabolic cocycle lies in TauCeti's period-polynomial space
  `W_w = ker(1 + S) ∩ ker(1 + U + U²)`.
* `IsCocycle.ext_of_S_T`: a cocycle is determined by its values at `S` and `T`. So
  `φ ↦ φ(S)` is injective on parabolic cocycles.

The two conditions defining `W_w` are the cocycle condition applied to the relations `S² = −1`
and `(TS)³ = −1`. The converse (every period polynomial is `φ(S)` for a parabolic cocycle) needs
the presentation of `PSL(2, ℤ)` by these two relations and is not proved here.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

variable {R : Type*} [CommRing R] {w : ℕ}

/-- The right action `P ∣ γ` of `SL(2, ℤ)` on binary forms of degree `w`. -/
noncomputable def act (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    homogeneousSubmodule (Fin 2) R w :=
  TauCeti.binaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P

theorem act_mul (P : homogeneousSubmodule (Fin 2) R w) (γ δ : SL(2, ℤ)) :
    act P (γ * δ) = act (act P γ) δ := by
  rw [act, SpecialLinearGroup.coe_mul, TauCeti.binaryFormRep_op_mul_apply]
  rfl

theorem act_one (P : homogeneousSubmodule (Fin 2) R w) : act P 1 = P := by
  rw [act, SpecialLinearGroup.coe_one, op_one, map_one]
  rfl

theorem act_add (P Q : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    act (P + Q) γ = act P γ + act Q γ := map_add _ P Q

theorem act_zero (γ : SL(2, ℤ)) : act (0 : homogeneousSubmodule (Fin 2) R w) γ = 0 :=
  map_zero _

theorem act_neg_one (hw : Even w) (P : homogeneousSubmodule (Fin 2) R w) : act P (-1) = P := by
  have h : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -1 := by simp
  rw [act, h, TauCeti.binaryFormRep_op_neg_of_even hw, op_one, map_one]
  rfl

/-- A 1-cocycle of `SL(2, ℤ)` with values in the binary forms of degree `w`, for the right
action: `φ(γ δ) = φ(γ) ∣ δ + φ(δ)`. -/
structure IsCocycle (φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w) : Prop where
  map_mul : ∀ γ δ, φ (γ * δ) = act (φ γ) δ + φ δ

namespace IsCocycle

variable {φ ψ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w}

theorem map_one (hφ : IsCocycle φ) : φ 1 = 0 := by
  have h := hφ.map_mul 1 1
  rw [mul_one, act_one] at h
  exact left_eq_add.mp h

theorem map_inv (hφ : IsCocycle φ) (γ : SL(2, ℤ)) : φ γ⁻¹ = -act (φ γ) γ⁻¹ := by
  have h := hφ.map_mul γ γ⁻¹
  rw [mul_inv_cancel, hφ.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A coboundary `γ ↦ P ∣ γ − P` is a cocycle. -/
theorem coboundary (P : homogeneousSubmodule (Fin 2) R w) :
    IsCocycle fun γ => act P γ - P := by
  refine ⟨fun γ δ => ?_⟩
  have h : act (act P γ - P) δ = act (act P γ) δ - act P δ := map_sub _ _ _
  rw [h, act_mul]
  abel

/-- A cocycle is determined by its values at `S` and `T`. -/
theorem ext_of_S_T (hφ : IsCocycle φ) (hψ : IsCocycle ψ) (hS : φ S = ψ S) (hT : φ T = ψ T) :
    φ = ψ := by
  funext γ
  have hmem : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [_root_.SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  | one => rw [hφ.map_one, hψ.map_one]
  | mul x y _ _ hx hy => rw [hφ.map_mul, hψ.map_mul, hx, hy]
  | inv x _ hx => rw [hφ.map_inv, hψ.map_inv, hx]

/-- **The value at `S` of a parabolic cocycle is a period polynomial.** -/
theorem map_S_mem_periodPolynomials [Invertible (2 : R)] (hw : Even w) (hφ : IsCocycle φ)
    (hT : φ T = 0) : φ S ∈ TauCeti.periodPolynomials R w := by
  -- `φ(−1) = 0`
  have h2 : ∀ P : homogeneousSubmodule (Fin 2) R w, P + P = 0 → P = 0 := by
    intro P hP
    have h : (2 : R) • P = 0 := by rw [two_smul]; exact hP
    calc P = (⅟(2 : R) * 2) • P := by rw [invOf_mul_self, one_smul]
      _ = 0 := by rw [mul_smul, h, smul_zero]
  have hneg : φ (-1) = 0 := by
    have h := hφ.map_mul (-1) (-1)
    rw [neg_mul_neg, mul_one, hφ.map_one, act_neg_one hw] at h
    exact h2 _ h.symm
  have hSS : (S * S : SL(2, ℤ)) = -1 := by decide +kernel
  have hU3 : (T * S) * (T * S) * (T * S) = (-1 : SL(2, ℤ)) := by
    have h := TauCeti.ModularGroup.T_mul_S_pow_three
    rwa [pow_succ, pow_two] at h
  have hU : φ (T * S) = φ S := by rw [hφ.map_mul, hT, act_zero, zero_add]
  rw [TauCeti.mem_periodPolynomials_iff]
  constructor
  · have h := hφ.map_mul S S
    rw [hSS, hneg] at h
    rw [add_comm]
    exact h.symm
  · have h := hφ.map_mul (T * S * (T * S)) (T * S)
    rw [hU3, hneg, hφ.map_mul (T * S) (T * S), hU, act_add] at h
    have e : φ S + act (φ S) (T * S) + act (act (φ S) (T * S)) (T * S) =
        act (act (φ S) (T * S)) (T * S) + act (φ S) (T * S) + φ S := by abel
    exact e.trans h.symm

/-- On parabolic cocycles, `φ ↦ φ(S)` is injective. -/
theorem eq_of_map_S_eq (hφ : IsCocycle φ) (hψ : IsCocycle ψ) (hφT : φ T = 0) (hψT : ψ T = 0)
    (hS : φ S = ψ S) : φ = ψ :=
  ext_of_S_T hφ hψ hS (hφT.trans hψT.symm)

end IsCocycle

end TauTrack.Cohomology
