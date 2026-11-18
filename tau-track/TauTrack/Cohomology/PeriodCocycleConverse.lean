module

public import TauTrack.Cohomology.PeriodCocycle
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import Mathlib.Tactic

/-!
# Every period polynomial is the value at `S` of a parabolic cocycle

The converse of `IsCocycle.map_S_mem_periodPolynomials`, given the presentation of `PSL(2, ℤ)` by
`S² = 1`, `U³ = 1` (`U = T S`) as a hypothesis `HasPresentation G`, for `G` the group of
permutations of the space of binary forms.

For `P ∈ W_w` consider the affine maps `A_{γ, c} : v ↦ v ∣ γ + c` of the space `V_w` of binary
forms. They compose by `A_{δ, d} ∘ A_{γ, c} = A_{γδ, c ∣ δ + d}`. The two conditions defining `W_w`
say exactly that `A_{S, P}` has order 2 and `A_{U, P}` has order 3. The presentation then gives a
homomorphism `γ ↦ A_{γ, φ(γ)}⁻¹`, and `φ` is the cocycle.

* `HasPresentation G`: the universal property of `PSL(2, ℤ)` for the target group `G`.
* `exists_cocycle_of_mem_periodPolynomials`: for `w` even and `P ∈ W_w` there is a cocycle `φ`
  with `φ(T) = 0` and `φ(S) = P`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

/-- The universal property of `PSL(2, ℤ) = ⟨S, U | S², U³⟩` for a target group `G`. -/
def HasPresentation (G : Type*) [Group G] : Prop :=
  ∀ s u : G, s * s = 1 → u * u * u = 1 →
    ∃ φ : PSL(2, ℤ) →* G, φ (S : PSL(2, ℤ)) = s ∧ φ ((T : PSL(2, ℤ)) * S) = u

variable {R : Type*} [CommRing R] {w : ℕ}

theorem act_sub (P Q : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    act (P - Q) γ = act P γ - act Q γ := map_sub _ P Q

theorem act_neg (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    act (-P) γ = -act P γ := map_neg _ P

/-- The affine map `v ↦ v ∣ γ + c` of the space of binary forms, as a permutation. -/
noncomputable def aff (γ : SL(2, ℤ)) (c : homogeneousSubmodule (Fin 2) R w) :
    Equiv.Perm (homogeneousSubmodule (Fin 2) R w) where
  toFun v := act v γ + c
  invFun v := act (v - c) γ⁻¹
  left_inv v := by
    change act (act v γ + c - c) γ⁻¹ = v
    rw [add_sub_cancel_right, ← act_mul, mul_inv_cancel, act_one]
  right_inv v := by
    change act (act (v - c) γ⁻¹) γ + c = v
    rw [← act_mul, inv_mul_cancel, act_one, sub_add_cancel]

@[simp] theorem aff_apply (γ : SL(2, ℤ)) (c v : homogeneousSubmodule (Fin 2) R w) :
    aff γ c v = act v γ + c := rfl

/-- `A_{δ, d} ∘ A_{γ, c} = A_{γδ, c ∣ δ + d}`. -/
theorem aff_mul_aff (γ δ : SL(2, ℤ)) (c d : homogeneousSubmodule (Fin 2) R w) :
    aff δ d * aff γ c = aff (γ * δ) (act c δ + d) := by
  ext1 v
  rw [Equiv.Perm.mul_apply, aff_apply, aff_apply, aff_apply, act_add, act_mul, add_assoc]

theorem aff_one_zero : aff (1 : SL(2, ℤ)) (0 : homogeneousSubmodule (Fin 2) R w) = 1 := by
  ext1 v
  rw [aff_apply, act_one, add_zero, Equiv.Perm.one_apply]

theorem aff_neg_one_zero (hw : Even w) :
    aff (-1 : SL(2, ℤ)) (0 : homogeneousSubmodule (Fin 2) R w) = 1 := by
  ext1 v
  rw [aff_apply, act_neg_one hw, add_zero, Equiv.Perm.one_apply]

theorem aff_inv (γ : SL(2, ℤ)) (c : homogeneousSubmodule (Fin 2) R w) :
    (aff γ c)⁻¹ = aff γ⁻¹ (-act c γ⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, aff_mul_aff, inv_mul_cancel]
  have h : act (-act c γ⁻¹) γ + c = 0 := by
    rw [act_neg, ← act_mul, inv_mul_cancel, act_one, neg_add_cancel]
  rw [h, aff_one_zero]

/-- **Every period polynomial is the value at `S` of a parabolic cocycle**, given the
presentation of `PSL(2, ℤ)`. -/
theorem exists_cocycle_of_mem_periodPolynomials
    (hpres : HasPresentation (Equiv.Perm (homogeneousSubmodule (Fin 2) R w))) (hw : Even w)
    {P : homogeneousSubmodule (Fin 2) R w} (hP : P ∈ TauCeti.periodPolynomials R w) :
    ∃ φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w, IsCocycle φ ∧ φ T = 0 ∧ φ S = P := by
  obtain ⟨hPS, hPU⟩ := TauCeti.mem_periodPolynomials_iff.mp hP
  have hSS : (S * S : SL(2, ℤ)) = -1 := by decide +kernel
  have hU3 : (T * S) * (T * S) * (T * S) = (-1 : SL(2, ℤ)) := by
    have h := TauCeti.ModularGroup.T_mul_S_pow_three
    rwa [pow_succ, pow_two] at h
  -- the two affine maps have orders 2 and 3
  have hs : aff S P * aff S P = 1 := by
    rw [aff_mul_aff, hSS]
    have h : act P S + P = 0 := by rw [add_comm]; exact hPS
    rw [h, aff_neg_one_zero hw]
  have hu : aff (T * S) P * aff (T * S) P * aff (T * S) P = 1 := by
    rw [aff_mul_aff, aff_mul_aff, ← mul_assoc, hU3]
    have h : act P (T * S * (T * S)) + (act P (T * S) + P) = 0 := by
      rw [act_mul]
      have e : act (act P (T * S)) (T * S) + (act P (T * S) + P) =
          P + act P (T * S) + act (act P (T * S)) (T * S) := by abel
      exact e.trans hPU
    rw [h, aff_neg_one_zero hw]
  have hs' : (aff S P)⁻¹ * (aff S P)⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hs, inv_one]
  have hu' : (aff (T * S) P)⁻¹ * (aff (T * S) P)⁻¹ * (aff (T * S) P)⁻¹ = 1 := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, hu, inv_one]
  obtain ⟨Φ, hΦS, hΦU⟩ := hpres _ _ hs' hu'
  let Ψ : SL(2, ℤ) →* Equiv.Perm (homogeneousSubmodule (Fin 2) R w) :=
    Φ.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  have hΨS : Ψ S = (aff S P)⁻¹ := hΦS
  have hΨU : Ψ (T * S) = (aff (T * S) P)⁻¹ := by
    have h : Ψ (T * S) = Φ ((T : PSL(2, ℤ)) * S) := rfl
    rw [h, hΦU]
  -- every `Ψ γ` is the inverse of an affine map over `γ`
  have key : ∀ γ : SL(2, ℤ), ∃ c, (Ψ γ)⁻¹ = aff γ c := by
    intro γ
    have hmem : γ ∈ Subgroup.closure ({S, T * S} : Set SL(2, ℤ)) := by
      rw [TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S]
      exact Subgroup.mem_top γ
    induction hmem using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨P, by rw [hΨS, inv_inv]⟩
      · exact ⟨P, by rw [hΨU, inv_inv]⟩
    | one => exact ⟨0, by rw [map_one, inv_one, aff_one_zero]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨act c y + d, by rw [map_mul, _root_.mul_inv_rev, hc, hd, aff_mul_aff]⟩
    | inv x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨-act c x⁻¹, by rw [map_inv, hc, aff_inv]⟩
  let φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w := fun γ => (Ψ γ)⁻¹ 0
  have hφ : ∀ γ, (Ψ γ)⁻¹ = aff γ (φ γ) := by
    intro γ
    obtain ⟨c, hc⟩ := key γ
    have h : φ γ = c := by
      change (Ψ γ)⁻¹ 0 = c
      rw [hc, aff_apply, act_zero, zero_add]
    rw [h, hc]
  have hcoc : IsCocycle φ := by
    refine ⟨fun γ δ => ?_⟩
    have h : aff (γ * δ) (φ (γ * δ)) = aff (γ * δ) (act (φ γ) δ + φ δ) := by
      rw [← hφ, map_mul, _root_.mul_inv_rev, hφ γ, hφ δ, aff_mul_aff]
    have h0 := congrArg (fun e : Equiv.Perm (homogeneousSubmodule (Fin 2) R w) => e 0) h
    simpa only [aff_apply, act_zero, zero_add] using h0
  have hφS : φ S = P := by
    change (Ψ S)⁻¹ 0 = P
    rw [hΨS, inv_inv, aff_apply, act_zero, zero_add]
  have hφU : φ (T * S) = P := by
    change (Ψ (T * S))⁻¹ 0 = P
    rw [hΨU, inv_inv, aff_apply, act_zero, zero_add]
  refine ⟨φ, hcoc, ?_, hφS⟩
  -- `φ(T S) = φ(T) ∣ S + φ(S)` forces `φ(T) ∣ S = 0`, hence `φ(T) = 0`
  have h := hcoc.map_mul T S
  rw [hφU, hφS] at h
  have h1 : act (φ T) S = 0 := by
    have := h.symm
    rwa [add_eq_right] at this
  have h2 : act (act (φ T) S) S⁻¹ = φ T := by rw [← act_mul, mul_inv_cancel, act_one]
  rw [← h2, h1, act_zero]

end TauTrack.Cohomology
