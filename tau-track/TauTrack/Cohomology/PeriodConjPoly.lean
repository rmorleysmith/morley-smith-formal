module

public import TauTrack.Cohomology.PeriodConj
public import TauTrack.Cohomology.Parabolic
import Mathlib.Tactic

/-!
# Complex conjugation on binary forms and on period polynomials

Conjugating the coefficients of a binary form of degree `w` is a conjugate-linear involution
`binaryConj` of `V_w ⊗ ℂ`; its fixed points are the forms with real coefficients.

* `cmap_linearSubst`, `binaryConj_binaryFormRep`: it commutes with the substitutions by
  integer matrices, hence with the action of `SL(2, ℤ)`.
* `binaryConj_mem_periodPolynomials`: it preserves the period polynomials `W_w`.
* `eq_of_eval_real`: two forms of degree `w` that agree at all points `(x, 1)`, `x` real, are
  equal.
* `binaryConj_periodPolynomial`: **`conj(r_f) = −r_{f^c} ∣ ε`**, `ε = diag(−1, 1)`: the
  conjugate of the period polynomial of `f` is minus the period polynomial of `f^c` with `X`
  replaced by `−X` (for `w` even).
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial
open scoped MatrixGroups ModularForm

namespace TauTrack.Cohomology

/-! ## Conjugation of coefficients -/

theorem cmap_cmap (P : MvPolynomial (Fin 2) ℂ) :
    map (starRingEnd ℂ) (map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [h, MvPolynomial.map_id]

/-- Conjugation of coefficients commutes with substitution by an integer matrix. -/
theorem cmap_linearSubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℂ) :
    map (starRingEnd ℂ) (MvPolynomial.linearSubst (M.map (Int.cast : ℤ → ℂ)) P) =
      MvPolynomial.linearSubst (M.map (Int.cast : ℤ → ℂ)) (map (starRingEnd ℂ) P) := by
  have h : (map (starRingEnd ℂ)).comp
      (MvPolynomial.linearSubst (M.map (Int.cast : ℤ → ℂ))).toRingHom =
      (MvPolynomial.linearSubst (M.map (Int.cast : ℤ → ℂ))).toRingHom.comp
        (map (starRingEnd ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [MvPolynomial.linearSubst_eq_aeval]
  exact DFunLike.congr_fun h P

/-- Evaluation of the conjugate polynomial at the conjugate point. -/
theorem eval_cmap (v : Fin 2 → ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    eval (fun i => starRingEnd ℂ (v i)) (map (starRingEnd ℂ) P) = starRingEnd ℂ (eval v P) := by
  have h : (eval (fun i => starRingEnd ℂ (v i))).comp (map (starRingEnd ℂ)) =
      (starRingEnd ℂ).comp (eval v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h P

variable (w : ℕ)

/-- Conjugation of the coefficients of a binary form of degree `w`, as a conjugate-linear map. -/
noncomputable def binaryConjLin :
    homogeneousSubmodule (Fin 2) ℂ w →ₛₗ[starRingEnd ℂ] homogeneousSubmodule (Fin 2) ℂ w where
  toFun P := ⟨map (starRingEnd ℂ) (P : MvPolynomial (Fin 2) ℂ),
    (mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp P.2).map _)⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by
    simp [MvPolynomial.smul_eq_C_mul])

variable {w}

@[simp]
theorem coe_binaryConjLin (P : homogeneousSubmodule (Fin 2) ℂ w) :
    (binaryConjLin w P : MvPolynomial (Fin 2) ℂ) = map (starRingEnd ℂ) (P : MvPolynomial (Fin 2) ℂ) :=
  rfl

theorem binaryConjLin_involutive : Function.Involutive (binaryConjLin w) := fun P =>
  Subtype.ext (cmap_cmap (P : MvPolynomial (Fin 2) ℂ))

variable (w) in
/-- **Conjugation of coefficients** on binary forms of degree `w`: a conjugate-linear
involution. -/
noncomputable def binaryConj :
    homogeneousSubmodule (Fin 2) ℂ w ≃ₛₗ[starRingEnd ℂ] homogeneousSubmodule (Fin 2) ℂ w :=
  LinearEquiv.ofInvolutive (binaryConjLin w) binaryConjLin_involutive

@[simp]
theorem coe_binaryConj (P : homogeneousSubmodule (Fin 2) ℂ w) :
    (binaryConj w P : MvPolynomial (Fin 2) ℂ) = map (starRingEnd ℂ) (P : MvPolynomial (Fin 2) ℂ) :=
  rfl

/-- Conjugation commutes with the action of integer matrices. -/
theorem binaryConj_binaryFormRep (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) ℂ w) :
    binaryConj w (TauCeti.binaryFormRep ℂ w (op M) P) =
      TauCeti.binaryFormRep ℂ w (op M) (binaryConj w P) := by
  apply Subtype.ext
  rw [coe_binaryConj, TauCeti.coe_binaryFormRep_apply, TauCeti.coe_binaryFormRep_apply,
    coe_binaryConj, cmap_linearSubst]

/-- Conjugation preserves the period polynomials. -/
theorem binaryConj_mem_periodPolynomials {P : homogeneousSubmodule (Fin 2) ℂ w}
    (hP : P ∈ TauCeti.periodPolynomials ℂ w) : binaryConj w P ∈ TauCeti.periodPolynomials ℂ w := by
  rw [TauCeti.mem_periodPolynomials_iff] at hP ⊢
  obtain ⟨h1, h2⟩ := hP
  refine ⟨?_, ?_⟩
  · have h := congrArg (binaryConj w) h1
    rwa [map_add, binaryConj_binaryFormRep, map_zero] at h
  · have h := congrArg (binaryConj w) h2
    rwa [map_add, map_add, binaryConj_binaryFormRep, binaryConj_binaryFormRep,
      binaryConj_binaryFormRep, map_zero] at h

/-! ## Forms are determined by their values at real points -/

theorem eval_dehom (x : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    Polynomial.eval x (dehom ℂ P) = eval ![x, 1] P := by
  have h : (Polynomial.aeval x).comp (dehom ℂ) = MvPolynomial.aeval ![x, 1] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [dehom]
  have h2 := DFunLike.congr_fun h P
  rw [AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval] at h2
  rw [h2]
  rfl

/-- Two binary forms of degree `w` that agree at all points `(x, 1)` with `x` real are equal. -/
theorem eq_of_eval_real {P Q : MvPolynomial (Fin 2) ℂ} (hP : P.IsHomogeneous w)
    (hQ : Q.IsHomogeneous w) (h : ∀ x : ℝ, eval ![(x : ℂ), 1] P = eval ![(x : ℂ), 1] Q) :
    P = Q := by
  apply dehom_injOn w hP hQ
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
  rintro _ ⟨x, rfl⟩
  simp only [Set.mem_ofPred_eq, eval_dehom]
  exact h x

/-! ## The period polynomial -/

/-- **Conjugation of the period polynomial**: `conj(r_f) = −r_{f^c} ∣ ε`, `ε = diag(−1, 1)`,
for `w` even. -/
theorem binaryConj_periodPolynomial {k : ℤ} (hk : k = w + 2) (hw : Even w)
    (f : CuspForm 𝒮ℒ k) :
    binaryConj w (TauCeti.periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) =
      -TauCeti.binaryFormRep ℂ w (op !![-1, 0; 0, 1])
        (TauCeti.periodPolynomial hk (conjForm f) : homogeneousSubmodule (Fin 2) ℂ w) := by
  apply Subtype.ext
  refine eq_of_eval_real (w := w) ((mem_homogeneousSubmodule _ _).mp (Subtype.property _))
    ((mem_homogeneousSubmodule _ _).mp (Subtype.property _)) fun x => ?_
  have hv : (fun i => starRingEnd ℂ ((![(x : ℂ), 1] : Fin 2 → ℂ) i)) = ![(x : ℂ), 1] := by
    funext i
    fin_cases i <;> simp
  have hmul : ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ)) *ᵥ
      ![(x : ℂ), 1] = ![-(x : ℂ), 1] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [coe_binaryConj, ← hv, eval_cmap, hv, conj_eval_periodPolynomial hk hw]
  simp only [Submodule.coe_neg, map_neg, TauCeti.coe_binaryFormRep_apply,
    MvPolynomial.eval_linearSubst, hmul]

end TauTrack.Cohomology
