module

public import TauTrack.Cohomology.Pairing
public import TauTrack.Cohomology.IntegralHecke
import Mathlib.Tactic

/-!
# The integral pairing on the lattice `H¹_par(SL(2, ℤ), V_w)`

The invariant pairing on binary forms takes the values `(−1)^k / C(w, k)` on monomials, so `w!`
times it is integer-valued on forms with integer coefficients.

* `intPairing w`: the integral form `w! ⟨ , ⟩` on binary forms over `ℤ`, with
  `intPairing_cast : (intPairing w P Q : ℂ) = w! ⟨P, Q⟩`.
* `intBracket w`: `w! {P, Q}` on binary forms over `ℤ` (`intBracket_cast`).
* `latticePairing hw`: **an integer-valued antisymmetric bilinear form on the lattice**
  `L_w = W_w(ℤ) ⧸ ℤ (X^w − Y^w)`, with

  `latticePairing_cast : (latticePairing hw u v : ℂ) = w! · parabolicPairing (ι u) (ι v)`,

  where `ι` is the map of the lattice into the complex cohomology, and
  `latticePairing_antisymm`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups Nat

namespace TauTrack.Cohomology

/-- Two biadditive functions on a free `ℤ`-module that agree on a basis are equal. -/
theorem biadditive_ext {M A ι : Type*} [AddCommGroup M] [AddCommGroup A]
    (b : Module.Basis ι ℤ M) (f g : M → M → A)
    (hf₁ : ∀ x y z, f (x + y) z = f x z + f y z) (hf₂ : ∀ x y z, f x (y + z) = f x y + f x z)
    (hg₁ : ∀ x y z, g (x + y) z = g x z + g y z) (hg₂ : ∀ x y z, g x (y + z) = g x y + g x z)
    (h : ∀ i k, f (b i) (b k) = g (b i) (b k)) (x y : M) : f x y = g x y := by
  have h1 : ∀ i y, f (b i) y = g (b i) y := by
    intro i y
    have e : (AddMonoidHom.mk' (f (b i)) (hf₂ (b i))).toIntLinearMap =
        (AddMonoidHom.mk' (g (b i)) (hg₂ (b i))).toIntLinearMap :=
      b.ext fun k => h i k
    exact LinearMap.congr_fun e y
  have e : (AddMonoidHom.mk' (fun x => f x y) (fun x x' => hf₁ x x' y)).toIntLinearMap =
      (AddMonoidHom.mk' (fun x => g x y) (fun x x' => hg₁ x x' y)).toIntLinearMap :=
    b.ext fun i => h1 i y
  exact LinearMap.congr_fun e x

variable {w : ℕ}

/-! ## The integral pairing on binary forms -/

variable (w) in
/-- The value of `w! ⟨ , ⟩` on monomials. -/
def intPairingCoeff (i k : Fin (w + 1)) : ℤ :=
  if i = Fin.rev k then (-1) ^ (k : ℕ) * ((k : ℕ)! * (w - k)! : ℕ) else 0

variable (w) in
/-- **The integral invariant pairing** `w! ⟨ , ⟩` on binary forms with integer coefficients. -/
noncomputable def intPairing :
    homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℤ :=
  (TauCeti.binaryFormMonomialBasis ℤ w).constr ℤ fun i =>
    (TauCeti.binaryFormMonomialBasis ℤ w).constr ℤ fun k => intPairingCoeff w i k

theorem intPairing_basis (i k : Fin (w + 1)) :
    intPairing w (TauCeti.binaryFormMonomialBasis ℤ w i)
        (TauCeti.binaryFormMonomialBasis ℤ w k) = intPairingCoeff w i k := by
  rw [intPairing, Module.Basis.constr_basis, Module.Basis.constr_basis]

theorem coeffMap_basis (j : Fin (w + 1)) :
    coeffMap w (TauCeti.binaryFormMonomialBasis ℤ w j) = TauCeti.binaryFormMonomialBasis ℂ w j :=
  TauCeti.mapHomogeneousSubmodule_binaryFormMonomialBasis (Int.castRingHom ℂ) j

/-- **`intPairing` is `w!` times the invariant pairing.** -/
theorem intPairing_cast (P Q : homogeneousSubmodule (Fin 2) ℤ w) :
    ((intPairing w P Q : ℤ) : ℂ) =
      (w ! : ℂ) * invariantPairing ℂ w (coeffMap w P) (coeffMap w Q) := by
  refine biadditive_ext (TauCeti.binaryFormMonomialBasis ℤ w)
    (fun P Q => ((intPairing w P Q : ℤ) : ℂ))
    (fun P Q => (w ! : ℂ) * invariantPairing ℂ w (coeffMap w P) (coeffMap w Q))
    (fun x y z => by simp) (fun x y z => by simp)
    (fun x y z => by simp [mul_add]) (fun x y z => by simp [mul_add]) (fun i k => ?_) P Q
  simp only [intPairing_basis, coeffMap_basis, invariantPairing_basis, intPairingCoeff]
  have hk : (k : ℕ) ≤ w := Nat.lt_succ_iff.mp k.2
  by_cases h : i = Fin.rev k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hc : (w.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
    have hf : ((w ! : ℕ) : ℂ) = (w.choose k : ℂ) * ((k : ℕ)! : ℂ) * ((w - k)! : ℂ) := by
      rw [← Nat.choose_mul_factorial_mul_factorial hk]
      push_cast
      ring
    push_cast
    rw [hf]
    field_simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp

/-! ## The integral bracket -/

variable (w) in
/-- The integral bracket `w! {P, Q}` on binary forms with integer coefficients. -/
noncomputable def intBracket :
    homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] homogeneousSubmodule (Fin 2) ℤ w →ₗ[ℤ] ℤ :=
  (intPairing w).comp
    (TauCeti.binaryFormRep ℤ w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) -
      TauCeti.binaryFormRep ℤ w (op ((T⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))

/-- **`intBracket` is `w!` times the bracket.** -/
theorem intBracket_cast (P Q : homogeneousSubmodule (Fin 2) ℤ w) :
    ((intBracket w P Q : ℤ) : ℂ) = (w ! : ℂ) * bracket ℂ w (coeffMap w P) (coeffMap w Q) := by
  rw [intBracket, LinearMap.comp_apply, intPairing_cast, LinearMap.sub_apply, map_sub,
    coeffMap_binaryFormRep, coeffMap_binaryFormRep, bracket, LinearMap.comp_apply,
    LinearMap.sub_apply]

theorem intBracket_antisymm (hw : Even w) (P Q : homogeneousSubmodule (Fin 2) ℤ w) :
    intBracket w Q P = -intBracket w P Q := by
  have h : ((intBracket w Q P : ℤ) : ℂ) = ((-intBracket w P Q : ℤ) : ℂ) := by
    rw [Int.cast_neg, intBracket_cast, intBracket_cast, bracket_antisymm hw]
    ring
  exact_mod_cast h

theorem coeffMap_periodIncl_eisensteinPeriodInt (hw : Even w) :
    coeffMap w (periodIncl ℤ w (eisensteinPeriodInt w hw)) =
      TauCeti.eisensteinPeriodPolynomial ℂ w := by
  apply Subtype.ext
  rw [coe_coeffMap]
  simp [eisensteinPeriodInt, periodIncl, TauCeti.coe_eisensteinPeriodPolynomial]

/-- `X^w − Y^w` is orthogonal to the integral period polynomials. -/
theorem intBracket_eisenstein (hw : Even w) (Q : PeriodSpace ℤ w) :
    intBracket w (periodIncl ℤ w Q) (periodIncl ℤ w (eisensteinPeriodInt w hw)) = 0 := by
  have h : ((intBracket w (periodIncl ℤ w Q) (periodIncl ℤ w (eisensteinPeriodInt w hw)) : ℤ) : ℂ)
      = ((0 : ℤ) : ℂ) := by
    have hmem : coeffMap w (periodIncl ℤ w Q) ∈ TauCeti.periodPolynomials ℂ w :=
      coeffMap_mem_periodPolynomials (periodSpaceEquiv ℤ w Q).2
    rw [intBracket_cast, coeffMap_periodIncl_eisensteinPeriodInt, bracket_eisenstein hw hmem,
      mul_zero, Int.cast_zero]
  exact_mod_cast h

/-! ## The pairing on the lattice -/

variable (w) in
/-- The integral bracket on integral period polynomials. -/
noncomputable def intPeriodPairing : PeriodSpace ℤ w →ₗ[ℤ] PeriodSpace ℤ w →ₗ[ℤ] ℤ :=
  (intBracket w).compl₁₂ (periodIncl ℤ w) (periodIncl ℤ w)

theorem intPeriodPairing_apply (P Q : PeriodSpace ℤ w) :
    intPeriodPairing w P Q = intBracket w (periodIncl ℤ w P) (periodIncl ℤ w Q) :=
  rfl

/-- **The integral pairing on the lattice** `L_w = W_w(ℤ) ⧸ ℤ (X^w − Y^w)`: it is `w!` times the
pairing on parabolic cohomology. -/
noncomputable def latticePairing (hw : Even w) :
    ParabolicLattice w hw →ₗ[ℤ] ParabolicLattice w hw →ₗ[ℤ] ℤ :=
  ((ℤ ∙ eisensteinPeriodInt w hw).liftQ
    ((ℤ ∙ eisensteinPeriodInt w hw).liftQ (intPeriodPairing w) (by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      refine LinearMap.ext fun Q => ?_
      rw [intPeriodPairing_apply, intBracket_antisymm hw, intBracket_eisenstein hw]
      rfl)).flip (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact intBracket_eisenstein hw P)).flip

@[simp]
theorem latticePairing_mk (hw : Even w) (P Q : PeriodSpace ℤ w) :
    latticePairing hw (Submodule.Quotient.mk P) (Submodule.Quotient.mk Q) =
      intPeriodPairing w P Q :=
  rfl

/-- **The lattice pairing is `w!` times the pairing on the complex cohomology.** -/
theorem latticePairing_cast (hw : Even w) (u v : ParabolicLattice w hw) :
    ((latticePairing hw u v : ℤ) : ℂ) =
      (w ! : ℂ) * parabolicPairing (K := ℂ) hw (latticeMap hw u) (latticeMap hw v) := by
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [latticePairing_mk, intPeriodPairing_apply, intBracket_cast, latticeMap_mk, latticeMap_mk,
    parabolicPairing_mk, periodPairing_apply]
  rfl

/-- **The lattice pairing is antisymmetric.** -/
theorem latticePairing_antisymm (hw : Even w) (u v : ParabolicLattice w hw) :
    latticePairing hw v u = -latticePairing hw u v := by
  obtain ⟨P, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [latticePairing_mk, latticePairing_mk, intPeriodPairing_apply, intPeriodPairing_apply,
    intBracket_antisymm hw]

end TauTrack.Cohomology
