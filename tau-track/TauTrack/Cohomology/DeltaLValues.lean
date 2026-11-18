module

public import TauTrack.Cohomology.DeltaBasis
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.LValue
import Mathlib.Tactic

/-!
# Rational ratios of the critical values of Ramanujan's `L`-function

The period polynomial `r_Δ` of `Δ` is a period polynomial of degree `10`, so modulo `X¹⁰ − Y¹⁰`
it is a complex combination of `P⁺ = X²Y²(X² − Y²)³` and
`P⁻ = 4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹` (`exists_deltaPeriod_coords`). Its coefficients are
the completed values `Λ(Δ, s) = (2π)^{−s} Γ(s) L(Δ, s)` at `s = 1, …, 11`
(TauCeti's `binaryFormMonomialBasis_repr_periodPolynomial`). Comparing coefficients:

* `Λ_delta_four`, `Λ_delta_six`: `48 Λ(Δ, 4) = 25 Λ(Δ, 2)` and `12 Λ(Δ, 6) = 5 Λ(Δ, 2)`;
* `Λ_delta_five`: `14 Λ(Δ, 5) = 9 Λ(Δ, 3)`;
* `Λ_delta_symm`: `Λ(Δ, 8) = Λ(Δ, 4)`, `Λ(Δ, 10) = Λ(Δ, 2)`, `Λ(Δ, 7) = Λ(Δ, 5)`,
  `Λ(Δ, 9) = Λ(Δ, 3)`.

For the `L`-function itself:

* `L_delta_four`: **`L(Δ, 4) = (25 π² / 72) L(Δ, 2)`**;
* `L_delta_six`: **`L(Δ, 6) = (π⁴ / 18) L(Δ, 2)`**;
* `L_delta_five`: **`L(Δ, 5) = (3 π² / 14) L(Δ, 3)`**.

These are instances of Manin's theorem on the periods of `Δ`; here they follow from the
period relations alone. The ratio of `L(Δ, 1)` to the other odd values (which involves `691`)
does not.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup Complex
open scoped MatrixGroups ModularForm Real

namespace TauTrack.Cohomology

/-- The completed `L`-function of `Δ`. -/
noncomputable abbrev ΛΔ : ℂ → ℂ :=
  ModularForm.Λ (by norm_num : (0 : ℤ) < 12) CuspForm.discriminant

/-- Ramanujan's `L`-function, continued to `ℂ`. -/
noncomputable abbrev LΔ : ℂ → ℂ :=
  ModularForm.L (by norm_num : (0 : ℤ) < 12) CuspForm.discriminant

/-- The period polynomial of `Δ`. -/
noncomputable def deltaPeriodPolynomial : TauCeti.periodPolynomials ℂ 10 :=
  TauCeti.periodPolynomial (k := 12) (w := 10) (by norm_num) CuspForm.discriminant

/-- The coefficient of `X^j Y^{10−j}` in `r_Δ`. -/
theorem repr_deltaPeriodPolynomial (j : Fin 11) :
    (TauCeti.binaryFormMonomialBasis ℂ 10).repr
        (deltaPeriodPolynomial : homogeneousSubmodule (Fin 2) ℂ 10) j =
      (-1) ^ (10 - j : ℕ) * (Nat.choose 10 j : ℂ) * I ^ (10 - j + 1 : ℕ) *
        ΛΔ ((10 - j : ℕ) + 1) :=
  TauCeti.binaryFormMonomialBasis_repr_periodPolynomial (k := 12) (w := 10) (by norm_num)
    CuspForm.discriminant j

/-- **`r_Δ` is a combination of `P⁺` and `P⁻` modulo `X¹⁰ − Y¹⁰`**: its coefficients of
`X^j Y^{10−j}`, `0 < j < 10`, are `a` times those of `P⁺` plus `b` times those of `P⁻`. -/
theorem exists_deltaPeriod_coords :
    ∃ a b : ℂ, ∀ (j : Fin 11), j ≠ 0 ∧ j ≠ 10 →
      (TauCeti.binaryFormMonomialBasis ℂ 10).repr
          (deltaPeriodPolynomial : homogeneousSubmodule (Fin 2) ℂ 10) j =
        a * (((TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaEvenInt j : ℤ) : ℂ) +
          b * (((TauCeti.binaryFormMonomialBasis ℤ 10).repr deltaOddPrim j : ℤ) : ℂ) := by
  obtain ⟨a, b, hab⟩ := exists_deltaClasses_coords
    (Submodule.Quotient.mk ((periodSpaceEquiv ℂ 10).symm deltaPeriodPolynomial))
  refine ⟨a, b * 43545600, fun j hj => ?_⟩
  have h := congrArg (coordQuot j hj) hab
  rw [deltaOddClass_eq, smul_smul, map_add, map_smul, map_smul, coordQuot_deltaEvenClass,
    coordQuot_latticeMap_deltaOddPrimLattice, smul_eq_mul, smul_eq_mul] at h
  rw [h]
  rfl

/-- The five odd coefficients. -/
theorem exists_odd_coords :
    ∃ b : ℂ, 10 * ΛΔ 2 = 4 * b ∧ 120 * ΛΔ 4 = 25 * b ∧ 252 * ΛΔ 6 = 42 * b ∧
      120 * ΛΔ 8 = 25 * b ∧ 10 * ΛΔ 10 = 4 * b := by
  obtain ⟨a, b, h⟩ := exists_deltaPeriod_coords
  have h4 : I ^ 4 = 1 := Complex.I_pow_four
  have h2 : I ^ 2 = -1 := Complex.I_sq
  have h6 : I ^ 6 = -1 := by rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, h2, one_mul]
  have h8 : I ^ 8 = 1 := by rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, h4, one_mul]
  have h10 : I ^ 10 = -1 := by rw [show (10 : ℕ) = 8 + 2 from rfl, pow_add, h8, h2, one_mul]
  have e9 := h 9 (by decide)
  have e7 := h 7 (by decide)
  have e5 := h 5 (by decide)
  have e3 := h 3 (by decide)
  have e1 := h 1 (by decide)
  rw [repr_deltaPeriodPolynomial, deltaEvenInt_eq] at e9 e7 e5 e3 e1
  simp [deltaOddPrim, Nat.choose, h2, h4, h6, h8, h10] at e9 e7 e5 e3 e1
  norm_num at e9 e7 e5 e3 e1
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e9
  · linear_combination e7
  · linear_combination e5
  · linear_combination e3
  · linear_combination e1

/-- The four even coefficients. -/
theorem exists_even_coords :
    ∃ a : ℂ, -(45 * I * ΛΔ 3) = a ∧ 210 * I * ΛΔ 5 = -(3 * a) ∧ -(210 * I * ΛΔ 7) = 3 * a ∧
      45 * I * ΛΔ 9 = -a := by
  obtain ⟨a, b, h⟩ := exists_deltaPeriod_coords
  have h4 : I ^ 4 = 1 := Complex.I_pow_four
  have h3 : I ^ 3 = -I := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq]; ring
  have h5 : I ^ 5 = I := by rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, h4]; ring
  have h7 : I ^ 7 = -I := by rw [show (7 : ℕ) = 4 + 3 from rfl, pow_add, h4, h3]; ring
  have h9 : I ^ 9 = I := by rw [show (9 : ℕ) = 4 + 5 from rfl, pow_add, h4, h5]; ring
  have e8 := h 8 (by decide)
  have e6 := h 6 (by decide)
  have e4 := h 4 (by decide)
  have e2 := h 2 (by decide)
  rw [repr_deltaPeriodPolynomial, deltaEvenInt_eq] at e8 e6 e4 e2
  simp [deltaOddPrim, Nat.choose, h3, h5, h7, h9] at e8 e6 e4 e2
  norm_num at e8 e6 e4 e2
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · linear_combination e8
  · linear_combination e6
  · linear_combination e4
  · linear_combination e2

/-! ## Ratios of the completed values -/

/-- **`48 Λ(Δ, 4) = 25 Λ(Δ, 2)`.** -/
theorem Λ_delta_four : 48 * ΛΔ 4 = 25 * ΛΔ 2 := by
  obtain ⟨b, h2, h4, -, -, -⟩ := exists_odd_coords
  linear_combination (2 / 5 : ℂ) * h4 - (5 / 2 : ℂ) * h2

/-- **`12 Λ(Δ, 6) = 5 Λ(Δ, 2)`.** -/
theorem Λ_delta_six : 12 * ΛΔ 6 = 5 * ΛΔ 2 := by
  obtain ⟨b, h2, -, h6, -, -⟩ := exists_odd_coords
  linear_combination (1 / 21 : ℂ) * h6 - (1 / 2 : ℂ) * h2

/-- **`14 Λ(Δ, 5) = 9 Λ(Δ, 3)`.** -/
theorem Λ_delta_five : 14 * ΛΔ 5 = 9 * ΛΔ 3 := by
  obtain ⟨a, h3, h5, -, -⟩ := exists_even_coords
  linear_combination (-I / 15) * h5 + (-I / 5) * h3 + (14 * ΛΔ 5 - 9 * ΛΔ 3) * Complex.I_mul_I

/-- The symmetry `s ↔ 12 − s` at the interior critical integers. -/
theorem Λ_delta_symm :
    ΛΔ 8 = ΛΔ 4 ∧ ΛΔ 10 = ΛΔ 2 ∧ ΛΔ 7 = ΛΔ 5 ∧ ΛΔ 9 = ΛΔ 3 := by
  obtain ⟨b, h2, h4, -, h8, h10⟩ := exists_odd_coords
  obtain ⟨a, h3, h5, h7, h9⟩ := exists_even_coords
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 120 : ℂ) * h8 - (1 / 120 : ℂ) * h4
  · linear_combination (1 / 10 : ℂ) * h10 - (1 / 10 : ℂ) * h2
  · linear_combination (I / 210) * h7 + (I / 210) * h5 + (ΛΔ 7 - ΛΔ 5) * Complex.I_mul_I
  · linear_combination (-I / 45) * h9 + (-I / 45) * h3 + (ΛΔ 9 - ΛΔ 3) * Complex.I_mul_I

/-! ## Ratios of the values of `L(Δ, s)` -/

/-- `L(Δ, n + 1) = Λ(Δ, n + 1) (2π)^{n+1} / n!`. -/
theorem LΔ_natCast_add_one (n : ℕ) :
    LΔ ((n : ℂ) + 1) = ΛΔ ((n : ℂ) + 1) * ((2 * π : ℂ) ^ (n + 1) / (n.factorial : ℂ)) := by
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hpi : (2 * π : ℂ) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * π : ℂ) ^ (-((n : ℂ) + 1)) = ((2 * π : ℂ) ^ (n + 1))⁻¹ := by
    rw [Complex.cpow_neg, ← Nat.cast_succ, Complex.cpow_natCast]
  rw [LΔ, ModularForm.L_apply_of_ne_zero _ _ hne, Complex.Gammaℂ_def, hpow,
    Complex.Gamma_nat_eq_factorial]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hp : (2 * π : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hpi
  field_simp

/-- **`L(Δ, 4) = (25 π² / 72) L(Δ, 2)`.** -/
theorem L_delta_four : LΔ 4 = 25 * (π : ℂ) ^ 2 / 72 * LΔ 2 := by
  have h4 := LΔ_natCast_add_one 3
  have h2 := LΔ_natCast_add_one 1
  norm_num [Nat.factorial] at h4 h2
  rw [h4, h2]
  linear_combination ((π : ℂ) ^ 4 / 18 : ℂ) * Λ_delta_four

/-- **`L(Δ, 6) = (π⁴ / 18) L(Δ, 2)`.** -/
theorem L_delta_six : LΔ 6 = (π : ℂ) ^ 4 / 18 * LΔ 2 := by
  have h6 := LΔ_natCast_add_one 5
  have h2 := LΔ_natCast_add_one 1
  norm_num [Nat.factorial] at h6 h2
  rw [h6, h2]
  linear_combination (2 * (π : ℂ) ^ 6 / 45 : ℂ) * Λ_delta_six

/-- **`L(Δ, 5) = (3 π² / 14) L(Δ, 3)`.** -/
theorem L_delta_five : LΔ 5 = 3 * (π : ℂ) ^ 2 / 14 * LΔ 3 := by
  have h5 := LΔ_natCast_add_one 4
  have h3 := LΔ_natCast_add_one 2
  norm_num [Nat.factorial] at h5 h3
  rw [h5, h3]
  linear_combination (2 * (π : ℂ) ^ 5 / 21 : ℂ) * Λ_delta_five

end TauTrack.Cohomology
