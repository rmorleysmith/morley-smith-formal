module

public import TauCeti.LinearAlgebra.IntegralLattice.Level
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import TauCeti.LinearAlgebra.IntegralLattice.Even
import Mathlib.Tactic

/-!
# A lattice of level 11 with square discriminant

The binary form `x² + xy + 3y²` has discriminant `−11`; its Gram matrix (for the norm `2Q`) is
`B = (2 1; 1 6)`, of determinant `11`. The orthogonal sum of two copies is an even lattice of
rank 4 with Gram matrix `G = B ⊕ B`, determinant `121 = 11²`, and level `11`: `11 · G⁻¹` is the
integral matrix `(6 −1; −1 2) ⊕ (6 −1; −1 2)`, with even diagonal.

* `lattice11`: the lattice, as TauCeti's `IntegralLattice` on `ℚ⁴` built from `G`
  (`IntegralLattice.ofGramMatrix`).
* `isEven_lattice11`, `isPosDef_lattice11`, `determinant_lattice11` (`= 121`),
  `level_lattice11_dvd` (`level ∣ 11`).

Its theta series `θ(z) = ∑ q^{Q(x, y) + Q(z, w)}` is therefore a modular form of weight 2 on
`Γ₀(11)` with trivial character (`TauTrack.ElevenFive.Theta`).
-/

@[expose] public section

open TauCeti TauCeti.IntegralLattice

namespace TauTrack.ElevenFive

/-- The Gram matrix `(2 1; 1 6) ⊕ (2 1; 1 6)` of two copies of `x² + xy + 3y²`. -/
def gram11 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 1, 0, 0; 1, 6, 0, 0; 0, 0, 2, 1; 0, 0, 1, 6]

theorem gram11_isSymm : gram11.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The lattice of rank 4, level 11 and determinant `11²`.** -/
noncomputable def lattice11 : IntegralLattice (Fin 4 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 4)) gram11 gram11_isSymm

theorem isEven_lattice11 : lattice11.IsEven := by
  rw [lattice11, isEven_ofGramMatrix_iff]
  intro i
  fin_cases i <;> decide

theorem gram11_det : gram11.det = 121 := by
  simp [gram11, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem isPosDef_lattice11 : lattice11.IsPosDef := by
  rw [lattice11, isPosDef_ofGramMatrix_iff]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gram11]
  · simp [gram11, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    by_contra hle
    rw [not_lt] at hle
    apply hx
    have a1 := sq_nonneg (2 * x 0 + x 1)
    have a2 := sq_nonneg (x 1)
    have a3 := sq_nonneg (2 * x 2 + x 3)
    have a4 := sq_nonneg (x 3)
    have hF : (2 * x 0 + x 1) ^ 2 + 11 * x 1 ^ 2 + (2 * x 2 + x 3) ^ 2 + 11 * x 3 ^ 2 ≤ 0 := by
      nlinarith [hle]
    have h1 : x 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by nlinarith)
    have h3 : x 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by nlinarith)
    have h0 : 2 * x 0 + x 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by nlinarith)
    have h2 : 2 * x 2 + x 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by nlinarith)
    funext i
    fin_cases i <;> simp <;> linarith

/-- **The determinant is `121 = 11²`.** -/
theorem determinant_lattice11 : lattice11.determinant = 121 := by
  rw [lattice11, determinant_ofGramMatrix, gram11_det]

instance : lattice11.IsNondegenerate :=
  isNondegenerate_ofGramMatrix _ _ _ (by convert (show gram11.det ≠ 0 by rw [gram11_det]; norm_num))

/-- `11 · G⁻¹`, integral with even diagonal. -/
def gram11Adj : Matrix (Fin 4) (Fin 4) ℤ :=
  !![6, -1, 0, 0; -1, 2, 0, 0; 0, 0, 6, -1; 0, 0, -1, 2]

/-- **The level divides 11.** -/
theorem level_lattice11_dvd : (lattice11.level : ℤ) ∣ 11 := by
  rw [level_dvd_iff_gramMatrix lattice11
    (ofGramMatrix.basis (Pi.basisFun ℚ (Fin 4)) gram11 gram11_isSymm)]
  refine ⟨gram11Adj, fun i ↦ ?_, ?_⟩
  · fin_cases i <;> decide
  · rw [show lattice11.gramMatrix (ofGramMatrix.basis (Pi.basisFun ℚ (Fin 4)) gram11
      gram11_isSymm) = gram11 from gramMatrix_ofGramMatrix _ _ _]
    have hinv : (gram11.map (Int.cast : ℤ → ℚ))⁻¹ =
        (11 : ℚ)⁻¹ • gram11Adj.map (Int.cast : ℤ → ℚ) := by
      refine Matrix.inv_eq_right_inv ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gram11, gram11Adj, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
    rw [hinv, smul_smul]
    norm_num

end TauTrack.ElevenFive
