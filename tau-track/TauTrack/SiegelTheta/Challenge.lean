module

public import Mathlib

/-!
# Challenge: the theta series of an even unimodular lattice is a Siegel modular form

Let `L` be an even unimodular lattice of rank `2k` in a Euclidean space `E`, and `n` a finite
index type (the degree). For a complex `n × n` matrix `Z` the theta series of degree `n` is

  `Θ_L(Z) = ∑_{x ∈ Lⁿ} exp(π i · tr(G(x) Z))`,   `G(x)_{ij} = ⟨x_i, x_j⟩`.

The statements say that `Θ_L` is a Siegel modular form of weight `k` for `Sp(2n, ℤ)`:

1. `summable_norm`: the series converges absolutely when `Im Z` is positive definite;
2. `differentiableOn`: `Θ_L` is holomorphic, as a function of the `n²` entries, on the open set
   of matrices whose symmetric part has positive definite imaginary part (this set contains the
   Siegel upper half-space `ℍ_n`);
3. `map_symplectic`: for `M = (A B; C D)` in `Sp(2n, ℤ)` (Mathlib's `Matrix.symplecticGroup n ℤ`)
   and `Z ∈ ℍ_n`,  `Θ_L((A Z + B)(C Z + D)⁻¹) = det(C Z + D)^k · Θ_L(Z)`;
4. `bounded`: `Θ_L` is bounded on each region `Im Z ≥ c · 1`, `c > 0`.

"Even" means `‖v‖²` is an even integer for `v ∈ L`; "unimodular" means `L` is its own dual
lattice. For `n = 1` this is the classical fact that `Θ_L` is a modular form of weight `k` for
`SL(2, ℤ)`. Only Mathlib definitions are used. This file states the results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

open Matrix
open scoped Real

namespace SiegelTheta

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The term `exp(π i · tr(G(x) Z))` of the theta series attached to a tuple `x ∈ Lⁿ`. -/
noncomputable def term (L : Submodule ℤ E) (x : n → L) (Z : Matrix n n ℂ) : ℂ :=
  Complex.exp (π * Complex.I * ∑ i, ∑ j, ((inner ℝ (x i : E) (x j : E) : ℝ) : ℂ) * Z j i)

/-- The theta series of `L` in degree `n`. -/
noncomputable def theta (L : Submodule ℤ E) (Z : Matrix n n ℂ) : ℂ :=
  ∑' x : n → L, term L x Z

theorem summable_norm (L : Submodule ℤ E) [DiscreteTopology L] (Z : Matrix n n ℂ)
    (hY : (Z.map Complex.im).PosDef) : Summable fun x : n → L => ‖term L x Z‖ := by
  sorry

theorem differentiableOn (L : Submodule ℤ E) [DiscreteTopology L] :
    DifferentiableOn ℂ (fun X : n → n → ℂ => theta L (Matrix.of X))
      {X | (((1 / 2 : ℂ) • (Matrix.of X + (Matrix.of X)ᵀ)).map Complex.im).PosDef} := by
  sorry

theorem map_symplectic (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (heven : ∀ v ∈ L, ∃ m : ℤ, ‖v‖ ^ 2 = 2 * m)
    (hunimodular : ∀ w : E, w ∈ L ↔ ∀ v ∈ L, ∃ m : ℤ, inner ℝ w v = m)
    (k : ℕ) (hk : Module.finrank ℝ E = 2 * k)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℤ) (hM : M ∈ symplecticGroup n ℤ)
    (Z : Matrix n n ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    theta L ((M.toBlocks₁₁.map (Int.cast : ℤ → ℂ) * Z + M.toBlocks₁₂.map (Int.cast : ℤ → ℂ)) *
        (M.toBlocks₂₁.map (Int.cast : ℤ → ℂ) * Z + M.toBlocks₂₂.map (Int.cast : ℤ → ℂ))⁻¹) =
      (M.toBlocks₂₁.map (Int.cast : ℤ → ℂ) * Z + M.toBlocks₂₂.map (Int.cast : ℤ → ℂ)).det ^ k *
        theta L Z := by
  sorry

theorem bounded (L : Submodule ℤ E) [DiscreteTopology L] (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, ∀ Z : Matrix n n ℂ,
      (Z.map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef → ‖theta (n := n) L Z‖ ≤ B := by
  sorry

end SiegelTheta
