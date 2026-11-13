module

public import Mathlib
public import TauTrack.Siegel.ThetaModular

/-!
# Solution: the theta series of an even unimodular lattice is a Siegel modular form

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
`SL(2, ℤ)`. Only Mathlib definitions are used. This file restates `Challenge.lean` word for word and proves it from `TauTrack/Siegel`.
-/

@[expose] public section

open Matrix
open scoped Real

namespace SiegelTheta

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The term `exp(π i · tr(G(x) Z))` of the theta series attached to a tuple `x ∈ Lⁿ`. -/
noncomputable def term (L : Submodule ℤ E) (x : n → L) (Z : Matrix n n ℂ) : ℂ :=
  Complex.exp (π * Complex.I * ∑ i, ∑ j, ((inner ℝ (x i : E) (x j : E) : ℝ) : ℂ) * Z j i)

/-- The theta series of `L` in degree `n`. -/
noncomputable def theta (L : Submodule ℤ E) (Z : Matrix n n ℂ) : ℂ :=
  ∑' x : n → L, term L x Z

/-- The term of the Challenge is the term used in the proofs. -/
theorem term_eq (L : Submodule ℤ E) (x : n → L) (Z : Matrix n n ℂ) :
    term L x Z = TauTrack.Siegel.thetaTerm x Z := by
  rw [term, TauTrack.Siegel.thetaTerm]
  congr 2

/-- The theta series of the Challenge is the theta series used in the proofs. -/
theorem theta_eq (L : Submodule ℤ E) (Z : Matrix n n ℂ) :
    theta L Z = TauTrack.Siegel.siegelTheta L Z := by
  rw [theta, TauTrack.Siegel.siegelTheta]
  exact tsum_congr fun x => term_eq L x Z

theorem summable_norm (L : Submodule ℤ E) [DiscreteTopology L] (Z : Matrix n n ℂ)
    (hY : (Z.map Complex.im).PosDef) : Summable fun x : n → L => ‖term L x Z‖ := by
  simpa only [term_eq] using TauTrack.Siegel.summable_norm_thetaTerm L hY

theorem differentiableOn (L : Submodule ℤ E) [DiscreteTopology L] :
    DifferentiableOn ℂ (fun X : n → n → ℂ => theta L (Matrix.of X))
      {X | (((1 / 2 : ℂ) • (Matrix.of X + (Matrix.of X)ᵀ)).map Complex.im).PosDef} := by
  have hset : {X : n → n → ℂ |
      (((1 / 2 : ℂ) • (Matrix.of X + (Matrix.of X)ᵀ)).map Complex.im).PosDef} =
      TauTrack.Siegel.domain n := by
    ext X
    exact ⟨fun h => ⟨TauTrack.Siegel.symPart_isSymm _, h⟩, fun h => h.2⟩
  rw [hset]
  exact (TauTrack.Siegel.differentiableOn_siegelTheta L).congr fun X _ => theta_eq L _

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
  have hL : ZLattice.IsEven L := ZLattice.isEven_iff.mpr heven
  have hU : ZLattice.IsUnimodular L := by
    rw [ZLattice.isUnimodular_iff_eq_dual]
    ext w
    rw [ZLattice.mem_dual]
    exact hunimodular w
  have h : TauTrack.Siegel.siegelTheta L
      (TauTrack.Siegel.act (TauTrack.Siegel.ofInt ⟨M, hM⟩).1 Z) =
      TauTrack.Siegel.j (TauTrack.Siegel.ofInt ⟨M, hM⟩).1 Z ^ (k : ℤ) *
        TauTrack.Siegel.siegelTheta L Z :=
    TauTrack.Siegel.siegelTheta_smul hL hU hk ⟨M, hM⟩ ⟨Z, hZ, hY⟩
  have hM' : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ ∈
      symplecticGroup n ℤ := by rwa [fromBlocks_toBlocks]
  have hγ : (⟨M, hM⟩ : symplecticGroup n ℤ) =
      ⟨fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂, hM'⟩ :=
    Subtype.ext (fromBlocks_toBlocks M).symm
  rw [TauTrack.Siegel.act, TauTrack.Siegel.j, hγ, TauTrack.Siegel.num_ofInt_fromBlocks,
    TauTrack.Siegel.den_ofInt_fromBlocks, zpow_natCast] at h
  simp only [TauTrack.Siegel.ci] at h
  rw [theta_eq, theta_eq]
  exact h

theorem bounded (L : Submodule ℤ E) [DiscreteTopology L] (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, ∀ Z : Matrix n n ℂ,
      (Z.map Complex.im - c • (1 : Matrix n n ℝ)).PosSemidef → ‖theta (n := n) L Z‖ ≤ B :=
  ⟨_, fun Z hZ => by rw [theta_eq]; exact TauTrack.Siegel.norm_siegelTheta_le L hc hZ⟩

end SiegelTheta
