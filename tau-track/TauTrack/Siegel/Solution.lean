module

public import Mathlib
public import TauTrack.Siegel.Basic

/-!
# Solution: the symplectic group acts on the Siegel upper half-space

The Siegel upper half-space `ℍ_n` is the set of symmetric complex `n × n` matrices `Z` whose
imaginary part is positive definite. A real symplectic matrix `M = (A B; C D)` (Mathlib's
`Matrix.symplecticGroup`) acts on it by `Z ↦ (A Z + B)(C Z + D)⁻¹`. The statements say:

1. `C Z + D` is invertible;
2. `(A Z + B)(C Z + D)⁻¹` is again symmetric with positive definite imaginary part;
3. the identity matrix acts trivially, and `(M N)·Z = M·(N·Z)`.

For `n = 1` this is the action of `SL(2, ℝ)` on the upper half-plane. Only Mathlib definitions
are used. Restates `Challenge.lean` and proves it from `TauTrack.Siegel.Basic`.
-/

@[expose] public section

open Matrix

namespace SiegelHalfSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(A Z + B)(C Z + D)⁻¹` for the real `2n × 2n` matrix `M = (A B; C D)`. -/
noncomputable def act (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  (M.toBlocks₁₁.map Complex.ofReal * Z + M.toBlocks₁₂.map Complex.ofReal) *
    (M.toBlocks₂₁.map Complex.ofReal * Z + M.toBlocks₂₂.map Complex.ofReal)⁻¹

theorem isUnit_den (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hM : M ∈ symplecticGroup n ℝ)
    (Z : Matrix n n ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    IsUnit (M.toBlocks₂₁.map Complex.ofReal * Z + M.toBlocks₂₂.map Complex.ofReal) :=
  TauTrack.Siegel.isUnit_den hM ⟨hZ, hY⟩

theorem act_mem (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hM : M ∈ symplecticGroup n ℝ)
    (Z : Matrix n n ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    (act M Z).IsSymm ∧ ((act M Z).map Complex.im).PosDef :=
  TauTrack.Siegel.isSiegel_act hM ⟨hZ, hY⟩

theorem act_one (Z : Matrix n n ℂ) : act 1 Z = Z :=
  TauTrack.Siegel.act_one Z

theorem act_mul (M N : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hN : N ∈ symplecticGroup n ℝ)
    (Z : Matrix n n ℂ) (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    act (M * N) Z = act M (act N Z) :=
  TauTrack.Siegel.act_mul M N (TauTrack.Siegel.isUnit_den hN ⟨hZ, hY⟩)

end SiegelHalfSpace
