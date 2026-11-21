module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Data.ZMod.Basic

/-!
# Challenge: the twelve characters of the modular group

Let `S = (0 −1; 1 0)` and `T = (1 1; 0 1)` be the standard generators of `SL(2, ℤ)` (Mathlib's
`ModularGroup.S` and `ModularGroup.T`), and let `η` be the Dedekind eta function (Mathlib's
`ModularForm.eta`). The statements say:

1. `character_determined`: every homomorphism `χ` from `SL(2, ℤ)` to a commutative group satisfies
   `χ(S) = χ(T)⁻³` and `χ(T)¹² = 1`, and is determined by `χ(T)`.
2. `exists_pitch`: there is an additive map `p : SL(2, ℤ) → ℤ/12` with `p(T) = 1`, `p(S) = 9` and
   `p(−1) = 6`, given on `γ = (a b; c d)` by the explicit formula (entries reduced modulo 12)
   * `p(γ) = (a + d)c − bd(c² − 1) − 3c` for odd `c`,
   * `p(γ) = (a + d)c − bd(c² − 1) + 3d − 3 − 3cd` for even `c`,

   such that
   * every homomorphism `χ` from `SL(2, ℤ)` to a commutative group is `γ ↦ χ(T)^{p(γ)}`: the map
     `p` is the largest abelian quotient of the modular group;
   * `η(γτ)² = e^{2πi p(γ)/12} (cτ + d) η(τ)²` for every `τ` in the upper half-plane: `p` is the
     exponent of the multiplier of `η²`, a form of weight 1 (this is the classical closed form of
     the multiplier of `η`, squared);
   * every character `χ : SL(2, ℤ) → ℂˣ` is `γ ↦ e^{2πi k p(γ)/12}` for exactly one `k` in `ℤ/12`.

So the modular group has exactly twelve characters, the powers of the multiplier of
`η² = Δ^{1/12}`, and its abelianisation is `ℤ/12` through `p`. Only Mathlib definitions
are used. This file states the results only; the proofs are in `Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups Real

namespace Tones

theorem character_determined {G : Type*} [CommGroup G] (χ : SL(2, ℤ) →* G) :
    χ S = (χ T ^ 3)⁻¹ ∧ χ T ^ 12 = 1 ∧ ∀ χ' : SL(2, ℤ) →* G, χ' T = χ T → χ' = χ := by
  sorry

theorem exists_pitch.{u} :
    ∃ p : SL(2, ℤ) → ZMod 12,
      (∀ γ δ, p (γ * δ) = p γ + p δ) ∧ p T = 1 ∧ p S = 9 ∧ p (-1) = 6 ∧
      (∀ (G : Type u) [CommGroup G] (χ : SL(2, ℤ) →* G) (γ : SL(2, ℤ)), χ γ = χ T ^ (p γ).val) ∧
      (∀ (γ : SL(2, ℤ)) (a b c d : ZMod 12),
        a = ((γ 0 0 : ℤ) : ZMod 12) → b = ((γ 0 1 : ℤ) : ZMod 12) →
        c = ((γ 1 0 : ℤ) : ZMod 12) → d = ((γ 1 1 : ℤ) : ZMod 12) →
        p γ = if Odd (γ 1 0) then (a + d) * c - b * d * (c * c - 1) - 3 * c
          else (a + d) * c - b * d * (c * c - 1) + 3 * d - 3 - 3 * c * d) ∧
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), ModularForm.eta ↑(γ • τ) ^ 2 =
        Complex.exp (2 * π * Complex.I * ((p γ).val : ℂ) / 12) *
          (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * ModularForm.eta ↑τ ^ 2) ∧
      ∀ χ : SL(2, ℤ) →* ℂˣ, ∃! k : ZMod 12,
        ∀ γ, (χ γ : ℂ) = Complex.exp (2 * π * Complex.I * (((k * p γ).val : ℕ) : ℂ) / 12) := by
  sorry

end Tones
