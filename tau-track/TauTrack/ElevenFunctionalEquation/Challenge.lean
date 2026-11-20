module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Challenge: the functional equation of the `L`-function of the newform of level 11

Let `f(z) = η(z)² η(11z)² = ∑ a(n) qⁿ`, where `η` is the Dedekind eta function (Mathlib's
`ModularForm.eta`). This is the newform of weight 2 and level 11 (LMFDB label 11.2.a.a), the
modular form of the elliptic curves of conductor 11. Let `L(f, s)` be its `L`-function (Mathlib's
`ModularForm.L`), the entire function equal to `∑ a(n) n^{−s}` for `Re s > 2`, and let
`Λ(s) = (2π)^{−s} Γ(s) L(f, s)` be its completion (Mathlib's `ModularForm.Λ`), the Mellin
transform of `t ↦ f(it)`. The statements say:

1. `fricke_relation`: `f(−1/(11z)) = −11 z² f(z)`, written with `η`. The Fricke involution
   `z ↦ −1/(11z)` therefore acts on `f` with eigenvalue `−1`.
2. `exists_newform_functional_equation`: `f` is a cusp form of weight 2 for `Γ₀(11)` such that
   * `Λ(2 − s) = 11^{s−1} Λ(s)` for every complex `s`; equivalently `11^{s/2} Λ(s)` is invariant
     under `s ↦ 2 − s`, so the functional equation has root number `+1`;
   * `L(f, 1)` is a positive real number, so the order of vanishing at the centre is `0`;
   * `11^{s/2} Λ(s)` is real for `s = 1 + it` with `t` real: on the critical line the completed
     `L`-function is a real function of `t`, the analogue of Hardy's function `Z(t)` for `ζ`.

Only Mathlib definitions are used. This file states the results only; the proofs are in
`Solution.lean`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ElevenFunctionalEquation

theorem fricke_relation (z : ℂ) (hz : 0 < z.im) :
    ModularForm.eta (-1 / (11 * z)) ^ 2 * ModularForm.eta (-1 / z) ^ 2 =
      -(11 * z ^ 2) * (ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) := by
  sorry

theorem exists_newform_functional_equation (hk : (0 : ℤ) < 2) :
    ∃ f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2,
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ s : ℂ, ModularForm.Λ hk f (2 - s) = (11 : ℂ) ^ (s - 1) * ModularForm.Λ hk f s) ∧
      (∃ r : ℝ, 0 < r ∧ ModularForm.L hk f 1 = r) ∧
      ∀ t : ℝ, ((11 : ℂ) ^ ((1 + t * Complex.I) / 2) *
        ModularForm.Λ hk f (1 + t * Complex.I)).im = 0 := by
  sorry

end ElevenFunctionalEquation
