module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Int.ModEq
public import TauTrack.ElevenFive.Congruence

/-!
# Solution: the Eisenstein congruence modulo 5 at level 11

The statement of `Challenge.lean`, proved from `TauTrack.ElevenFive.Congruence` and
`TauTrack.LevelEleven.Basic`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ElevenFive

theorem eisenstein_congruence_mod_five :
    ∃ (f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2) (a : ℕ → ℤ),
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n = (a n : ℂ)) ∧
      (∀ n : ℕ, n ≠ 0 →
        a n ≡ ∑ d ∈ n.divisors.filter (fun d ↦ ¬ 11 ∣ d), (d : ℤ) [ZMOD 5]) ∧
      ∀ p : ℕ, p.Prime → p ≠ 11 → a p ≡ 1 + p [ZMOD 5] := by
  refine ⟨TauTrack.eta11Form, TauTrack.newform11, fun z ↦ ?_, TauTrack.newform11_spec,
    fun n hn ↦ ?_, fun p hp h11 ↦ TauTrack.ElevenFive.newform11_prime_modEq hp h11⟩
  · change TauTrack.eta11 z = _
    simp [TauTrack.eta11, TauTrack.etaSq]
  · rw [← TauTrack.ElevenFive.sigmaStar_eq_sum]
    exact TauTrack.ElevenFive.newform11_modEq_sigmaStar hn

end ElevenFive
