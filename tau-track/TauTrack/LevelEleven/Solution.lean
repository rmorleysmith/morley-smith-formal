module

public import Mathlib
public import TauTrack.LevelEleven.Basic

/-!
# Solution: the newform of weight 2 and level 11

The statement of `Challenge.lean`, proved from `TauTrack.LevelEleven.Basic`.
-/

@[expose] public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace LevelEleven

theorem exists_newform :
    ∃ (f : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2) (a : ℕ → ℤ),
      (∀ z : ℍ, f z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n = (a n : ℂ)) ∧
      a 1 = 1 ∧ a 2 = -2 ∧
      (∀ g : CuspForm ((Gamma0 11).map (mapGL ℝ)) 2, g = (qExpansion 1 g).coeff 1 • f) ∧
      (∀ g : ModularForm ((Gamma0 11).map (mapGL ℝ)) 2,
        (∀ i ≤ 2, (qExpansion 1 g).coeff i = (a i : ℂ)) → ∀ z : ℍ, g z = f z) ∧
      (∀ m n : ℕ, n ≠ 0 → a m * a n = ∑ d ∈ (m.gcd n).divisors,
        (if 11 ∣ d then 0 else (d : ℤ)) * a (m * n / d ^ 2)) ∧
      (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧
      (∀ p r : ℕ, p.Prime → p ≠ 11 →
        a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℤ) * a (p ^ r)) ∧
      ∀ r : ℕ, a (11 ^ (r + 1)) = a 11 * a (11 ^ r) := by
  refine ⟨TauTrack.eta11Form, TauTrack.newform11, fun z ↦ ?_, TauTrack.newform11_spec,
    TauTrack.newform11_one, TauTrack.newform11_two, TauTrack.cuspForm_eq_coeff_one_smul,
    fun g hg z ↦ ?_, fun m n hn ↦ TauTrack.newform11_mul m hn,
    fun m n h ↦ TauTrack.newform11_mul_coprime h,
    fun p r hp hp11 ↦ TauTrack.newform11_prime_pow hp hp11 r, TauTrack.newform11_eleven_pow⟩
  · change TauTrack.eta11 z = _
    simp [TauTrack.eta11, TauTrack.etaSq]
  · have := TauTrack.eq_eta11Form_of_coeff g fun i hi ↦ by
      rw [hg i hi, TauTrack.newform11_spec]
    rw [this]
    rfl

end LevelEleven
