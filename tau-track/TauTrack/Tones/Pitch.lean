module

public import TauTrack.Tones.EtaCharacter
import Mathlib.Tactic

/-!
# The pitch of an element of the modular group, and the twelve-tone dictionary

`etaChar γ` (the multiplier of `η²`) is a 12th root of unity, `ζ₁₂^{pitch γ}` with `ζ₁₂ = e^{2πi/12}`;
`pitch : SL(2, ℤ) → ℤ/12` is additive (`pitch_mul`), with

* `pitch T = 1` (semitone), `pitch S = 9` (a minor third down), `pitch (S T) = 10` (a whole tone
  down), `pitch (−1) = 6` (the tritone);
* the powers of `S` (the stabiliser of the Gaussian point `i`) have pitches `{0, 3, 6, 9}`, the
  diminished seventh; the powers of `S T` (the stabiliser of the Eisenstein point `ρ`) have pitches
  `{0, 2, 4, 6, 8, 10}`, the whole-tone scale; the powers of `(S T)²` the augmented triad `{0, 4, 8}`.

The finite statements about `ℤ/12`:
* `(ℤ/12)^×`, the intervals that generate the circle (`1, 5, 7, 11`), is the Klein four-group;
* multiplication by `7` is the circle of fifths;
* the diatonic scale is seven consecutive fifths and is maximally even.

The Galois reading, `(ℤ/12)^× = Gal(ℚ(ζ₁₂)/ℚ)`, `σ₇` fixing `ℚ(√−3)` and `σ₅` fixing `ℚ(i)`: the
arithmetic is `units_fix_three` and `units_fix_four` (`ζ₁₂^{3a} = ζ₁₂³` iff `a ≡ 1 (mod 4)`,
`ζ₁₂^{4a} = ζ₁₂⁴` iff `a ≡ 1 (mod 3)`).

Exposition: https://github.com/rmorleysmith/l-functions-and-physics (note 1, twelve tones).
-/

@[expose] public section

open Complex ModularGroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TauTrack.Tones

/-! ## The pitch map -/

theorem etaChar_pow_twelve (γ : SL(2, ℤ)) : etaChar γ ^ 12 = 1 := by
  have h : etaCharUnits ^ 12 = 1 := by
    apply char_ext
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_etaCharUnits, MonoidHom.one_apply,
      Units.val_one]
    exact isPrimitiveRoot_etaChar_T.pow_eq_one
  have := congrArg (fun χ : SL(2, ℤ) →* ℂˣ ↦ ((χ γ : ℂˣ) : ℂ)) h
  simpa [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, coe_etaCharUnits] using this

theorem exists_pitch (γ : SL(2, ℤ)) : ∃ k < 12, etaChar T ^ k = etaChar γ :=
  isPrimitiveRoot_etaChar_T.eq_pow_of_pow_eq_one (etaChar_pow_twelve γ)

/-- **The pitch of `γ`**: `etaChar γ = ζ₁₂^{pitch γ}`. -/
noncomputable def pitch (γ : SL(2, ℤ)) : ZMod 12 := ((exists_pitch γ).choose : ℕ)

theorem etaChar_eq_pow_pitch (γ : SL(2, ℤ)) : etaChar γ = etaChar T ^ (pitch γ).val := by
  rw [pitch, ZMod.val_natCast, Nat.mod_eq_of_lt (exists_pitch γ).choose_spec.1]
  exact (exists_pitch γ).choose_spec.2.symm

/-- The pitch is determined by the character value. -/
theorem pitch_eq_of {γ : SL(2, ℤ)} {k : ℕ} (h : etaChar γ = etaChar T ^ k) : pitch γ = k := by
  have hk : etaChar T ^ k = etaChar T ^ (k % 12) := by
    conv_lhs => rw [← Nat.mod_add_div k 12, pow_add, pow_mul,
      isPrimitiveRoot_etaChar_T.pow_eq_one, one_pow, mul_one]
  have h2 := (etaChar_eq_pow_pitch γ).symm.trans (h.trans hk)
  have h3 := isPrimitiveRoot_etaChar_T.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (by norm_num)) h2
  apply ZMod.val_injective
  rw [h3, ZMod.val_natCast]

/-- **The pitch is additive.** -/
theorem pitch_mul (γ δ : SL(2, ℤ)) : pitch (γ * δ) = pitch γ + pitch δ := by
  have h : etaChar (γ * δ) = etaChar T ^ ((pitch γ).val + (pitch δ).val) := by
    rw [map_mul, etaChar_eq_pow_pitch γ, etaChar_eq_pow_pitch δ, pow_add]
  rw [pitch_eq_of h]
  push_cast
  simp

theorem pitch_one : pitch 1 = 0 := by
  have := pitch_mul 1 1
  rw [mul_one] at this
  linear_combination -this

/-- `T` is a semitone. -/
theorem pitch_T : pitch T = 1 := by
  have := pitch_eq_of (γ := T) (k := 1) (pow_one _).symm
  simpa using this

/-- `S` is a minor third down: `9 ≡ −3`. -/
theorem pitch_S : pitch S = 9 := by
  have := pitch_eq_of etaChar_S_eq_pow
  simpa using this

/-- `S T` is a whole tone down: `10 ≡ −2`. -/
theorem pitch_ST : pitch (S * T) = 10 := by
  rw [pitch_mul, pitch_S, pitch_T]
  rfl

/-- `−1 = S²` is the tritone. -/
theorem pitch_neg_one : pitch (-1) = 6 := by
  rw [← S_mul_S, pitch_mul, pitch_S]
  rfl

theorem pitch_pow (γ : SL(2, ℤ)) (n : ℕ) : pitch (γ ^ n) = n * pitch γ := by
  induction n with
  | zero => simp [pitch_one]
  | succ n ih => rw [pow_succ, pitch_mul, ih]; push_cast; ring

/-- **The Gaussian point**: the powers of `S` (its stabiliser) sound the diminished seventh. -/
theorem pitches_S : (Finset.range 4).image (fun n ↦ pitch (S ^ n)) = {0, 3, 6, 9} := by
  simp only [pitch_pow, pitch_S]
  decide

/-- **The Eisenstein point**: the powers of `S T` (its stabiliser) sound the whole-tone scale. -/
theorem pitches_ST : (Finset.range 6).image (fun n ↦ pitch ((S * T) ^ n)) = {0, 2, 4, 6, 8, 10} := by
  simp only [pitch_pow, pitch_ST]
  decide

/-- The powers of `(S T)²` sound the augmented triad. -/
theorem pitches_ST_sq :
    (Finset.range 3).image (fun n ↦ pitch (((S * T) ^ 2) ^ n)) = {0, 4, 8} := by
  simp only [pitch_pow, pitch_ST]
  decide

/-! ## The finite dictionary in `ℤ/12` -/

/-- **The interval generators form the Klein four-group**: every unit of `ℤ/12` squares to `1`. -/
theorem units_sq_eq_one : ∀ u : (ZMod 12)ˣ, u ^ 2 = 1 := by decide

theorem card_units : Fintype.card (ZMod 12)ˣ = 4 := by decide

/-- The units are the intervals `1, 5, 7, 11` (semitone, fourth, fifth, major seventh). -/
theorem isUnit_iff : ∀ a : ZMod 12, IsUnit a ↔ a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 11 := by decide

/-- **The circle of fifths** visits every pitch class. -/
theorem fifths_surjective : ∀ x : ZMod 12, ∃ k : ZMod 12, 7 * k = x := by decide

/-- The diatonic scale. -/
def diatonic : Finset (ZMod 12) := {0, 2, 4, 5, 7, 9, 11}

/-- **The diatonic scale is seven consecutive fifths** (F, C, G, D, A, E, B). -/
theorem diatonic_eq_fifths :
    diatonic = (Finset.range 7).image (fun k : ℕ ↦ 7 * ((k : ZMod 12) - 1)) := by decide

/-- **The diatonic scale is maximally even**: a translate of `⌊12k/7⌋`, `k < 7`. -/
theorem diatonic_maximally_even :
    diatonic = (Finset.range 7).image (fun k : ℕ ↦ (((12 * k) / 7 : ℕ) : ZMod 12) + 11) := by
  decide

/-- `σ_a : ζ₁₂ ↦ ζ₁₂^a` fixes `i = ζ₁₂³` iff `a ≡ 1 (mod 4)`: among the units, `a = 1, 5`. -/
theorem units_fix_three : ∀ a : ZMod 12, IsUnit a → (3 * a = 3 ↔ a = 1 ∨ a = 5) := by decide

/-- `σ_a` fixes `ζ₃ = ζ₁₂⁴` (so `√−3`) iff `a ≡ 1 (mod 3)`: among the units, `a = 1, 7`. -/
theorem units_fix_four : ∀ a : ZMod 12, IsUnit a → (4 * a = 4 ↔ a = 1 ∨ a = 7) := by decide

end TauTrack.Tones
