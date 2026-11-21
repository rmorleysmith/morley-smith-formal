module

public import Mathlib

/-!
# The energies of the square frame

For `ad - bc = 1`: `(a - d)² + (b + c)² + 4 = (a + d)² + (b - c)²`, so `n = (a - d)² + (b + c)²`
forces `n` and `n + 4` to be sums of two squares. Conversely, from `n = p² + q²` and
`n + 4 = r² + s²` with `r ≡ p` and `s ≡ q (mod 2)` the matrix `a = (r + p)/2`, `d = (r - p)/2`,
`b = (q + s)/2`, `c = (q - s)/2` has determinant `(r² + s² - p² - q²)/4 = 1`. The parities can be
matched, after swapping `r` and `s` if needed, because `x² ≡ x (mod 2)` and `x² mod 4` is `x mod 2`,
so `p, q` and `r, s` contain the same number of odd entries.
-/

@[expose] public section

namespace MorleySmithFormal.SquareFrameEnergies

theorem identities (a b c d : ℤ) (h : a * d - b * c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 = (a - d) ^ 2 + (b + c) ^ 2 ∧
      (a - d) ^ 2 + (b + c) ^ 2 + 4 = (a + d) ^ 2 + (b - c) ^ 2 :=
  ⟨by linear_combination (2 : ℤ) * h, by linear_combination (-4 : ℤ) * h⟩

/-- A square is congruent modulo `4` to its residue modulo `2`. -/
theorem sq_emod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · have e : (2 * k) ^ 2 = 0 + 4 * k ^ 2 := by ring
    rw [e, Int.add_mul_emod_self_left]
    omega
  · have e : (2 * k + 1) ^ 2 = 1 + 4 * (k ^ 2 + k) := by ring
    rw [e, Int.add_mul_emod_self_left]
    omega

/-- The matrix built from matched parities. -/
theorem construct (p q r s : ℤ) (h : r ^ 2 + s ^ 2 = p ^ 2 + q ^ 2 + 4)
    (hp : Even (r + p)) (hq : Even (s + q)) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a - d) ^ 2 + (b + c) ^ 2 = p ^ 2 + q ^ 2 := by
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  have hr : r = 2 * x - p := by linarith
  have hs : s = 2 * y - q := by linarith
  subst hr hs
  refine ⟨x, y, y - (2 * y - q), x - p, ?_, by ring⟩
  have h4 : 4 * (x * (x - p) - y * (y - (2 * y - q))) = 4 * 1 := by linear_combination h
  exact mul_left_cancel₀ (by norm_num) h4

/-- From `p² + q² + 4 = r² + s²` the parities of `p, q` match those of `r, s` or of `s, r`. -/
theorem parity_match (p q r s : ℤ) (h : r ^ 2 + s ^ 2 = p ^ 2 + q ^ 2 + 4) :
    (Even (r + p) ∧ Even (s + q)) ∨ (Even (s + p) ∧ Even (r + q)) := by
  have e1 := sq_emod_four p
  have e2 := sq_emod_four q
  have e3 := sq_emod_four r
  have e4 := sq_emod_four s
  simp only [Int.even_iff]
  generalize p ^ 2 = P at *
  generalize q ^ 2 = Q at *
  generalize r ^ 2 = R at *
  generalize s ^ 2 = S at *
  rcases Int.emod_two_eq_zero_or_one p with hp | hp <;>
  rcases Int.emod_two_eq_zero_or_one q with hq | hq <;>
  rcases Int.emod_two_eq_zero_or_one r with hr | hr <;>
  rcases Int.emod_two_eq_zero_or_one s with hs | hs <;>
  omega

theorem exists_iff (n : ℤ) :
    (∃ a b c d : ℤ, a * d - b * c = 1 ∧ (a - d) ^ 2 + (b + c) ^ 2 = n) ↔
      (∃ p q : ℤ, p ^ 2 + q ^ 2 = n) ∧ (∃ r s : ℤ, r ^ 2 + s ^ 2 = n + 4) := by
  constructor
  · rintro ⟨a, b, c, d, h, rfl⟩
    exact ⟨⟨a - d, b + c, rfl⟩, ⟨a + d, b - c, ((identities a b c d h).2).symm⟩⟩
  · rintro ⟨⟨p, q, rfl⟩, ⟨r, s, hrs⟩⟩
    rcases parity_match p q r s hrs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact construct p q r s hrs h1 h2
    · exact construct p q s r (by linarith) h1 h2

end MorleySmithFormal.SquareFrameEnergies
