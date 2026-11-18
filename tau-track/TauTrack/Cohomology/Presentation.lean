module

public import TauCeti.NumberTheory.Modular.Relations
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import Mathlib.Tactic

/-!
# `PSL(2, ℤ)` is the free product of cyclic groups of orders `2` and `3`

The classes of `S = (0 -1; 1 0)` and `U = T S = (1 -1; 1 0)` in `PSL(2, ℤ)` satisfy `S² = 1` and
`U³ = 1` (TauCeti's `coe_S_sq`, `coe_T_mul_coe_S_pow_three`) and generate the group. Here we show
that these are the only relations: `PSL(2, ℤ) = ⟨S, U | S², U³⟩ ≅ C₂ * C₃`.

## Proof

Ping-pong (`Monoid.CoprodI.lift_injective_of_ping_pong`). `PSL(2, ℤ)` acts on integer `2 × 2`
matrices by `M ↦ g M gᵀ`; this is well defined on the quotient because `-1` acts trivially. On a
symmetric matrix `(a b; b c)` the generators act by

* `S : (a, b, c) ↦ (c, -b, a)`,
* `U : (a, b, c) ↦ (a - 2b + c, a - b, a)`,
* `U² : (a, b, c) ↦ (c, c - b, a - 2b + c)`.

So with `X₀ = {a, c ≥ 0, b < 0}` and `X₁ = {a, c ≥ 0, b > 0}` we get `S X₁ ⊆ X₀` and
`U X₀, U² X₀ ⊆ X₁`. (For `M = v vᵀ`, `v = (x, y)`, the entry `b` is `x y`: this is the usual
ping-pong on the sign of `x y`.) Hence the map `C₂ * C₃ → PSL(2, ℤ)` is injective; it is
surjective by TauCeti's `closure_coe_S_coe_T_mul_coe_S`.

## Main results

* `TauTrack.Cohomology.coprodEquiv`: the isomorphism `C₂ * C₃ ≃* PSL(2, ℤ)`.
* `TauTrack.Cohomology.exists_hom_of_relations`: for `s, u` in a group with `s² = 1`, `u³ = 1`
  there is a homomorphism `PSL(2, ℤ) →* G` with `S ↦ s`, `U ↦ u`.
* `TauTrack.Cohomology.hom_ext_S_U`: such a homomorphism is unique.
-/

@[expose] public section

open Matrix ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

/-! ### Cyclic factors -/

/-- The homomorphism from the cyclic group of order `n` sending the generator to `g`, for
`g ^ n = 1`. -/
def cyclicHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift n ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      simpa using congrArg Additive.ofMul hg⟩)

theorem cyclicHom_ofAdd_intCast {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) (k : ℤ) :
    cyclicHom n g hg (Multiplicative.ofAdd (k : ZMod n)) = g ^ k := by
  simp [cyclicHom]

theorem cyclicHom_ofAdd_one {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    cyclicHom n g hg (Multiplicative.ofAdd 1) = g := by
  simpa using cyclicHom_ofAdd_intCast n g hg 1

theorem cyclicHom_apply {G : Type*} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1)
    (h : Multiplicative (ZMod n)) :
    cyclicHom n g hg h = g ^ (ZMod.val (Multiplicative.toAdd h)) := by
  have := cyclicHom_ofAdd_intCast n g hg ((ZMod.val (Multiplicative.toAdd h) : ℕ) : ℤ)
  rwa [zpow_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd] at this

theorem exists_cyclicHom_eq_pow {G : Type*} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1)
    (h : Multiplicative (ZMod n)) (hh : h ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ cyclicHom n g hg h = g ^ k := by
  refine ⟨ZMod.val (Multiplicative.toAdd h), Nat.pos_of_ne_zero fun h0 => hh ?_, ZMod.val_lt _,
    cyclicHom_apply n g hg h⟩
  rw [ZMod.val_eq_zero] at h0
  exact Multiplicative.toAdd.injective h0

/-- The two factors: cyclic of order `2` (index `0`) and of order `3` (index `1`). -/
abbrev Factor (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))

/-- The pair `(s, u)` as a family indexed by `Fin 2`. -/
def gen {G : Type*} (s u : G) : Fin 2 → G := ![s, u]

theorem gen_pow {G : Type*} [Group G] (s u : G) (hs : s * s = 1) (hu : u * u * u = 1)
    (i : Fin 2) : gen s u i ^ (i.val + 2) = 1 := by
  fin_cases i
  · simpa [gen, pow_two] using hs
  · simpa [gen, pow_succ] using hu

/-- The homomorphisms from the two cyclic factors sending the generators to `s` and `u`. -/
def factorHom {G : Type*} [Group G] (s u : G) (hs : s * s = 1) (hu : u * u * u = 1)
    (i : Fin 2) : Factor i →* G :=
  cyclicHom (i.val + 2) (gen s u i) (gen_pow s u hs hu i)

theorem factorHom_zero {G : Type*} [Group G] (s u : G) (hs : s * s = 1) (hu : u * u * u = 1) :
    factorHom s u hs hu 0 (Multiplicative.ofAdd 1) = s :=
  cyclicHom_ofAdd_one _ (gen s u 0) (gen_pow s u hs hu 0)

theorem factorHom_one {G : Type*} [Group G] (s u : G) (hs : s * s = 1) (hu : u * u * u = 1) :
    factorHom s u hs hu 1 (Multiplicative.ofAdd 1) = u :=
  cyclicHom_ofAdd_one _ (gen s u 1) (gen_pow s u hs hu 1)

/-- A nontrivial element of the factor of order `2` maps to `s`. -/
theorem factorHom_zero_of_ne_one {G : Type*} [Group G] (s u : G) (hs : s * s = 1)
    (hu : u * u * u = 1) (h : Factor 0) (hh : h ≠ 1) : factorHom s u hs hu 0 h = s := by
  obtain ⟨k, hk0, hk, hk'⟩ :=
    exists_cyclicHom_eq_pow _ (gen s u 0) (gen_pow s u hs hu 0) h hh
  have hk2 : k < 2 := hk
  interval_cases k
  exact hk'.trans (pow_one _)

/-- A nontrivial element of the factor of order `3` maps to `u` or `u ^ 2`. -/
theorem factorHom_one_of_ne_one {G : Type*} [Group G] (s u : G) (hs : s * s = 1)
    (hu : u * u * u = 1) (h : Factor 1) (hh : h ≠ 1) :
    factorHom s u hs hu 1 h = u ∨ factorHom s u hs hu 1 h = u ^ 2 := by
  obtain ⟨k, hk0, hk, hk'⟩ :=
    exists_cyclicHom_eq_pow _ (gen s u 1) (gen_pow s u hs hu 1) h hh
  have hk3 : k < 3 := hk
  interval_cases k
  · exact Or.inl (hk'.trans (pow_one _))
  · exact Or.inr hk'

/-! ### The action of `PSL(2, ℤ)` on integer `2 × 2` matrices by `M ↦ g M gᵀ` -/

/-- `SL(2, ℤ)` acting on integer matrices by `M ↦ g M gᵀ`, as a homomorphism to permutations. -/
def congrPerm : SL(2, ℤ) →* Equiv.Perm (Matrix (Fin 2) (Fin 2) ℤ) :=
  MonoidHom.toHomPerm
    { toFun := fun g M => (g : Matrix (Fin 2) (Fin 2) ℤ) * M * (g : Matrix (Fin 2) (Fin 2) ℤ)ᵀ
      map_one' := by
        funext M
        change _ = M
        simp
      map_mul' := fun g h => by
        funext M
        change _ = (g : Matrix (Fin 2) (Fin 2) ℤ) *
          ((h : Matrix (Fin 2) (Fin 2) ℤ) * M * (h : Matrix (Fin 2) (Fin 2) ℤ)ᵀ) *
            (g : Matrix (Fin 2) (Fin 2) ℤ)ᵀ
        simp [Matrix.transpose_mul, Matrix.mul_assoc] }

theorem congrPerm_apply (g : SL(2, ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    congrPerm g M = (g : Matrix (Fin 2) (Fin 2) ℤ) * M * (g : Matrix (Fin 2) (Fin 2) ℤ)ᵀ :=
  rfl

theorem center_le_ker_congrPerm : Subgroup.center SL(2, ℤ) ≤ congrPerm.ker := by
  intro z hz
  rw [SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hz
  rw [MonoidHom.mem_ker]
  ext M : 1
  rcases hz with rfl | rfl <;> simp [congrPerm_apply]

/-- The action descends to `PSL(2, ℤ)`. -/
def pslPerm : PSL(2, ℤ) →* Equiv.Perm (Matrix (Fin 2) (Fin 2) ℤ) :=
  QuotientGroup.lift _ congrPerm center_le_ker_congrPerm

theorem pslPerm_coe (g : SL(2, ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    pslPerm (g : PSL(2, ℤ)) M =
      (g : Matrix (Fin 2) (Fin 2) ℤ) * M * (g : Matrix (Fin 2) (Fin 2) ℤ)ᵀ :=
  rfl

/-- `PSL(2, ℤ)` acts on integer `2 × 2` matrices by `M ↦ g M gᵀ`. Not an instance. -/
@[reducible] def pslAction : MulAction PSL(2, ℤ) (Matrix (Fin 2) (Fin 2) ℤ) :=
  MulAction.compHom _ pslPerm

/-! ### Ping-pong -/

/-- The ping-pong sets: symmetric matrices `(a b; b c)` with `a, c ≥ 0` and `b < 0` (index `0`)
or `b > 0` (index `1`). For `M = v vᵀ` with `v = (x, y)` this is the sign of `x y`. -/
def pingSet (i : Fin 2) : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
  {M | M 1 0 = M 0 1 ∧ 0 ≤ M 0 0 ∧ 0 ≤ M 1 1 ∧ if i = 0 then M 0 1 < 0 else 0 < M 0 1}

theorem pslPerm_S_mem {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ pingSet 1) :
    pslPerm (S : PSL(2, ℤ)) M ∈ pingSet 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  rw [pslPerm_coe]
  simp only [pingSet, Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] at h4 ⊢
  simp at h4 ⊢
  omega

theorem pslPerm_U_mem {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ pingSet 0) :
    pslPerm ((T : PSL(2, ℤ)) * S) M ∈ pingSet 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  rw [← QuotientGroup.mk_mul, pslPerm_coe]
  simp only [pingSet, Set.mem_ofPred_eq, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.transpose_apply] at h4 ⊢
  simp at h4 ⊢
  omega

theorem pslPerm_U_sq_mem {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ pingSet 0) :
    pslPerm (((T : PSL(2, ℤ)) * S) ^ 2) M ∈ pingSet 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, pslPerm_coe]
  simp only [pingSet, Set.mem_ofPred_eq, pow_two, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.transpose_apply] at h4 ⊢
  simp at h4 ⊢
  omega

theorem coe_S_mul_coe_S : (S : PSL(2, ℤ)) * S = 1 := by
  rw [← pow_two, TauCeti.ModularGroup.coe_S_sq]

theorem coe_U_mul_coe_U_mul_coe_U :
    ((T : PSL(2, ℤ)) * S) * ((T : PSL(2, ℤ)) * S) * ((T : PSL(2, ℤ)) * S) = 1 := by
  rw [← pow_two, ← pow_succ, TauCeti.ModularGroup.coe_T_mul_coe_S_pow_three]

/-- The homomorphisms from the cyclic groups of orders `2` and `3` to `PSL(2, ℤ)` sending the
generators to `S` and `U = T S`. -/
def modularFactorHom (i : Fin 2) : Factor i →* PSL(2, ℤ) :=
  factorHom (S : PSL(2, ℤ)) ((T : PSL(2, ℤ)) * S) coe_S_mul_coe_S coe_U_mul_coe_U_mul_coe_U i

open Cardinal in
/-- Ping-pong: the free product of the cyclic groups of orders `2` and `3` embeds in
`PSL(2, ℤ)`. -/
theorem lift_modularFactorHom_injective :
    Function.Injective (Monoid.CoprodI.lift modularFactorHom) := by
  let _ := pslAction
  have hsmul : ∀ (g : PSL(2, ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ), g • M = pslPerm g M :=
    fun _ _ => rfl
  refine Monoid.CoprodI.lift_injective_of_ping_pong modularFactorHom (Or.inr ⟨1, ?_⟩) pingSet
    ?_ ?_ ?_
  · change 3 ≤ #(Multiplicative (ZMod 3))
    rw [Cardinal.mk_fintype]
    simp
  · intro i
    fin_cases i
    · exact ⟨!![1, -1; -1, 1], by simp [pingSet]⟩
    · exact ⟨!![1, 1; 1, 1], by simp [pingSet]⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro M ⟨-, -, -, hi⟩ ⟨-, -, -, hj⟩
    fin_cases i <;> fin_cases j <;> simp at hij hi hj <;> omega
  · intro i j hij h hh
    rw [Set.smul_set_subset_iff]
    intro M hM
    rw [hsmul]
    fin_cases i <;> fin_cases j
    · simp at hij
    · have h0 : modularFactorHom 0 h = (S : PSL(2, ℤ)) :=
        factorHom_zero_of_ne_one _ _ _ _ h hh
      have key := pslPerm_S_mem hM
      rw [← h0] at key
      exact key
    · rcases factorHom_one_of_ne_one (S : PSL(2, ℤ)) ((T : PSL(2, ℤ)) * S) coe_S_mul_coe_S
        coe_U_mul_coe_U_mul_coe_U h hh with h1 | h1
      · have key := pslPerm_U_mem hM
        rw [← h1] at key
        exact key
      · have key := pslPerm_U_sq_mem hM
        rw [← h1] at key
        exact key
    · simp at hij

/-- `S` and `U` generate, so the map from the free product is onto. -/
theorem lift_modularFactorHom_surjective :
    Function.Surjective (Monoid.CoprodI.lift modularFactorHom) := by
  rw [← MonoidHom.range_eq_top, ← top_le_iff, ← TauCeti.ModularGroup.closure_coe_S_coe_T_mul_coe_S,
    Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact ⟨Monoid.CoprodI.of (i := (0 : Fin 2)) (Multiplicative.ofAdd 1), by
      rw [Monoid.CoprodI.lift_of]
      exact factorHom_zero _ _ _ _⟩
  · exact ⟨Monoid.CoprodI.of (i := (1 : Fin 2)) (Multiplicative.ofAdd 1), by
      rw [Monoid.CoprodI.lift_of]
      exact factorHom_one _ _ _ _⟩

theorem lift_modularFactorHom_bijective :
    Function.Bijective (Monoid.CoprodI.lift modularFactorHom) :=
  ⟨lift_modularFactorHom_injective, lift_modularFactorHom_surjective⟩

/-- `PSL(2, ℤ)` is the free product of a cyclic group of order `2` (generated by `S`) and a cyclic
group of order `3` (generated by `U = T S`). -/
noncomputable def coprodEquiv : Monoid.CoprodI Factor ≃* PSL(2, ℤ) :=
  MulEquiv.ofBijective (Monoid.CoprodI.lift modularFactorHom) lift_modularFactorHom_bijective

theorem coprodEquiv_of_zero :
    coprodEquiv (Monoid.CoprodI.of (i := (0 : Fin 2)) (Multiplicative.ofAdd 1)) =
      (S : PSL(2, ℤ)) := by
  rw [coprodEquiv, MulEquiv.ofBijective_apply, Monoid.CoprodI.lift_of]
  exact factorHom_zero _ _ _ _

theorem coprodEquiv_of_one :
    coprodEquiv (Monoid.CoprodI.of (i := (1 : Fin 2)) (Multiplicative.ofAdd 1)) =
      (T : PSL(2, ℤ)) * S := by
  rw [coprodEquiv, MulEquiv.ofBijective_apply, Monoid.CoprodI.lift_of]
  exact factorHom_one _ _ _ _

/-- `PSL(2, ℤ)` is generated by `S` and `U = T S` subject only to `S² = 1`, `U³ = 1`. -/
theorem exists_hom_of_relations {G : Type*} [Group G] (s u : G) (hs : s * s = 1)
    (hu : u * u * u = 1) :
    ∃ φ : PSL(2, ℤ) →* G, φ (S : PSL(2, ℤ)) = s ∧ φ ((T : PSL(2, ℤ)) * S) = u := by
  refine ⟨(Monoid.CoprodI.lift (factorHom s u hs hu)).comp coprodEquiv.symm.toMonoidHom, ?_, ?_⟩
  · rw [← coprodEquiv_of_zero]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Monoid.CoprodI.lift_of]
    exact factorHom_zero s u hs hu
  · rw [← coprodEquiv_of_one]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Monoid.CoprodI.lift_of]
    exact factorHom_one s u hs hu

/-- A homomorphism out of `PSL(2, ℤ)` is determined by its values at `S` and `U = T S`. -/
theorem hom_ext_S_U {G : Type*} [Group G] {φ ψ : PSL(2, ℤ) →* G}
    (hS : φ (S : PSL(2, ℤ)) = ψ (S : PSL(2, ℤ)))
    (hU : φ ((T : PSL(2, ℤ)) * S) = ψ ((T : PSL(2, ℤ)) * S)) : φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense TauCeti.ModularGroup.closure_coe_S_coe_T_mul_coe_S ?_
  rintro g (rfl | rfl)
  · exact hS
  · exact hU

end TauTrack.Cohomology

