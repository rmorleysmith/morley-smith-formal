module

public import TauTrack.Siegel.Form
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.GradedMonoid

/-!
# The graded ring of Siegel modular forms

For a fixed degree `n`, the Siegel modular forms of weight `k` form a complex vector space
`M_k`, and the product of forms of weights `k` and `l` has weight `k + l`. So

  `M_* = ⨁_k M_k`

is a commutative graded `ℂ`-algebra. This is the degree-`n` version of Mathlib's
`DirectSum.GCommRing (ModularForm Γ)`.

* `SiegelModularForm.instAddCommGroup`, `instModule`: each `M_k` is a complex vector space.
* `SiegelModularForm.instGCommRing`, `instGAlgebra`: the graded commutative `ℂ`-algebra.
* `SiegelModularForm.evalAlgHom`: evaluation `M_* → (ℍ_n → ℂ)`, an algebra homomorphism.
* `SiegelModularForm.pow`: the `m`-th power of a form of weight `k`, of weight `m * k`.
-/

@[expose] public noncomputable section

open Matrix Complex
open scoped DirectSum

namespace TauTrack.Siegel

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace SiegelModularForm

variable {k l : ℤ}

/-! ## Each weight is a complex vector space -/

@[simp] theorem coe_zero : ⇑(0 : SiegelModularForm n k) = 0 := rfl

@[simp] theorem coe_add (F G : SiegelModularForm n k) : ⇑(F + G) = ⇑F + ⇑G := rfl

@[simp] theorem coe_smul (c : ℂ) (F : SiegelModularForm n k) : ⇑(c • F) = c • ⇑F := rfl

@[simp] theorem coe_mul (F : SiegelModularForm n k) (G : SiegelModularForm n l) :
    ⇑(F.mul G) = ⇑F * ⇑G := rfl

@[simp] theorem coe_const (c : ℂ) : ⇑(const n c) = fun _ => c := rfl

instance : Neg (SiegelModularForm n k) where
  neg F := (-1 : ℂ) • F

instance : Sub (SiegelModularForm n k) where
  sub F G := F + -G

instance instSMulNat : SMul ℕ (SiegelModularForm n k) where
  smul m F := (m : ℂ) • F

instance instSMulInt : SMul ℤ (SiegelModularForm n k) where
  smul m F := (m : ℂ) • F

@[simp] theorem coe_neg (F : SiegelModularForm n k) : ⇑(-F) = -⇑F := by
  funext Z
  change (-1 : ℂ) • F Z = -F Z
  simp

@[simp] theorem coe_sub (F G : SiegelModularForm n k) : ⇑(F - G) = ⇑F - ⇑G := by
  funext Z
  change F Z + (-G) Z = F Z - G Z
  rw [coe_neg, Pi.neg_apply, sub_eq_add_neg]

theorem coe_nsmul (m : ℕ) (F : SiegelModularForm n k) : ⇑(m • F) = m • ⇑F := by
  funext Z
  change (m : ℂ) • F Z = m • F Z
  simp [nsmul_eq_mul]

theorem coe_zsmul (m : ℤ) (F : SiegelModularForm n k) : ⇑(m • F) = m • ⇑F := by
  funext Z
  change (m : ℂ) • F Z = m • F Z
  simp [zsmul_eq_mul]

instance instAddCommGroup : AddCommGroup (SiegelModularForm n k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub
    (fun F m => coe_nsmul m F) (fun F m => coe_zsmul m F)

/-- The inclusion of `M_k` into the functions on `ℍ_n`, as an additive map. -/
def coeHom : SiegelModularForm n k →+ (SiegelUpperHalfSpace n → ℂ) where
  toFun F := F
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℂ (SiegelModularForm n k) :=
  Function.Injective.module ℂ coeHom DFunLike.coe_injective fun _ _ => rfl

/-! ## The graded ring -/

instance : One (SiegelModularForm n 0) where
  one := const n 1

@[simp] theorem coe_one : ⇑(1 : SiegelModularForm n 0) = 1 := rfl

instance : NatCast (SiegelModularForm n 0) where
  natCast m := const n m

instance : IntCast (SiegelModularForm n 0) where
  intCast m := const n m

/-- Transport a form along an equality of weights. -/
def mcast {a b : ℤ} (h : a = b) (F : SiegelModularForm n a) : SiegelModularForm n b where
  toFun := F
  holo := F.holo
  slash_eq := h ▸ F.slash_eq
  bdd := F.bdd

@[simp] theorem mcast_apply {a b : ℤ} (h : a = b) (F : SiegelModularForm n a)
    (Z : SiegelUpperHalfSpace n) : mcast h F Z = F Z := rfl

theorem gradedMonoid_eq_of_cast {a b : GradedMonoid (SiegelModularForm n)}
    (h : a.fst = b.fst) (h2 : mcast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

instance : GradedMonoid.GOne (SiegelModularForm n) where
  one := 1

instance : GradedMonoid.GMul (SiegelModularForm n) where
  mul F G := F.mul G

/-- Siegel modular forms of degree `n`, graded by weight, form a commutative graded ring. -/
instance instGCommRing : DirectSum.GCommRing (SiegelModularForm n) where
  one_mul _ := gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  mul_zero {_ _} _ := ext fun _ => mul_zero _
  zero_mul {_ _} _ := ext fun _ => zero_mul _
  mul_add {_ _} _ _ _ := ext fun _ => mul_add _ _ _
  add_mul {_ _} _ _ _ := ext fun _ => add_mul _ _ _
  mul_comm _ _ := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  natCast := Nat.cast
  natCast_zero := ext fun _ => Nat.cast_zero
  natCast_succ _ := ext fun _ => Nat.cast_succ _
  intCast := Int.cast
  intCast_ofNat _ := ext fun _ => AddGroupWithOne.intCast_ofNat _
  intCast_negSucc_ofNat m := ext fun Z => by
    change ((Int.negSucc m : ℤ) : ℂ) = (-(const n ((m + 1 : ℕ) : ℂ))) Z
    rw [coe_neg]
    exact Int.cast_negSucc m

/-- The graded ring of Siegel modular forms is a graded `ℂ`-algebra; the constants sit in
weight `0`. -/
instance instGAlgebra : DirectSum.GAlgebra ℂ (SiegelModularForm n) where
  toFun := { toFun := fun z => const n z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def c x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun Z => by
    change c • x.snd Z = c * x.snd Z
    exact smul_eq_mul c (x.snd Z))

/-- `M_* = ⨁_k M_k` is a commutative ring. -/
example : CommRing (⨁ k, SiegelModularForm n k) := inferInstance

/-- `M_* = ⨁_k M_k` is a `ℂ`-algebra. -/
example : Algebra ℂ (⨁ k, SiegelModularForm n k) := inferInstance

/-- The inclusion of `M_k` into the functions on `ℍ_n`, as a linear map. -/
def coeLinearMap (k : ℤ) : SiegelModularForm n k →ₗ[ℂ] (SiegelUpperHalfSpace n → ℂ) where
  toFun F := F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of the graded ring on `ℍ_n`: a sum of forms of different weights is sent to the
sum of the underlying functions. It is a homomorphism of `ℂ`-algebras. -/
def evalAlgHom :
    (⨁ k, SiegelModularForm n k) →ₐ[ℂ] (SiegelUpperHalfSpace n → ℂ) :=
  DirectSum.toAlgebra ℂ (SiegelModularForm n) coeLinearMap (by funext Z; rfl) (fun F G => by
    funext Z
    change F Z * G Z = F Z * G Z
    rfl)

@[simp] theorem evalAlgHom_of (k : ℤ) (F : SiegelModularForm n k) :
    evalAlgHom (DirectSum.of (SiegelModularForm n) k F) = F := by
  simp [evalAlgHom, DirectSum.toAlgebra, coeLinearMap]

/-- The `m`-th power of a form of weight `k`, a form of weight `m * k`. -/
def pow (F : SiegelModularForm n k) (m : ℕ) : SiegelModularForm n (m * k) :=
  m.rec (mcast (by simp) (1 : SiegelModularForm n 0)) (fun m G => mcast (by grind) (G.mul F))

@[simp] theorem coe_pow (F : SiegelModularForm n k) (m : ℕ) : ⇑(F.pow m) = ⇑F ^ m := by
  induction m with
  | zero => funext Z; simp [pow]
  | succ m ih =>
    funext Z
    have h : (F.pow (m + 1)) Z = (F.pow m) Z * F Z := rfl
    rw [h, ih, Pi.pow_apply, Pi.pow_apply, pow_succ]

end SiegelModularForm

end TauTrack.Siegel
