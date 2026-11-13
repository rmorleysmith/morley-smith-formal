module

public import TauTrack.Siegel.Form

/-!
# The Petersson integrand of Siegel modular forms

* `detIm_act`: `det Im(M·Z) = det Im(Z) / |j(M, Z)|²`.
* `petersson k F G Z = conj(F Z) · G Z · (det Im Z)^k`, the integrand of the Petersson inner
  product.
* `petersson_slash`: `petersson k (F ∣[k] M) (G ∣[k] M) Z = petersson k F G (M·Z)`.
* `SiegelModularForm.petersson_smul`: for two Siegel modular forms of weight `k`, the Petersson
  integrand is invariant under `Sp(2n, ℤ)`, so it is a function on the quotient
  `Sp(2n, ℤ) \ ℍ_n`.

This is the first step towards the inner product `⟨F, G⟩ = ∫ conj(F) G (det Y)^k dμ` on cusp
forms; the invariant measure, a fundamental domain and convergence are not done here.
-/

@[expose] public section

open Matrix Complex
open scoped ComplexOrder ComplexConjugate

namespace TauTrack.Siegel

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det Im Z`. -/
noncomputable def detIm (Z : Matrix n n ℂ) : ℝ := (Z.map Complex.im).det

theorem det_cx (Y : Matrix n n ℝ) : (cx Y).det = (Y.det : ℂ) := by
  rw [cx_eq]; exact (RingHom.map_det Complex.ofRealHom Y).symm

theorem detIm_pos {Z : Matrix n n ℂ} (hZ : IsSiegel Z) : 0 < detIm Z := hZ.2.det_pos

/-- `det Im(M·Z) = det Im(Z) / |j(M, Z)|²`. -/
theorem detIm_act {M : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hM : M ∈ symplecticGroup n ℝ)
    {Z : Matrix n n ℂ} (hZ : IsSiegel Z) :
    detIm (act M Z) = detIm Z / ‖j M Z‖ ^ 2 := by
  have h := congrArg Matrix.det (imH_act hM hZ)
  rw [imH_of_isSymm (isSiegel_act hM hZ).1, imH_of_isSymm hZ.1, Matrix.det_mul,
    Matrix.det_mul, det_cx, det_cx, Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hj : j M Z ≠ 0 := j_ne_zero hM hZ
  have h2 : ((detIm (act M Z) : ℝ) : ℂ) = ((detIm Z / ‖j M Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [detIm, detIm, h]
    push_cast
    rw [← Complex.conj_mul' (j M Z)]
    change star (j M Z)⁻¹ * _ * (j M Z)⁻¹ = _
    rw [star_inv₀]
    have hs : star (j M Z) ≠ 0 := star_ne_zero.mpr hj
    change (star (j M Z))⁻¹ * _ * (j M Z)⁻¹ = _ / (star (j M Z) * j M Z)
    field_simp
  exact_mod_cast h2

/-- The Petersson integrand `conj(F Z) · G Z · (det Im Z)^k`. -/
noncomputable def petersson (k : ℤ) (F G : SiegelUpperHalfSpace n → ℂ)
    (Z : SiegelUpperHalfSpace n) : ℂ :=
  conj (F Z) * G Z * ((detIm Z.1 : ℝ) : ℂ) ^ k

/-- `petersson k (F ∣[k] M) (G ∣[k] M) Z = petersson k F G (M·Z)`. -/
theorem petersson_slash (k : ℤ) (F G : SiegelUpperHalfSpace n → ℂ) (M : symplecticGroup n ℝ)
    (Z : SiegelUpperHalfSpace n) :
    petersson k (slash k M F) (slash k M G) Z = petersson k F G (M • Z) := by
  have hj : j M.1 Z.1 ≠ 0 := j_ne_zero M.2 Z.2
  have hd : detIm (M • Z).1 = detIm Z.1 / ‖j M.1 Z.1‖ ^ 2 := detIm_act M.2 Z.2
  rw [petersson, petersson, slash_apply, slash_apply, hd]
  push_cast
  rw [← Complex.conj_mul' (j M.1 Z.1), div_zpow, mul_zpow, map_mul, map_zpow₀]
  have hs : conj (j M.1 Z.1) ≠ 0 := (map_ne_zero _).mpr hj
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

/-- For two Siegel modular forms of weight `k` the Petersson integrand is invariant under
`Sp(2n, ℤ)`. -/
theorem SiegelModularForm.petersson_smul {k : ℤ} (F G : SiegelModularForm n k)
    (γ : symplecticGroup n ℤ) (Z : SiegelUpperHalfSpace n) :
    petersson k F G (ofInt γ • Z) = petersson k F G Z := by
  rw [← petersson_slash]
  have hF : slash k (ofInt γ) F = F := F.slash_eq γ
  have hG : slash k (ofInt γ) G = G := G.slash_eq γ
  rw [hF, hG]

/-- `petersson k F F Z = |F(Z)|² · (det Im Z)^k ≥ 0`. -/
theorem petersson_self (k : ℤ) (F : SiegelUpperHalfSpace n → ℂ) (Z : SiegelUpperHalfSpace n) :
    petersson k F F Z = ((‖F Z‖ ^ 2 * detIm Z.1 ^ k : ℝ) : ℂ) := by
  rw [petersson, Complex.conj_mul']
  push_cast
  rfl

end TauTrack.Siegel
