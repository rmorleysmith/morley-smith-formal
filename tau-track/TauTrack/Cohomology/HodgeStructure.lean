module

public import TauTrack.Cohomology.PeriodConjPoly
public import TauTrack.Cohomology.EichlerShimura
public import TauCeti.Geometry.Hodge.Structure
import Mathlib.Tactic

/-!
# The Hodge structure on the parabolic cohomology of `SL(2, ℤ)`

For `w` even and positive and `k = w + 2`, the parabolic cohomology
`H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`, in the model `W_w ⧸ ⟨X^w − Y^w⟩` of period polynomials modulo the
Eisenstein line (`parabolicH1Equiv`), carries

* a conjugation `parabolicConjugation`: conjugation of the coefficients of a period polynomial
  (the real structure whose fixed points are the classes of real period polynomials);
* a subspace `hodgeF`: the classes of the period polynomials `r_f`, `f ∈ S_k`, i.e. the image of
  the diagonal under the Eichler–Shimura isomorphism.

* `conj_hodgeF`: the conjugate of `hodgeF` is the image of the antidiagonal
  `{(−g, g)}`, because `conj(r_f) = −r_{f^c} ∣ ε = −r_{f^c}⁺ + r_{f^c}⁻`.
* `isCompl_hodgeF`: `hodgeF` and its conjugate are complementary.
* `parabolicHodgeStructure`: **a pure Hodge structure of weight `k − 1 = w + 1`** in TauCeti's
  sense (`TauCeti.Hodge.HodgeStructureOn`), with filtration `F^p = everything` for `p ≤ 0`,
  `F^p = hodgeF` for `1 ≤ p ≤ w + 1`, and `F^p = 0` beyond: the Hodge types are `(k − 1, 0)`
  and `(0, k − 1)`.
* `finrank_hodgeF`: `dim H^{k−1,0} = dim S_k`.

This is the Hodge realisation of the cusp forms of weight `k`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial
open scoped MatrixGroups ModularForm
open TauCeti.Hodge

namespace TauTrack.Cohomology

variable {w : ℕ}

/-! ## The conjugation -/

variable (w) in
/-- Conjugation of coefficients on binary forms, as a conjugation in TauCeti's sense. -/
noncomputable def binaryConjugation : Conjugation (homogeneousSubmodule (Fin 2) ℂ w) where
  toEquiv := binaryConj w
  involutive := binaryConjLin_involutive

variable (w) in
/-- Conjugation of coefficients on the period polynomials `W_w`. -/
noncomputable def periodConjugation : Conjugation (PeriodSpace ℂ w) :=
  (binaryConjugation w).restrict (U := TauCeti.periodPolynomials ℂ w)
    fun _ hP => binaryConj_mem_periodPolynomials hP

theorem coe_periodConjugation (P : PeriodSpace ℂ w) :
    ((periodSpaceEquiv ℂ w ((periodConjugation w).toEquiv P) : TauCeti.periodPolynomials ℂ w) :
        homogeneousSubmodule (Fin 2) ℂ w) =
      binaryConj w ((periodSpaceEquiv ℂ w P : TauCeti.periodPolynomials ℂ w) :
        homogeneousSubmodule (Fin 2) ℂ w) :=
  (binaryConjugation w).restrict_toEquiv_apply _ (periodSpaceEquiv ℂ w P)

/-- The Eisenstein line in `W_w`. -/
noncomputable abbrev eisensteinLine (hw : Even w) : Submodule ℂ (PeriodSpace ℂ w) :=
  ℂ ∙ (periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw)

theorem periodConjugation_eisenstein (hw : Even w) :
    (periodConjugation w).toEquiv ((periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw)) =
      (periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw) := by
  have he : ((eisensteinPeriod ℂ w hw : TauCeti.periodPolynomials ℂ w) :
      homogeneousSubmodule (Fin 2) ℂ w) = TauCeti.eisensteinPeriodPolynomial ℂ w := rfl
  apply (periodSpaceEquiv ℂ w).injective
  apply Subtype.ext
  rw [coe_periodConjugation, LinearEquiv.apply_symm_apply, he]
  apply Subtype.ext
  rw [coe_binaryConj, TauCeti.coe_eisensteinPeriodPolynomial]
  simp

theorem periodConjugation_mem_eisensteinLine (hw : Even w) (x : PeriodSpace ℂ w)
    (hx : x ∈ eisensteinLine hw) : (periodConjugation w).toEquiv x ∈ eisensteinLine hw := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smulₛₗ, periodConjugation_eisenstein]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The conjugation on `H¹_par`**, in the model `W_w ⧸ ⟨X^w − Y^w⟩`. -/
noncomputable def parabolicConjugation (hw : Even w) :
    Conjugation (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  (periodConjugation w).quotient (periodConjugation_mem_eisensteinLine hw)

/-! ## The Eichler–Shimura isomorphism in this model -/

/-- The Eichler–Shimura isomorphism `S_k × S_k ≃ W_w ⧸ ⟨X^w − Y^w⟩`. -/
noncomputable def eichlerShimuraPeriod (hw : Even w) (hw0 : w ≠ 0) :
    (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) ≃ₗ[ℂ]
      (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  (eichlerShimuraParabolic hw hw0).trans (parabolicH1Equiv hw).symm

theorem eichlerShimuraPeriod_apply (hw : Even w) (hw0 : w ≠ 0)
    (f g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    eichlerShimuraPeriod hw hw0 (f, g) = Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm
      (TauCeti.periodPolynomialEquiv (weight_eq w) (CuspForm.toModularFormₗ f, g))) := by
  rw [eichlerShimuraPeriod, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    parabolicH1Equiv_mk]
  rfl

/-- On the diagonal the Eichler–Shimura map is the class of the period polynomial. -/
theorem eichlerShimuraPeriod_diag (hw : Even w) (hw0 : w ≠ 0)
    (f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    eichlerShimuraPeriod hw hw0 (f, f) = Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm
      (TauCeti.periodPolynomial (weight_eq w) f)) := by
  rw [eichlerShimuraPeriod_apply]
  congr 2
  exact TauCeti.periodPolynomialEquiv_coe_cuspForm_same (weight_eq w) f

/-- `(−g, g)` goes to the class of `−r_g ∣ ε`. -/
theorem coe_periodPolynomialEquiv_neg (g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    (TauCeti.periodPolynomialEquiv (weight_eq w) (CuspForm.toModularFormₗ (-g), g) :
        homogeneousSubmodule (Fin 2) ℂ w) =
      -TauCeti.binaryFormRep ℂ w (op !![-1, 0; 0, 1])
        (TauCeti.periodPolynomial (weight_eq w) g : homogeneousSubmodule (Fin 2) ℂ w) := by
  rw [TauCeti.coe_periodPolynomialEquiv_apply]
  simp only [map_neg, Submodule.coe_neg]
  have h1 : (TauCeti.extendedEvenPeriodPolynomialEquiv (weight_eq w) (CuspForm.toModularFormₗ g) :
      homogeneousSubmodule (Fin 2) ℂ w) = TauCeti.evenPeriodPolynomial (weight_eq w) g :=
    congrArg _ (TauCeti.extendedEvenPeriodPolynomialEquiv_coe_cuspForm (weight_eq w) g)
  rw [h1, TauCeti.oddPeriodPolynomialEquiv_apply, TauCeti.coe_evenPeriodPolynomial,
    TauCeti.coe_oddPeriodPolynomial]
  module

/-- **Conjugation on the diagonal**: the conjugate of the class of `r_f` is the image of
`(−f^c, f^c)`. -/
theorem parabolicConjugation_diag (hw : Even w) (hw0 : w ≠ 0)
    (f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    (parabolicConjugation hw).toEquiv (eichlerShimuraPeriod hw hw0 (f, f)) =
      eichlerShimuraPeriod hw hw0 (-conjForm f, conjForm f) := by
  rw [eichlerShimuraPeriod_diag, eichlerShimuraPeriod_apply, parabolicConjugation,
    Conjugation.quotient_toEquiv_mk]
  congr 1
  apply (periodSpaceEquiv ℂ w).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_periodConjugation, LinearEquiv.apply_symm_apply,
    binaryConj_periodPolynomial (weight_eq w) hw]
  exact (coe_periodPolynomialEquiv_neg (conjForm f)).symm

/-! ## The Hodge filtration -/

/-- The diagonal embedding `f ↦ (f, f)`. -/
noncomputable def diagMap (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] V × V :=
  LinearMap.prod LinearMap.id LinearMap.id

/-- The antidiagonal embedding `g ↦ (−g, g)`. -/
noncomputable def antidiagMap (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] V × V :=
  LinearMap.prod (-LinearMap.id) LinearMap.id

theorem isCompl_range_diag_antidiag (V : Type*) [AddCommGroup V] [Module ℂ V] :
    IsCompl (LinearMap.range (diagMap V)) (LinearMap.range (antidiagMap V)) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ ⟨f, rfl⟩ ⟨g, hg⟩
    have h1 : -g = f := congrArg Prod.fst hg
    have h2 : g = f := congrArg Prod.snd hg
    rw [h2] at h1
    have h3 : (2 : ℂ) • f = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      exact neg_add_cancel f
    have hf : f = 0 := (smul_eq_zero.mp h3).resolve_left two_ne_zero
    rw [hf, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨a, b⟩ -
    refine Submodule.mem_sup.mpr ⟨((2 : ℂ)⁻¹ • (a + b), (2 : ℂ)⁻¹ • (a + b)),
      ⟨(2 : ℂ)⁻¹ • (a + b), rfl⟩, (-((2 : ℂ)⁻¹ • (b - a)), (2 : ℂ)⁻¹ • (b - a)),
      ⟨(2 : ℂ)⁻¹ • (b - a), rfl⟩, ?_⟩
    ext
    · simp only [Prod.mk_add_mk]
      module
    · simp only [Prod.mk_add_mk]
      module

/-- **The Hodge subspace `H^{k−1,0}`**: the classes of the period polynomials `r_f`. -/
noncomputable def hodgeF (hw : Even w) (hw0 : w ≠ 0) :
    Submodule ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  (LinearMap.range (diagMap (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)))).map
    (eichlerShimuraPeriod hw hw0).toLinearMap

/-- The conjugate subspace `H^{0,k−1}`: the image of the antidiagonal. -/
noncomputable def hodgeFbar (hw : Even w) (hw0 : w ≠ 0) :
    Submodule ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  (LinearMap.range (antidiagMap (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)))).map
    (eichlerShimuraPeriod hw hw0).toLinearMap

/-- **`H^{k−1,0}` and `H^{0,k−1}` are complementary.** -/
theorem isCompl_hodgeF (hw : Even w) (hw0 : w ≠ 0) :
    IsCompl (hodgeF hw hw0) (hodgeFbar hw hw0) :=
  (Submodule.orderIsoMapComap (eichlerShimuraPeriod hw hw0)).isCompl
    (isCompl_range_diag_antidiag _)

/-- **Conjugation exchanges the two Hodge subspaces.** -/
theorem conj_hodgeF (hw : Even w) (hw0 : w ≠ 0) :
    (hodgeF hw hw0).map (parabolicConjugation hw).toEquiv.toLinearMap = hodgeFbar hw hw0 := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨conjForm f, rfl⟩, ?_⟩
    exact (parabolicConjugation_diag hw hw0 f).symm
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨eichlerShimuraPeriod hw hw0 (conjForm g, conjForm g),
      ⟨_, ⟨conjForm g, rfl⟩, rfl⟩, ?_⟩
    have h := parabolicConjugation_diag hw hw0 (conjForm g)
    rw [conjForm, conjForm, CuspForm.conj_conj] at h
    exact h

/-- **The Hodge structure of weight `k − 1 = w + 1` on the parabolic cohomology of
`SL(2, ℤ)` with coefficients in binary forms of degree `w`.** -/
noncomputable def parabolicHodgeStructure (hw : Even w) (hw0 : w ≠ 0) :
    HodgeStructureOn (PeriodSpace ℂ w ⧸ eisensteinLine hw) (parabolicConjugation hw)
      ((w : ℤ) + 1) where
  F p := if p ≤ 0 then ⊤ else if p ≤ (w : ℤ) + 1 then hodgeF hw hw0 else ⊥
  F_antitone := by
    intro p q hpq
    by_cases hq : q ≤ 0
    · have hp : p ≤ 0 := hpq.trans hq
      simp [hp, hq]
    · by_cases hp : p ≤ 0
      · simp [hp]
      · by_cases hq2 : q ≤ (w : ℤ) + 1
        · have hp2 : p ≤ (w : ℤ) + 1 := hpq.trans hq2
          simp [hp, hq, hp2, hq2]
        · simp [hq, hq2]
  F_top := ⟨0, by simp⟩
  opposed p := by
    by_cases hp : p ≤ 0
    · have h1 : ¬ ((w : ℤ) + 1 + 1 - p ≤ 0) := by omega
      have h2 : ¬ ((w : ℤ) + 1 + 1 - p ≤ (w : ℤ) + 1) := by omega
      simp only [hp, h1, h2, ↓reduceIte, Submodule.map_bot]
      exact isCompl_top_bot
    · by_cases hp2 : p ≤ (w : ℤ) + 1
      · have h1 : ¬ ((w : ℤ) + 1 + 1 - p ≤ 0) := by omega
        have h2 : (w : ℤ) + 1 + 1 - p ≤ (w : ℤ) + 1 := by omega
        simp only [hp, hp2, h1, h2, ↓reduceIte, conj_hodgeF]
        exact isCompl_hodgeF hw hw0
      · have h1 : (w : ℤ) + 1 + 1 - p ≤ 0 := by omega
        simp only [hp, hp2, h1, ↓reduceIte, Submodule.map_top]
        rw [LinearMap.range_eq_top.mpr (parabolicConjugation hw).toEquiv.surjective]
        exact isCompl_bot_top

/-- **`dim H^{k−1,0} = dim S_k`.** -/
theorem finrank_hodgeF (hw : Even w) (hw0 : w ≠ 0) :
    Module.finrank ℂ (hodgeF hw hw0) =
      Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  have hinj : Function.Injective
      ((eichlerShimuraPeriod hw hw0).toLinearMap ∘ₗ diagMap (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ))) := by
    refine (eichlerShimuraPeriod hw hw0).injective.comp fun f g h => ?_
    simpa [diagMap] using congrArg Prod.fst h
  have e : hodgeF hw hw0 = LinearMap.range
      ((eichlerShimuraPeriod hw hw0).toLinearMap ∘ₗ diagMap (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ))) := by
    rw [hodgeF, LinearMap.range_comp]
  rw [e]
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm

end TauTrack.Cohomology
