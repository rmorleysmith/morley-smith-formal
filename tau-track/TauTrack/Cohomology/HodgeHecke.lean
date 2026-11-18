module

public import TauTrack.Cohomology.HodgeStructure
public import TauTrack.RamanujanTau.Basic
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.Dimension
public import TauCeti.Geometry.Hodge.Substructure
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.EichlerShimura
public import TauCeti.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Tactic

/-!
# Hecke operators on the Hodge structure of `H¹_par(SL(2, ℤ), V_w)`

The Hecke operator `Tₙ` acts on `H¹_par`, in the model `W_w ⧸ ⟨X^w − Y^w⟩`, by transport of
`Tₙ × Tₙ` on `S_k × S_k` along the Eichler–Shimura isomorphism (`heckeParabolic`).

* `heckeParabolic_mk`: this is the action of Popa–Zagier's Hecke elements on period polynomials
  (TauCeti's `periodAction`): for every solution `ξ` of their period relation (A),
  `Tₙ [P] = [P ∣ ξ]`.
* `conjForm_hecke`: `(Tₙ f)^c = Tₙ (f^c)` (the Hecke operators are defined over `ℝ`).
* `parabolicConjugation_eichlerShimuraPeriod`: the conjugation on `H¹_par` is
  `(f, g) ↦ (−f^c, g^c)` on `S_k × S_k`.
* `isMorphism_heckeParabolic`: **`Tₙ` is an endomorphism of the Hodge structure**: it commutes
  with the conjugation and preserves the Hodge filtration.
* `hodgeNumber_top`, `hodgeNumber_zero`: `h^{k−1,0} = h^{0,k−1} = dim S_k`.

The plane of an eigenform:

* `eigenPlane`: the image of `ℂ f × ℂ f`; it has dimension two (`finrank_eigenPlane`), `Tₙ` acts
  on it by the eigenvalue (`heckeParabolic_eigenPlane`), and if `f^c = f` it is a sub-Hodge
  structure (`isSubstructure_eigenPlane`).

Weight 12 (`w = 10`), where `S₁₂ = ℂ Δ`:

* `conjForm_discriminant`: `Δ^c = Δ`.

* `heckeTCuspLevelOne_twelve`: `Tₙ = τ(n)` on `S₁₂`.
* `finrank_parabolic_ten`: `H¹_par(SL(2, ℤ), V₁₀)` has dimension `2`.
* `heckeParabolic_ten`: `Tₙ` acts on it as the scalar `τ(n)`.
* `hodgeNumber_ten`: its Hodge numbers are `h^{11,0} = h^{0,11} = 1`.

So `H¹_par(SL(2, ℤ), V₁₀)` is a Hodge structure of rank `2`, weight `11` and type
`(11, 0) + (0, 11)` on which `Tₙ` is `τ(n)`: the Hodge realisation of the motive of `Δ`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial MonoidAlgebra
open scoped MatrixGroups ModularForm
open TauCeti.Hodge TauCeti.TraceFormulaMatrixModule

namespace TauTrack.Cohomology

variable {w : ℕ}

/-! ## Conjugation and the Hecke operators on cusp forms -/

/-- **The Hecke operators commute with `f ↦ f^c`.** -/
theorem conjForm_hecke {k : ℤ} (n : ℕ) [NeZero n] (f : CuspForm 𝒮ℒ k) :
    conjForm (TauCeti.heckeTCuspLevelOne k n f) = TauCeti.heckeTCuspLevelOne k n (conjForm f) := by
  apply CuspForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  change UpperHalfPlane.qExpansion 1 ⇑(conjForm (TauCeti.heckeTCuspLevelOne k n f)) =
    UpperHalfPlane.qExpansion 1 ⇑(TauCeti.heckeTCuspLevelOne k n (conjForm f))
  ext m
  rw [CuspForm.qExpansion_conj one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_map, TauCeti.qExpansion_coeff_heckeTCuspLevelOne,
    TauCeti.qExpansion_coeff_heckeTCuspLevelOne, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, map_zpow₀, Complex.conj_natCast,
    CuspForm.qExpansion_conj one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_map]

/-! ## The Hecke operators on `H¹_par` -/

/-- `Tₙ × Tₙ` on `S_k × S_k`. -/
noncomputable def heckePair (w n : ℕ) [NeZero n] :
    Module.End ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :=
  (TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n).prodMap
    (TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n)

/-- **The Hecke operator `Tₙ` on `H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`**, in the model
`W_w ⧸ ⟨X^w − Y^w⟩`. -/
noncomputable def heckeParabolic (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n] :
    Module.End ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  (eichlerShimuraPeriod hw hw0).conj (heckePair w n)

theorem heckeParabolic_eichlerShimuraPeriod (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    (f g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    heckeParabolic hw hw0 n (eichlerShimuraPeriod hw hw0 (f, g)) =
      eichlerShimuraPeriod hw hw0 (TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n f,
        TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n g) := by
  rw [heckeParabolic, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The class of the period polynomial attached to `(f + c E_k, g)` is the Eichler–Shimura
image of `(f, g)`. -/
theorem mk_periodPolynomialEquiv (hw : Even w) (hw0 : w ≠ 0) (hk3 : 3 ≤ w + 2)
    (f g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) (c : ℂ) :
    (Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm
        (TauCeti.periodPolynomialEquiv (weight_eq w)
          (CuspForm.toModularFormₗ f + c • ModularForm.E hk3, g))) :
      PeriodSpace ℂ w ⧸ eisensteinLine hw) = eichlerShimuraPeriod hw hw0 (f, g) := by
  have hsplit : ((CuspForm.toModularFormₗ f + c • ModularForm.E hk3, g) :
      ModularForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) =
      (CuspForm.toModularFormₗ f, g) + c • (ModularForm.E hk3, 0) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, periodPolynomialEquiv_E hw hw0 hk3, map_add, map_smul,
    Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, eichlerShimuraPeriod_apply]
  have h0 : (Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm (eisensteinPeriod ℂ w hw)) :
      PeriodSpace ℂ w ⧸ eisensteinLine hw) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)
  rw [h0, smul_zero, add_zero]

/-- **`Tₙ` on `H¹_par` is the action of Popa–Zagier's Hecke elements on period polynomials**:
for every solution `ξ` of the period relation (A), `Tₙ [P] = [P ∣ ξ]`. -/
theorem heckeParabolic_mk (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    {ξ : ℂ[TauCeti.TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    (P : TauCeti.periodPolynomials ℂ w) :
    heckeParabolic hw hw0 n (Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm P)) =
      Submodule.Quotient.mk ((periodSpaceEquiv ℂ w).symm
        ⟨periodAction hw ξ P, h.periodAction_mem_periodPolynomials hw n P.2⟩) := by
  have hk3 : 3 ≤ w + 2 := by omega
  have hk2 : Even (w + 2) := hw.add even_two
  obtain ⟨⟨F, g⟩, rfl⟩ := (TauCeti.periodPolynomialEquiv (weight_eq w)).surjective P
  have htop := (TauCeti.isCompl_cuspFormSubmodule_span_E hk3 hk2).sup_eq_top
  have hF : F ∈ ModularForm.cuspFormSubmodule 𝒮ℒ ((w + 2 : ℕ) : ℤ) ⊔ ℂ ∙ ModularForm.E hk3 :=
    htop ▸ Submodule.mem_top
  obtain ⟨F₁, ⟨f, rfl⟩, F₂, hF₂, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hF₂
  have hact : (⟨periodAction hw ξ (TauCeti.periodPolynomialEquiv (weight_eq w)
        (CuspForm.toModularFormₗ f + c • ModularForm.E hk3, g)),
        h.periodAction_mem_periodPolynomials hw n (Subtype.property _)⟩ :
      TauCeti.periodPolynomials ℂ w) =
      TauCeti.periodPolynomialEquiv (weight_eq w)
        (CuspForm.toModularFormₗ (TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n f) +
          (c * (ArithmeticFunction.sigma (w + 2 - 1) n : ℂ)) • ModularForm.E hk3,
          TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n g) := by
    apply Subtype.ext
    refine (h.periodAction_periodPolynomialEquiv (weight_eq w) hw n _).trans ?_
    congr 3
    rw [map_add, map_smul, TauCeti.heckeTLevelOne_E hk3 hk2 n, smul_smul]
    congr 1
    exact TauCeti.heckeTLevelOne_coe_cuspForm _ n f
  rw [hact, mk_periodPolynomialEquiv hw hw0 hk3, mk_periodPolynomialEquiv hw hw0 hk3,
    heckeParabolic_eichlerShimuraPeriod]

/-! ## The conjugation in terms of cusp forms -/

/-- The conjugate of the image of the antidiagonal element `(−g, g)` is the image of
`(g^c, g^c)`. -/
theorem parabolicConjugation_antidiag (hw : Even w) (hw0 : w ≠ 0)
    (g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    (parabolicConjugation hw).toEquiv (eichlerShimuraPeriod hw hw0 (-g, g)) =
      eichlerShimuraPeriod hw hw0 (conjForm g, conjForm g) := by
  have h := parabolicConjugation_diag hw hw0 (conjForm g)
  rw [conjForm, conjForm, CuspForm.conj_conj] at h
  rw [← h, (parabolicConjugation hw).apply_apply]

/-- **The conjugation on `H¹_par` is `(f, g) ↦ (−f^c, g^c)`** on `S_k × S_k`. -/
theorem parabolicConjugation_eichlerShimuraPeriod (hw : Even w) (hw0 : w ≠ 0)
    (f g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    (parabolicConjugation hw).toEquiv (eichlerShimuraPeriod hw hw0 (f, g)) =
      eichlerShimuraPeriod hw hw0 (-conjForm f, conjForm g) := by
  have hfg : (f, g) = ((2 : ℂ)⁻¹ • (f + g), (2 : ℂ)⁻¹ • (f + g)) +
      (-((2 : ℂ)⁻¹ • (g + (-1 : ℂ) • f)), (2 : ℂ)⁻¹ • (g + (-1 : ℂ) • f)) := by
    ext1
    · simp only [Prod.mk_add_mk]
      module
    · simp only [Prod.mk_add_mk]
      module
  have hc : starRingEnd ℂ ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  have hc1 : starRingEnd ℂ (-1 : ℂ) = -1 := by
    rw [map_neg, map_one]
  nth_rewrite 1 [hfg]
  rw [map_add, map_add, parabolicConjugation_diag, parabolicConjugation_antidiag, ← map_add]
  congr 1
  simp only [conjForm, CuspForm.conj_smul, CuspForm.conj_add, hc, hc1]
  ext1
  · simp only [Prod.mk_add_mk]
    module
  · simp only [Prod.mk_add_mk]
    module

/-- **`Tₙ` commutes with the conjugation on `H¹_par`.** -/
theorem heckeParabolic_conj (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    (x : PeriodSpace ℂ w ⧸ eisensteinLine hw) :
    heckeParabolic hw hw0 n ((parabolicConjugation hw).toEquiv x) =
      (parabolicConjugation hw).toEquiv (heckeParabolic hw hw0 n x) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := (eichlerShimuraPeriod hw hw0).surjective x
  rw [parabolicConjugation_eichlerShimuraPeriod, heckeParabolic_eichlerShimuraPeriod,
    heckeParabolic_eichlerShimuraPeriod, parabolicConjugation_eichlerShimuraPeriod,
    conjForm_hecke, conjForm_hecke, map_neg]

/-- `Tₙ` preserves `H^{k−1,0}`. -/
theorem map_heckeParabolic_hodgeF (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n] :
    (hodgeF hw hw0).map (heckeParabolic hw hw0 n) ≤ hodgeF hw hw0 := by
  rintro _ ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩
  refine ⟨_, ⟨TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n f, rfl⟩, ?_⟩
  exact (heckeParabolic_eichlerShimuraPeriod hw hw0 n f f).symm

/-- **`Tₙ` is an endomorphism of the Hodge structure on `H¹_par(SL(2, ℤ), V_w)`.** -/
theorem isMorphism_heckeParabolic (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n] :
    HodgeStructureOn.IsMorphism (parabolicHodgeStructure hw hw0) (parabolicHodgeStructure hw hw0)
      (heckeParabolic hw hw0 n) where
  commutes_conj := heckeParabolic_conj hw hw0 n
  map_F_le p := by
    change (if p ≤ 0 then ⊤ else if p ≤ (w : ℤ) + 1 then hodgeF hw hw0 else ⊥).map _ ≤
      (if p ≤ 0 then ⊤ else if p ≤ (w : ℤ) + 1 then hodgeF hw hw0 else ⊥)
    split_ifs
    · exact le_top
    · exact map_heckeParabolic_hodgeF hw hw0 n
    · rw [Submodule.map_bot]

/-! ## Hodge numbers -/

theorem F_top_eq (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).F ((w : ℤ) + 1) = hodgeF hw hw0 := by
  have h1 : ¬ ((w : ℤ) + 1 ≤ 0) := by omega
  change (if (w : ℤ) + 1 ≤ 0 then ⊤ else if (w : ℤ) + 1 ≤ (w : ℤ) + 1 then hodgeF hw hw0 else ⊥) = _
  simp [h1]

theorem F_zero_eq (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).F 0 = ⊤ := by
  change (if (0 : ℤ) ≤ 0 then ⊤ else if (0 : ℤ) ≤ (w : ℤ) + 1 then hodgeF hw hw0 else ⊥) = _
  simp

/-- The Hodge component `H^{k−1,0}` is `hodgeF`. -/
theorem piece_top (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).piece ((w : ℤ) + 1) = hodgeF hw hw0 := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.conjF_def, sub_self, F_top_eq, F_zero_eq,
    Submodule.map_top, LinearMap.range_eq_top.mpr (parabolicConjugation hw).toEquiv.surjective,
    inf_top_eq]

/-- The Hodge component `H^{0,k−1}` is `hodgeFbar`. -/
theorem piece_zero (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).piece 0 = hodgeFbar hw hw0 := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.conjF_def, sub_zero, F_top_eq, F_zero_eq,
    conj_hodgeF, top_inf_eq]

/-- **`h^{k−1,0} = dim S_k`.** -/
theorem hodgeNumber_top (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).hodgeNumber ((w : ℤ) + 1) =
      Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  rw [HodgeStructureOn.hodgeNumber_def, piece_top, finrank_hodgeF]

/-- **`h^{0,k−1} = dim S_k`.** -/
theorem hodgeNumber_zero (hw : Even w) (hw0 : w ≠ 0) :
    (parabolicHodgeStructure hw hw0).hodgeNumber 0 =
      Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  rw [HodgeStructureOn.hodgeNumber_symm, sub_zero, hodgeNumber_top]

/-- `dim (W_w ⧸ ⟨X^w − Y^w⟩) = 2 dim S_k`. -/
theorem finrank_parabolic (hw : Even w) (hw0 : w ≠ 0) :
    Module.finrank ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) =
      2 * Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  rw [← (eichlerShimuraPeriod hw hw0).finrank_eq, Module.finrank_prod, two_mul]

/-! ## The plane of an eigenform -/

/-- `(c₁, c₂) ↦ (c₁ f, c₂ f)`. -/
noncomputable def planeMap {V : Type*} [AddCommGroup V] [Module ℂ V] (f : V) :
    ℂ × ℂ →ₗ[ℂ] V × V :=
  (LinearMap.toSpanSingleton ℂ V f).prodMap (LinearMap.toSpanSingleton ℂ V f)

theorem planeMap_apply {V : Type*} [AddCommGroup V] [Module ℂ V] (f : V) (c : ℂ × ℂ) :
    planeMap f c = (c.1 • f, c.2 • f) :=
  rfl

/-- **The plane of a cusp form `f`** in `H¹_par`: the Eichler–Shimura image of `ℂ f × ℂ f`. -/
noncomputable def eigenPlane (hw : Even w) (hw0 : w ≠ 0) (f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    Submodule ℂ (PeriodSpace ℂ w ⧸ eisensteinLine hw) :=
  LinearMap.range ((eichlerShimuraPeriod hw hw0).toLinearMap ∘ₗ planeMap f)

theorem mem_eigenPlane (hw : Even w) (hw0 : w ≠ 0) (f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ))
    (c₁ c₂ : ℂ) : eichlerShimuraPeriod hw hw0 (c₁ • f, c₂ • f) ∈ eigenPlane hw hw0 f :=
  ⟨(c₁, c₂), rfl⟩

/-- **The plane of a nonzero cusp form has dimension two.** -/
theorem finrank_eigenPlane (hw : Even w) (hw0 : w ≠ 0) {f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)}
    (hf : f ≠ 0) : Module.finrank ℂ (eigenPlane hw hw0 f) = 2 := by
  have hinj : Function.Injective ((eichlerShimuraPeriod hw hw0).toLinearMap ∘ₗ planeMap f) := by
    refine (eichlerShimuraPeriod hw hw0).injective.comp fun c d h => ?_
    rw [planeMap_apply, planeMap_apply, Prod.mk.injEq] at h
    exact Prod.ext (smul_left_injective ℂ hf h.1) (smul_left_injective ℂ hf h.2)
  rw [eigenPlane, ← (LinearEquiv.ofInjective _ hinj).finrank_eq, Module.finrank_prod,
    Module.finrank_self]

/-- **`Tₙ` acts on the plane of an eigenform by its eigenvalue.** -/
theorem heckeParabolic_eigenPlane (hw : Even w) (hw0 : w ≠ 0) (n : ℕ) [NeZero n]
    {f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)} {a : ℂ}
    (hf : TauCeti.heckeTCuspLevelOne ((w + 2 : ℕ) : ℤ) n f = a • f)
    {x : PeriodSpace ℂ w ⧸ eisensteinLine hw} (hx : x ∈ eigenPlane hw hw0 f) :
    heckeParabolic hw hw0 n x = a • x := by
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.comp_apply, planeMap_apply, LinearEquiv.coe_coe,
    heckeParabolic_eichlerShimuraPeriod, ← map_smul, map_smul, map_smul, hf, Prod.smul_mk,
    smul_comm a c.1, smul_comm a c.2]

/-- **The plane of a cusp form with real coefficients (`f^c = f`) is a sub-Hodge structure**,
with one line in `H^{k−1,0}` and one in `H^{0,k−1}`. -/
theorem isSubstructure_eigenPlane (hw : Even w) (hw0 : w ≠ 0)
    {f : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)} (hf : conjForm f = f) :
    (parabolicHodgeStructure hw hw0).IsSubstructure (eigenPlane hw hw0 f) where
  conj_mem := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.comp_apply, planeMap_apply, LinearEquiv.coe_coe,
      parabolicConjugation_eichlerShimuraPeriod]
    simp only [conjForm, CuspForm.conj_smul]
    rw [show CuspForm.conj levelOne_le_conjAct_inv_J f = f from hf, ← neg_smul]
    exact mem_eigenPlane hw hw0 f _ _
  le_iSup_inf_piece := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.comp_apply, planeMap_apply, LinearEquiv.coe_coe]
    have hsplit : (c.1 • f, c.2 • f) =
        ((((2 : ℂ)⁻¹ * (c.1 + c.2)) • f, ((2 : ℂ)⁻¹ * (c.1 + c.2)) • f) : _ × _) +
          ((-((2 : ℂ)⁻¹ * (c.2 - c.1))) • f, ((2 : ℂ)⁻¹ * (c.2 - c.1)) • f) := by
      ext1
      · simp only [Prod.mk_add_mk]
        module
      · simp only [Prod.mk_add_mk]
        module
    rw [hsplit, map_add]
    refine Submodule.add_mem _
      (Submodule.mem_iSup_of_mem ((w : ℤ) + 1) ⟨mem_eigenPlane hw hw0 f _ _, ?_⟩)
      (Submodule.mem_iSup_of_mem 0 ⟨mem_eigenPlane hw hw0 f _ _, ?_⟩)
    · rw [piece_top]
      exact ⟨_, ⟨((2 : ℂ)⁻¹ * (c.1 + c.2)) • f, rfl⟩, rfl⟩
    · rw [piece_zero]
      refine ⟨_, ⟨((2 : ℂ)⁻¹ * (c.2 - c.1)) • f, rfl⟩, ?_⟩
      rw [neg_smul]
      rfl

/-! ## Weight 12: the Hodge realisation of `Δ` -/

/-- `S₁₂(SL(2, ℤ))` has dimension one. -/
theorem finrank_cuspForm_twelve : Module.finrank ℂ (CuspForm 𝒮ℒ (12 : ℤ)) = 1 :=
  (CuspForm.dimension_level_one 12 (by decide)).trans (by decide)

/-- `Tₙ Δ = τ(n) Δ` in `S₁₂`. -/
theorem heckeTCuspLevelOne_discriminant (n : ℕ) [NeZero n] :
    TauCeti.heckeTCuspLevelOne 12 n CuspForm.discriminant =
      (ramanujanTau n : ℂ) • CuspForm.discriminant := by
  apply CuspForm.toModularFormₗ_injective
  rw [map_smul]
  exact (TauCeti.heckeTLevelOne_coe_cuspForm 12 n CuspForm.discriminant).symm.trans
    (heckeTLevelOne_Δ₁₂ n)

/-- **`Tₙ = τ(n)` on `S₁₂`.** -/
theorem heckeTCuspLevelOne_twelve (n : ℕ) [NeZero n] (f : CuspForm 𝒮ℒ (12 : ℤ)) :
    TauCeti.heckeTCuspLevelOne 12 n f = (ramanujanTau n : ℂ) • f := by
  have hΔ : (CuspForm.discriminant : CuspForm 𝒮ℒ (12 : ℤ)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun g : CuspForm 𝒮ℒ (12 : ℤ) => (g : UpperHalfPlane → ℂ)) h
    simp only [CuspForm.coe_discriminant] at h1
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I (congrFun h1 UpperHalfPlane.I)
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hΔ).mp finrank_cuspForm_twelve f
  rw [map_smul, heckeTCuspLevelOne_discriminant, smul_comm]

/-- `Δ^c = Δ`: the coefficients `τ(n)` are integers. -/
theorem conjForm_discriminant :
    conjForm (CuspForm.discriminant : CuspForm 𝒮ℒ (12 : ℤ)) = CuspForm.discriminant := by
  apply CuspForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
  change UpperHalfPlane.qExpansion 1 ⇑(conjForm (CuspForm.discriminant : CuspForm 𝒮ℒ (12 : ℤ))) =
    UpperHalfPlane.qExpansion 1 ⇑(CuspForm.discriminant : CuspForm 𝒮ℒ (12 : ℤ))
  ext m
  rw [CuspForm.qExpansion_conj one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_map,
    CuspForm.coe_discriminant, ramanujanTau_spec, map_intCast]

/-- **`H¹_par(SL(2, ℤ), V₁₀)` has dimension two.** -/
theorem finrank_parabolic_ten :
    Module.finrank ℂ (PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide)) = 2 := by
  rw [finrank_parabolic (by decide) (by decide)]
  exact congrArg (2 * ·) finrank_cuspForm_twelve

/-- **`Tₙ` acts on `H¹_par(SL(2, ℤ), V₁₀)` as the scalar `τ(n)`.** -/
theorem heckeParabolic_ten (n : ℕ) [NeZero n]
    (x : PeriodSpace ℂ 10 ⧸ eisensteinLine (w := 10) (by decide)) :
    heckeParabolic (w := 10) (by decide) (by decide) n x = (ramanujanTau n : ℂ) • x := by
  obtain ⟨⟨f, g⟩, rfl⟩ := (eichlerShimuraPeriod (w := 10) (by decide) (by decide)).surjective x
  rw [heckeParabolic_eichlerShimuraPeriod, ← map_smul]
  congr 1
  exact Prod.ext (heckeTCuspLevelOne_twelve n f) (heckeTCuspLevelOne_twelve n g)

/-- **The Hodge numbers of `H¹_par(SL(2, ℤ), V₁₀)` are `h^{11,0} = h^{0,11} = 1`.** -/
theorem hodgeNumber_ten :
    (parabolicHodgeStructure (w := 10) (by decide) (by decide)).hodgeNumber 11 = 1 ∧
      (parabolicHodgeStructure (w := 10) (by decide) (by decide)).hodgeNumber 0 = 1 := by
  refine ⟨?_, ?_⟩
  · exact (hodgeNumber_top (w := 10) (by decide) (by decide)).trans finrank_cuspForm_twelve
  · exact (hodgeNumber_zero (w := 10) (by decide) (by decide)).trans finrank_cuspForm_twelve

end TauTrack.Cohomology
