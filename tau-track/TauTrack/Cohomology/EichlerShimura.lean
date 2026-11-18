module

public import TauTrack.Cohomology.Parabolic
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.EichlerShimura
import Mathlib.Tactic

/-!
# Eichler–Shimura: two copies of the cusp forms are the parabolic cohomology

For `w` even and positive and `k = w + 2`:

  `S_k(SL(2, ℤ)) × S_k(SL(2, ℤ)) ≃ H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`.

The map sends `(f, g)` to the class of the parabolic cocycle whose value at `S` is
`r_f⁺ + r_g⁻`, the even period polynomial of `f` plus the odd period polynomial of `g`.

The analysis is TauCeti's: `periodPolynomialEquiv : M_k × S_k ≃ W_w`, with the Eisenstein series
`E_k` going to `X^w − Y^w`. What is added here is the cohomological reading
(`Parabolic.lean`): `H¹_par = W_w ⧸ ⟨X^w − Y^w⟩`. Dividing `M_k = S_k ⊕ ℂ E_k` by the Eisenstein
line on both sides gives the statement.

* `eichlerShimuraMap`: the map `S_k × S_k → H¹_par`.
* `eichlerShimuraParabolic`: it is a linear equivalence.
* `finrank_parabolicH1`: `dim H¹_par = 2 dim S_k`.
-/

@[expose] public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups
open UpperHalfPlane ModularForm

namespace TauTrack.Cohomology

variable {w : ℕ}

theorem weight_eq (w : ℕ) : ((w + 2 : ℕ) : ℤ) = (w : ℤ) + 2 := by
  push_cast
  rfl

/-- The Eichler–Shimura map `(f, g) ↦ [r_f⁺ + r_g⁻]` from two copies of the cusp forms of weight
`w + 2` to the parabolic cohomology with coefficients in binary forms of degree `w`. -/
noncomputable def eichlerShimuraMap (hw : Even w) :
    (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) →ₗ[ℂ] ParabolicH1 ℂ w :=
  periodToH1 (R := ℂ) hw ∘ₗ (TauCeti.periodPolynomialEquiv (weight_eq w)).toLinearMap ∘ₗ
    (CuspForm.toModularFormₗ.prodMap LinearMap.id)

theorem eichlerShimuraMap_apply (hw : Even w)
    (f g : CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) :
    eichlerShimuraMap hw (f, g) =
      periodToH1 hw (TauCeti.periodPolynomialEquiv (weight_eq w) (CuspForm.toModularFormₗ f, g)) :=
  rfl

/-- TauCeti's isomorphism sends `(E_k, 0)` to `X^w − Y^w`. -/
theorem periodPolynomialEquiv_E (hw : Even w) (hw0 : w ≠ 0) (hk3 : 3 ≤ w + 2) :
    TauCeti.periodPolynomialEquiv (weight_eq w) (ModularForm.E hk3, 0) =
      eisensteinPeriod ℂ w hw := by
  apply Subtype.ext
  rw [TauCeti.coe_periodPolynomialEquiv_apply,
    TauCeti.extendedEvenPeriodPolynomialEquiv_E (weight_eq w) hw hw0 hk3]
  simp [eisensteinPeriod]

/-- The class of `X^w − Y^w` is zero. -/
theorem periodToH1_eisensteinPeriod (hw : Even w) :
    periodToH1 (R := ℂ) hw (eisensteinPeriod ℂ w hw) = 0 := by
  rw [← LinearMap.mem_ker, ker_periodToH1]
  exact Submodule.mem_span_singleton_self _

theorem eichlerShimuraMap_injective (hw : Even w) (hw0 : w ≠ 0) :
    Function.Injective (eichlerShimuraMap hw) := by
  have hk3 : 3 ≤ w + 2 := by omega
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨f, g⟩ h
  have h1 : TauCeti.periodPolynomialEquiv (weight_eq w) (CuspForm.toModularFormₗ f, g) ∈
      LinearMap.ker (periodToH1 (R := ℂ) hw) := h
  rw [ker_periodToH1, Submodule.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  rw [← periodPolynomialEquiv_E hw hw0 hk3, ← map_smul] at hc
  have h2 := (TauCeti.periodPolynomialEquiv (weight_eq w)).injective hc
  have hg : g = 0 := by
    have := congrArg Prod.snd h2
    simpa using this.symm
  have hf : CuspForm.toModularFormₗ f = c • ModularForm.E hk3 := by
    have := congrArg Prod.fst h2
    simpa using this.symm
  have hdisj := (TauCeti.isCompl_cuspFormSubmodule_span_E hk3 (hw.add even_two)).disjoint
  have h0 : CuspForm.toModularFormₗ f = 0 :=
    Submodule.disjoint_def.mp hdisj _ (LinearMap.mem_range_self _ f)
      (hf ▸ Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))
  have hf0 : f = 0 := CuspForm.toModularFormₗ_injective (by rw [h0, map_zero])
  rw [hf0, hg]
  rfl

theorem eichlerShimuraMap_surjective (hw : Even w) (hw0 : w ≠ 0) :
    Function.Surjective (eichlerShimuraMap hw) := by
  have : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  have hk3 : 3 ≤ w + 2 := by omega
  intro x
  obtain ⟨P, rfl⟩ := periodToH1_surjective (R := ℂ) hw x
  obtain ⟨⟨F, g⟩, rfl⟩ := (TauCeti.periodPolynomialEquiv (weight_eq w)).surjective P
  have htop := (TauCeti.isCompl_cuspFormSubmodule_span_E hk3 (hw.add even_two)).sup_eq_top
  have hF : F ∈ ModularForm.cuspFormSubmodule 𝒮ℒ ((w + 2 : ℕ) : ℤ) ⊔ ℂ ∙ ModularForm.E hk3 :=
    htop ▸ Submodule.mem_top
  obtain ⟨F₁, ⟨f, rfl⟩, F₂, hF₂, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hF₂
  refine ⟨(f, g), ?_⟩
  have hsplit : ((CuspForm.toModularFormₗ f + c • ModularForm.E hk3, g) :
      ModularForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) =
      (CuspForm.toModularFormₗ f, g) + c • (ModularForm.E hk3, 0) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, periodPolynomialEquiv_E hw hw0 hk3, map_add, map_smul,
    periodToH1_eisensteinPeriod, smul_zero, add_zero]
  rfl

/-- **Eichler–Shimura for parabolic cohomology**: for `w` even and positive,
`S_{w+2} × S_{w+2} ≃ H¹_par(SL(2, ℤ), V_w ⊗ ℂ)`. -/
noncomputable def eichlerShimuraParabolic (hw : Even w) (hw0 : w ≠ 0) :
    (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ) × CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) ≃ₗ[ℂ] ParabolicH1 ℂ w :=
  LinearEquiv.ofBijective (eichlerShimuraMap hw)
    ⟨eichlerShimuraMap_injective hw hw0, eichlerShimuraMap_surjective hw hw0⟩

/-- **`dim H¹_par(SL(2, ℤ), V_w) = 2 dim S_{w+2}`.** -/
theorem finrank_parabolicH1 (hw : Even w) (hw0 : w ≠ 0) :
    Module.finrank ℂ (ParabolicH1 ℂ w) =
      2 * Module.finrank ℂ (CuspForm 𝒮ℒ ((w + 2 : ℕ) : ℤ)) := by
  rw [← (eichlerShimuraParabolic hw hw0).finrank_eq, Module.finrank_prod, two_mul]

end TauTrack.Cohomology
