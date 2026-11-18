module

public import TauTrack.Cohomology.PeriodCocycleConverse
public import TauTrack.Cohomology.Presentation

/-!
# Period polynomials are exactly the values at `S` of parabolic cocycles

Combining `IsCocycle.map_S_mem_periodPolynomials`, `exists_cocycle_of_mem_periodPolynomials` and
the presentation of `PSL(2, ℤ)` (`exists_hom_of_relations`):

for `w` even and `2` invertible, a binary form `P` of degree `w` lies in the period-polynomial
space `W_w = ker(1 + S) ∩ ker(1 + U + U²)` if and only if `P = φ(S)` for a 1-cocycle
`φ : SL(2, ℤ) → V_w` with `φ(T) = 0`; and that cocycle is unique.
-/

@[expose] public section

open Matrix MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauTrack.Cohomology

/-- The presentation of `PSL(2, ℤ)`, in the form used by the converse theorem. -/
theorem hasPresentation (G : Type*) [Group G] : HasPresentation G :=
  fun s u hs hu => exists_hom_of_relations s u hs hu

variable {R : Type*} [CommRing R] {w : ℕ}

/-- **Period polynomials are exactly the values at `S` of parabolic cocycles.** -/
theorem mem_periodPolynomials_iff_exists_cocycle [Invertible (2 : R)] (hw : Even w)
    (P : homogeneousSubmodule (Fin 2) R w) :
    P ∈ TauCeti.periodPolynomials R w ↔
      ∃ φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w, IsCocycle φ ∧ φ T = 0 ∧ φ S = P := by
  constructor
  · exact fun hP => exists_cocycle_of_mem_periodPolynomials (hasPresentation _) hw hP
  · rintro ⟨φ, hφ, hT, rfl⟩
    exact hφ.map_S_mem_periodPolynomials hw hT

/-- The parabolic cocycle with a given value at `S` is unique. -/
theorem existsUnique_cocycle_of_mem_periodPolynomials (hw : Even w)
    {P : homogeneousSubmodule (Fin 2) R w} (hP : P ∈ TauCeti.periodPolynomials R w) :
    ∃! φ : SL(2, ℤ) → homogeneousSubmodule (Fin 2) R w, IsCocycle φ ∧ φ T = 0 ∧ φ S = P := by
  obtain ⟨φ, hφ, hT, hS⟩ := exists_cocycle_of_mem_periodPolynomials (hasPresentation _) hw hP
  refine ⟨φ, ⟨hφ, hT, hS⟩, ?_⟩
  rintro ψ ⟨hψ, hψT, hψS⟩
  exact IsCocycle.eq_of_map_S_eq hψ hφ hψT hT (hψS.trans hS.symm)

end TauTrack.Cohomology
