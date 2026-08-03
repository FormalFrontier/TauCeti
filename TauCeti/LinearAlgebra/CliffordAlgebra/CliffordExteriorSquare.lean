/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector

/-!
# Clifford bivectors and the degree-two filtration

The degree-two leading term of a half-normalized Clifford bivector is the exterior bivector that
gave rise to it. This identifies the exterior square faithfully with its image in the Clifford
algebra.

This is a Layer 0 to Layer 3 bridge in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean): the faithful
exterior-square model is needed before the bivector commutator construction can be transported
back from its Clifford range. It does not define that transported bracket, an orthogonal Lie
equivalence, coordinates, or a Spin action.

## Main results

* `TauCeti.CliffordAlgebra.filtrationLeadingTerm_apply_ιMulti_eq_cliffordBivector`: the
  degree-two leading-term equation.
* `TauCeti.CliffordAlgebra.cliffordBivectorExterior_injective`: injectivity of the exterior-square
  Clifford bivector map.
* `TauCeti.CliffordAlgebra.cliffordBivectorExteriorEquivRange`: the induced equivalence onto its
  range.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The degree filtration", and Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the
  Clifford algebra".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

private theorem equivExterior_ι_mul_ι_sub_swap (Q : QuadraticForm R M)
    [Invertible (2 : R)] (a b : M) :
    equivExterior Q (ι Q a * ι Q b - ι Q b * ι Q a) =
      ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b -
        ExteriorAlgebra.ι R b * ExteriorAlgebra.ι R a := by
  simp only [equivExterior, map_sub, changeFormEquiv_apply, changeForm_ι_mul_ι]
  rw [QuadraticMap.associated_isSymm R (-Q) a b]
  module

/-- `equivExterior` sends a half-normalized Clifford bivector to its exterior product. -/
theorem equivExterior_cliffordBivector (Q : QuadraticForm R M) [Invertible (2 : R)]
    (a b : M) :
    equivExterior Q (cliffordBivector Q a b) = ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b := by
  rw [cliffordBivector_def, map_smul, equivExterior_ι_mul_ι_sub_swap]
  rw [eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap a b),
    sub_neg_eq_add, ← two_smul R, invOf_smul_smul]

private theorem cliffordBivector_sub_ι_mul_ι_mem_filtration_one (Q : QuadraticForm R M)
    [Invertible (2 : R)] (a b : M) :
    cliffordBivector Q a b - ι Q a * ι Q b ∈ filtration Q 1 := by
  have htwice : (2 : R) • (cliffordBivector Q a b - ι Q a * ι Q b) =
      -(ι Q a * ι Q b + ι Q b * ι Q a) := by
    rw [cliffordBivector_def, smul_sub, smul_smul, mul_invOf_self]
    rw [one_smul, two_smul]
    module
  rw [← invOf_smul_smul (2 : R) (cliffordBivector Q a b - ι Q a * ι Q b), htwice]
  exact Submodule.smul_mem _ _ <| Submodule.neg_mem _ <|
    filtration_mono Q (by omega) (ι_mul_ι_add_swap_mem_filtration_zero Q a b)

/-- The degree-two leading term of a decomposable exterior bivector is its corresponding
half-normalized Clifford bivector modulo the lower filtration. -/
theorem filtrationLeadingTerm_apply_ιMulti_eq_cliffordBivector (Q : QuadraticForm R M)
    [Invertible (2 : R)] (a b : M) :
    filtrationLeadingTerm Q 1 (exteriorPower.ιMulti R 2 ![a, b]) =
      Submodule.Quotient.mk
        ⟨cliffordBivector Q a b, cliffordBivector_mem_filtration_two Q a b⟩ := by
  rw [filtrationLeadingTerm_apply_ιMulti, Submodule.Quotient.eq,
    Submodule.mem_comap, map_sub]
  simp only [Submodule.subtype_apply]
  have hprod : (List.ofFn ((ι Q) ∘ ![a, b])).prod = ι Q a * ι Q b := by
    simp
  rw [hprod]
  simpa only [neg_sub] using Submodule.neg_mem _
    (cliffordBivector_sub_ι_mul_ι_mem_filtration_one Q a b)

/-- The exterior-model equivalence composed with the Clifford bivector map is the identity. -/
theorem equivExterior_comp_cliffordBivectorExterior (Q : QuadraticForm R M)
    [Invertible (2 : R)] :
    (equivExterior Q).toLinearMap.comp (cliffordBivectorExterior Q) = (⋀[R]^2 M).subtype := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe]
  rw [hv, cliffordBivectorExterior_apply_ιMulti, equivExterior_cliffordBivector]
  simp

/-- The exterior-square Clifford bivector map is injective. -/
theorem cliffordBivectorExterior_injective (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (cliffordBivectorExterior Q) := by
  intro x y hxy
  have hlead : equivExterior Q (cliffordBivectorExterior Q x) =
      equivExterior Q (cliffordBivectorExterior Q y) := congrArg (equivExterior Q) hxy
  have hsub : (⋀[R]^2 M).subtype x = (⋀[R]^2 M).subtype y := by
    rw [← equivExterior_comp_cliffordBivectorExterior Q]
    exact hlead
  exact Subtype.ext hsub

/-- The exterior square is linearly equivalent to the range of the Clifford bivector map. -/
noncomputable def cliffordBivectorExteriorEquivRange (Q : QuadraticForm R M) [Invertible (2 : R)] :
    ⋀[R]^2 M ≃ₗ[R] LinearMap.range (cliffordBivectorExterior Q) :=
  LinearEquiv.ofInjective (cliffordBivectorExterior Q) (cliffordBivectorExterior_injective Q)

/-- Coercing the range equivalence back to the Clifford algebra recovers the original map. -/
@[simp]
theorem coe_cliffordBivectorExteriorEquivRange_apply (Q : QuadraticForm R M)
    [Invertible (2 : R)] (x : ⋀[R]^2 M) :
    (cliffordBivectorExteriorEquivRange Q x : CliffordAlgebra Q) =
      cliffordBivectorExterior Q x := by
  rw [cliffordBivectorExteriorEquivRange, LinearEquiv.ofInjective_apply]

/-- Applying the Clifford bivector map to the inverse equivalence recovers the range element. -/
@[simp]
theorem cliffordBivectorExteriorEquivRange_symm_apply (Q : QuadraticForm R M)
    [Invertible (2 : R)] (x : LinearMap.range (cliffordBivectorExterior Q)) :
    cliffordBivectorExterior Q ((cliffordBivectorExteriorEquivRange Q).symm x) = x := by
  rw [← coe_cliffordBivectorExteriorEquivRange_apply, LinearEquiv.apply_symm_apply]

end CliffordAlgebra

end TauCeti
