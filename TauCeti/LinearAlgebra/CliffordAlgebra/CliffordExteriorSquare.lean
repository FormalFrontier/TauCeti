/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.QuadraticLieSubalgebra

/-!
# Clifford bivectors and the exterior square

The half-normalized Clifford bivector map embeds the second exterior power faithfully in the
Clifford algebra. Its image is the canonical Lie subalgebra of quadratic elements, so the exterior
square is linearly equivalent to that subalgebra.

This is a generic prerequisite for transporting the Clifford commutator to the exterior square in
the spin representations roadmap. It does not define the transported bracket or identify it with
an orthogonal Lie algebra.

## Main results

* `TauCeti.CliffordAlgebra.equivExterior_cliffordBivector`: the exterior model sends a Clifford
  bivector to the corresponding exterior product.
* `TauCeti.CliffordAlgebra.cliffordBivectorExterior_injective`: the exterior-square Clifford
  bivector map is injective.
* `TauCeti.CliffordAlgebra.cliffordBivectorExteriorEquivQuadraticLieSubalgebra`: the exterior
  square is linearly equivalent to the quadratic Lie subalgebra.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
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

/-- The exterior model sends a half-normalized Clifford bivector to its exterior product. -/
theorem equivExterior_cliffordBivector (Q : QuadraticForm R M) [Invertible (2 : R)]
    (a b : M) :
    equivExterior Q (cliffordBivector Q a b) = ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b := by
  rw [cliffordBivector_def, map_smul, equivExterior_ι_mul_ι_sub_swap]
  rw [eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap a b),
    sub_neg_eq_add, ← two_smul R, invOf_smul_smul]

private theorem equivExterior_comp_cliffordBivectorExterior (Q : QuadraticForm R M)
    [Invertible (2 : R)] :
    (equivExterior Q).toLinearMap.comp (cliffordBivectorExterior Q) = (⋀[R]^2 M).subtype := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe]
  rw [hx, cliffordBivectorExterior_apply_ιMulti, equivExterior_cliffordBivector]
  simp

/-- The exterior-square Clifford bivector map is injective. -/
theorem cliffordBivectorExterior_injective (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (cliffordBivectorExterior Q) := by
  apply Function.Injective.of_comp (f := equivExterior Q)
  -- `of_comp` exposes function composition, while the named equation uses `LinearMap.comp`.
  change Function.Injective ((equivExterior Q).toLinearMap.comp (cliffordBivectorExterior Q))
  simpa only [equivExterior_comp_cliffordBivectorExterior] using
    Submodule.subtype_injective (⋀[R]^2 M)

/-- The second exterior power is linearly equivalent to the quadratic elements of the Clifford
algebra through the half-normalized Clifford bivector map. -/
noncomputable def cliffordBivectorExteriorEquivQuadraticLieSubalgebra
    (Q : QuadraticForm R M) [Invertible (2 : R)] :
    ⋀[R]^2 M ≃ₗ[R] ↥(quadraticLieSubalgebra Q) :=
  (LinearEquiv.ofInjective (cliffordBivectorExterior Q)
      (cliffordBivectorExterior_injective Q)).trans
    (LinearEquiv.ofEq _ _ (quadraticLieSubalgebra_toSubmodule_eq_range Q).symm)

/-- The quadratic element underlying the exterior-square equivalence is the Clifford bivector
map. -/
@[simp]
theorem coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_apply
    (Q : QuadraticForm R M) [Invertible (2 : R)] (x : ⋀[R]^2 M) :
    ((cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q x : quadraticLieSubalgebra Q) :
      CliffordAlgebra Q) = cliffordBivectorExterior Q x := by
  rw [cliffordBivectorExteriorEquivQuadraticLieSubalgebra, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

/-- Applying the Clifford bivector map to the inverse exterior-square equivalence recovers the
quadratic element. -/
@[simp]
theorem cliffordBivectorExteriorEquivQuadraticLieSubalgebra_symm_apply
    (Q : QuadraticForm R M) [Invertible (2 : R)] (x : quadraticLieSubalgebra Q) :
    cliffordBivectorExterior Q
      ((cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).symm x) = x := by
  rw [← coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_apply]
  exact congr_arg Subtype.val
    ((cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).apply_symm_apply x)

end CliffordAlgebra

end TauCeti
