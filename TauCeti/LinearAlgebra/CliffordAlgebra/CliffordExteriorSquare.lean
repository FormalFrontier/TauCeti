/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Lie.TransferInstance
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Subalgebra

/-!
# The exterior-square model of quadratic Clifford elements

The half-normalized Clifford bivector map identifies the second exterior power with the canonical
Lie subalgebra of quadratic elements in the Clifford algebra. Transporting its Lie structure
equips the exterior square with the corresponding commutator bracket.

This is a generic prerequisite for identifying bivectors with the orthogonal Lie algebra in the
spin representations roadmap. It does not construct that orthogonal Lie equivalence.

## Main results

* `CliffordAlgebra.bivectorExteriorEquivQuadraticLieSubalgebra`: the exterior
  square is linearly equivalent to the quadratic Lie subalgebra.
* `CliffordAlgebra.bivectorLieRing` and
  `CliffordAlgebra.bivectorLieAlgebra`: the Lie structures transported to the
  exterior square.
* `CliffordAlgebra.bivectorLieEquiv`: the transported Lie equivalence with the
  quadratic Lie subalgebra.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section


universe u v

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The second exterior power is linearly equivalent to the quadratic elements of the Clifford
algebra through the half-normalized Clifford bivector map. -/
noncomputable def bivectorExteriorEquivQuadraticLieSubalgebra :
    ⋀[R]^2 M ≃ₗ[R] ↥(quadraticLieSubalgebra Q) :=
  (LinearEquiv.ofInjective (bivectorExterior Q)
      (bivectorExterior_injective Q)).trans
    (LinearEquiv.ofEq _ _ (quadraticLieSubalgebra_toSubmodule_eq_range Q).symm)

/-- The quadratic element underlying the exterior-square equivalence is the Clifford bivector
map. -/
@[simp]
theorem coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply
    (x : ⋀[R]^2 M) :
    ((bivectorExteriorEquivQuadraticLieSubalgebra Q x : quadraticLieSubalgebra Q) :
      CliffordAlgebra Q) = bivectorExterior Q x := by
  rw [bivectorExteriorEquivQuadraticLieSubalgebra, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

/-- The exterior-algebra element underlying the inverse equivalence is the exterior model of the
quadratic Clifford element. -/
@[simp]
theorem coe_bivectorExteriorEquivQuadraticLieSubalgebra_symm_apply
    (x : quadraticLieSubalgebra Q) :
    (((bivectorExteriorEquivQuadraticLieSubalgebra Q).symm x : ⋀[R]^2 M) :
      ExteriorAlgebra R M) = equivExterior Q x := by
  rw [← equivExterior_bivectorExterior Q,
    ← coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply,
    LinearEquiv.apply_symm_apply]

/-- The Lie ring structure on the second exterior power transported from the quadratic elements
through `bivectorExteriorEquivQuadraticLieSubalgebra`. It is explicit in `Q` because the
exterior square alone does not determine the quadratic form. -/
@[instance_reducible]
noncomputable def bivectorLieRing :
    LieRing (⋀[R]^2 M) :=
  (bivectorExteriorEquivQuadraticLieSubalgebra Q).toAddEquiv.lieRing

/-- The Lie algebra structure on the second exterior power transported from the quadratic
elements. It is explicit in `Q` for the same reason as `bivectorLieRing`. -/
@[instance_reducible]
noncomputable def bivectorLieAlgebra :
    letI := bivectorLieRing Q
    LieAlgebra R (⋀[R]^2 M) :=
  (bivectorExteriorEquivQuadraticLieSubalgebra Q).lieAlgebra

/-- The transported Lie equivalence between the second exterior power and the quadratic
elements. -/
noncomputable def bivectorLieEquiv :
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    ⋀[R]^2 M ≃ₗ⁅R⁆ quadraticLieSubalgebra Q :=
  (bivectorExteriorEquivQuadraticLieSubalgebra Q).lieEquiv R

/-- The transported Lie equivalence has the same forward map as the exterior-square linear
equivalence. -/
@[simp]
theorem bivectorLieEquiv_apply (x : ⋀[R]^2 M) :
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    bivectorLieEquiv Q x =
      bivectorExteriorEquivQuadraticLieSubalgebra Q x := by
  rw [bivectorLieEquiv]
  exact LinearEquiv.lieEquiv_apply _ x

/-- The inverse transported Lie equivalence has the same map as the inverse exterior-square
linear equivalence. -/
@[simp]
theorem bivectorLieEquiv_symm_apply (x : quadraticLieSubalgebra Q) :
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    (bivectorLieEquiv Q).symm x =
      (bivectorExteriorEquivQuadraticLieSubalgebra Q).symm x := by
  rw [bivectorLieEquiv]
  exact LinearEquiv.lieEquiv_symm_apply _ x

end CliffordAlgebra
