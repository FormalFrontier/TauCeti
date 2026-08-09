/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Algebra.Lie.TransferInstance
public import TauCeti.LinearAlgebra.CliffordAlgebra.QuadraticLieSubalgebra

/-!
# The exterior-square model of quadratic Clifford elements

The half-normalized Clifford bivector map identifies the second exterior power with the canonical
Lie subalgebra of quadratic elements in the Clifford algebra. Transporting its Lie structure
equips the exterior square with the corresponding commutator bracket.

This is a generic prerequisite for identifying bivectors with the orthogonal Lie algebra in the
spin representations roadmap. It does not construct that orthogonal Lie equivalence.

## Main results

* `TauCeti.CliffordAlgebra.cliffordBivectorExteriorEquivQuadraticLieSubalgebra`: the exterior
  square is linearly equivalent to the quadratic Lie subalgebra.
* `TauCeti.CliffordAlgebra.cliffordBivectorLieRing` and
  `TauCeti.CliffordAlgebra.cliffordBivectorLieAlgebra`: the Lie structures transported to the
  exterior square.
* `TauCeti.CliffordAlgebra.cliffordBivectorLieEquiv`: the transported Lie equivalence with the
  quadratic Lie subalgebra.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

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

/-- The exterior-algebra element underlying the inverse equivalence is the exterior model of the
quadratic Clifford element. -/
@[simp]
theorem coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_symm_apply
    (Q : QuadraticForm R M) [Invertible (2 : R)] (x : quadraticLieSubalgebra Q) :
    (((cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).symm x : ⋀[R]^2 M) :
      ExteriorAlgebra R M) = equivExterior Q x := by
  rw [← equivExterior_cliffordBivectorExterior Q,
    ← coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_apply,
    LinearEquiv.apply_symm_apply]

/-- The Lie ring structure on the second exterior power transported from the quadratic elements
through `cliffordBivectorExteriorEquivQuadraticLieSubalgebra`. It is explicit in `Q` because the
exterior square alone does not determine the quadratic form. -/
@[instance_reducible]
noncomputable def cliffordBivectorLieRing (Q : QuadraticForm R M) [Invertible (2 : R)] :
    LieRing (⋀[R]^2 M) :=
  (cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).toAddEquiv.lieRing

/-- The Lie algebra structure on the second exterior power transported from the quadratic
elements. It is explicit in `Q` for the same reason as `cliffordBivectorLieRing`. -/
@[instance_reducible]
noncomputable def cliffordBivectorLieAlgebra (Q : QuadraticForm R M) [Invertible (2 : R)] :
    letI := cliffordBivectorLieRing Q
    LieAlgebra R (⋀[R]^2 M) :=
  (cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).lieAlgebra

/-- The transported Lie equivalence between the second exterior power and the quadratic
elements. -/
noncomputable def cliffordBivectorLieEquiv (Q : QuadraticForm R M) [Invertible (2 : R)] :
    letI := cliffordBivectorLieRing Q
    letI := cliffordBivectorLieAlgebra Q
    ⋀[R]^2 M ≃ₗ⁅R⁆ quadraticLieSubalgebra Q :=
  (cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).lieEquiv R

/-- The transported Lie equivalence has the same forward map as the exterior-square linear
equivalence. -/
@[simp]
theorem cliffordBivectorLieEquiv_apply (Q : QuadraticForm R M) [Invertible (2 : R)]
    (x : ⋀[R]^2 M) :
    letI := cliffordBivectorLieRing Q
    letI := cliffordBivectorLieAlgebra Q
    cliffordBivectorLieEquiv Q x =
      cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q x := by
  rw [cliffordBivectorLieEquiv]
  exact LinearEquiv.lieEquiv_apply _ x

/-- The inverse transported Lie equivalence has the same map as the inverse exterior-square
linear equivalence. -/
@[simp]
theorem cliffordBivectorLieEquiv_symm_apply (Q : QuadraticForm R M) [Invertible (2 : R)]
    (x : quadraticLieSubalgebra Q) :
    letI := cliffordBivectorLieRing Q
    letI := cliffordBivectorLieAlgebra Q
    (cliffordBivectorLieEquiv Q).symm x =
      (cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).symm x := by
  rw [cliffordBivectorLieEquiv]
  exact LinearEquiv.lieEquiv_symm_apply _ x

end CliffordAlgebra

end TauCeti
