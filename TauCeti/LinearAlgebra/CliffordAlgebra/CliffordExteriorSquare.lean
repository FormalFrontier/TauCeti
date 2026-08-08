/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.QuadraticLieSubalgebra

/-!
# The exterior-square model of quadratic Clifford elements

The half-normalized Clifford bivector map identifies the second exterior power with the canonical
Lie subalgebra of quadratic elements in the Clifford algebra.

This is a generic prerequisite for transporting the Clifford commutator to the exterior square in
the spin representations roadmap. It does not define the transported bracket or identify it with
an orthogonal Lie algebra.

## Main results

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
theorem coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_symm_apply
    (Q : QuadraticForm R M) [Invertible (2 : R)] (x : quadraticLieSubalgebra Q) :
    (((cliffordBivectorExteriorEquivQuadraticLieSubalgebra Q).symm x : ⋀[R]^2 M) :
      ExteriorAlgebra R M) = equivExterior Q x := by
  rw [← equivExterior_cliffordBivectorExterior Q,
    ← coe_cliffordBivectorExteriorEquivQuadraticLieSubalgebra_apply,
    LinearEquiv.apply_symm_apply]

end CliffordAlgebra

end TauCeti
