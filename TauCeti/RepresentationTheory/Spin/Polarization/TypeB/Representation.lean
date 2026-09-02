/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Basic

/-!
# The type-B spin representation of an odd polarization

`TauCeti.SpinPolarizationData.typeBQuadraticEquiv` identifies the split type-`B` matrix Lie
algebra `LieAlgebra.Orthogonal.typeB ι K` with the quadratic elements of the Clifford algebra of
an odd polarization, and those act on the spinor module `ExteriorAlgebra K P.W` through
`TauCeti.SpinPolarizationData.spinAction`. Composing the two gives the **spin representation** of
the type-`B` matrix algebra, which this file assembles and extends to the universal enveloping
algebra.

Only the composition is done here: what the numbered root and coroot generators do in this
representation is read off from their Clifford realizations in
`TauCeti/RepresentationTheory/Spin/Polarization/TypeB/RootGenerators.lean`, and the integrality
of that action is the subject of
`TauCeti/RepresentationTheory/Spin/Polarization/TypeB/KostantLattice.lean`. Nothing here is
specific to `ℚ`: any field in which `2` is invertible carries the same representation.

The enveloping-algebra extension is what the Chevalley--Demazure construction consumes, since
divided powers of root vectors and binomial coefficients in coroots live in the enveloping
algebra and not in the Lie algebra. This is a prerequisite of the full-weight simply connected
type-`B` carrier in Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`, whose consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.

## Main declarations

* `TauCeti.SpinPolarizationData.typeBSpinLieRep`: the spin representation of the split type-`B`
  matrix Lie algebra.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_apply`: its value on a matrix.
* `TauCeti.SpinPolarizationData.typeBSpinRep`: its extension to the universal enveloping algebra.
* `TauCeti.SpinPolarizationData.typeBSpinRep_ι`: the extension evaluated on a Lie generator.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
-/

public section

open CliffordAlgebra

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K P.W) (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- The type-`B` matrix Lie algebra acting on the spinor module through the quadratic Clifford
realization associated to an odd polarization. -/
noncomputable def typeBSpinLieRep :
    LieAlgebra.Orthogonal.typeB ι K →ₗ⁅K⁆ Module.End K (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toLieHom.comp <|
    (quadraticLieSubalgebra Q).incl.comp (P.typeBQuadraticEquiv b z hz).toLieHom

/-- The spin representation sends a type-`B` matrix to the spin action of its quadratic Clifford
realization. -/
@[simp]
theorem typeBSpinLieRep_apply (x : LieAlgebra.Orthogonal.typeB ι K) :
    P.typeBSpinLieRep b z hz x =
      spinAction Q P (P.typeBQuadraticEquiv b z hz x : CliffordAlgebra Q) := by
  rw [typeBSpinLieRep, LieHom.comp_apply, LieHom.comp_apply, LieSubalgebra.coe_incl,
    AlgHom.toLieHom_apply]
  rfl

/-- The type-`B` spin representation extended to the universal enveloping algebra. -/
noncomputable def typeBSpinRep :
    _root_.UniversalEnvelopingAlgebra K (LieAlgebra.Orthogonal.typeB ι K) →ₐ[K]
      Module.End K (ExteriorAlgebra K P.W) :=
  _root_.UniversalEnvelopingAlgebra.lift K (P.typeBSpinLieRep b z hz)

/-- A Lie generator acts in the enveloping-algebra representation through its quadratic
Clifford element. -/
@[simp]
theorem typeBSpinRep_ι (x : LieAlgebra.Orthogonal.typeB ι K) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom K
          (LieAlgebra.Orthogonal.typeB ι K) (TensorAlgebra.ι K x)) =
      spinAction Q P (P.typeBQuadraticEquiv b z hz x : CliffordAlgebra Q) := by
  rw [typeBSpinRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply',
    P.typeBSpinLieRep_apply b z hz]

end SpinPolarizationData

end TauCeti
