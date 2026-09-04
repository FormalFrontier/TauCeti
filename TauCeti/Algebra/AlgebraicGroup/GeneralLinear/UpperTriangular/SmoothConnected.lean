/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

/-!
# Geometry of the upper-triangular subgroup scheme

The standard upper-triangular subgroup of `GL_n` is the weight parabolic for the strictly
decreasing weights `i ↦ n - 1 - i`. This file specializes the general geometry of
injective-weight parabolics to establish smoothness and geometric connectedness of the
upper-triangular group over every field.

## Main declarations

* `TauCeti.GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is smooth.
* `TauCeti.GeneralLinear.UpperTriangular.
    geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This advances the Borel-subgroup milestone in Layer 7, "Structure theory", of the
ReductiveGroups roadmap: together with the existing solvability theorem, it supplies the smooth
connected solvable standard subgroup that will be shown maximal among such subgroups.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

namespace UpperTriangular

variable (n : ℕ)

/-- **The standard upper-triangular subgroup of `GL_n` is smooth over every field.** -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    k (weights n) (weights_injective n)

/-- **The standard upper-triangular subgroup of `GL_n` is geometrically connected over every
field.** -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  geometricallyConnectedCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    k (weights n) (weights_injective n)

end UpperTriangular

end

end TauCeti.GeneralLinear
