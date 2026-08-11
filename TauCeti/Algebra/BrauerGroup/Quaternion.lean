/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.BrauerGroup.BaseChange
import TauCeti.Algebra.CentralSimple.Quaternion

/-!
# The Brauer class of the real quaternions

This file applies the general Brauer-group API to the real quaternions. Quaternion conjugation
identifies `ℍ[ℝ]` with its opposite algebra, so its Brauer class is self-inverse and has order
dividing `2`; and complexification kills that class, in the two ways
`TauCeti/Algebra/BrauerGroup/BaseChange.lean` offers.

These are the Brauer-group computations in the Hamilton-quaternion worked example of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
-/

public section

open scoped Quaternion

namespace TauCeti

/-! ### Worked examples -/

/-- **The Brauer class of the real quaternions is its own inverse.** Quaternion conjugation is an
`ℝ`-algebra isomorphism `ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (Mathlib's `Quaternion.starAe`), so this is
`TauCeti.BrauerGroup.inv_mk_eq_mk_of_algEquiv_op`; concretely it is the isomorphism
`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₄(ℝ)` of `TauCeti.Quaternion.tensorSelfAlgEquivMatrix`. -/
example : (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]))⁻¹ = BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) :=
  BrauerGroup.inv_mk_eq_mk_of_algEquiv_op _root_.Quaternion.starAe

/-- **The Brauer class of the real quaternions has order dividing `2`.** That the order is exactly
`2` -- so that `[ℍ[ℝ]]` generates a copy of `ℤ/2` inside `BrauerGroup ℝ` -- needs the class to be
nontrivial, which the nonsplitting of `ℍ[ℝ]` does not yet give here. -/
example : orderOf (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])) ∣ 2 :=
  BrauerGroup.orderOf_mk_dvd_two_of_algEquiv_op _root_.Quaternion.starAe

/-- **Complexification kills the Brauer class of the real quaternions**, because `ℂ` is
algebraically closed and so has trivial Brauer group.

That this is a *nontrivial* class being killed -- that `ℍ[ℝ]` is not already split over `ℝ`, so
that the kernel of `TauCeti.BrauerGroup.baseChange ℝ ℂ` is bigger than `1` -- is the same missing
step as in the previous example: it needs the uniqueness half of Artin-Wedderburn, as does the
expectation `BrauerGroup ℝ ≃ ℤ/2`. -/
example : BrauerGroup.baseChange ℝ ℂ (BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])) = 1 := by
  rw [BrauerGroup.baseChange_eq_one_of_isAlgClosed, MonoidHom.one_apply]

/-- The same class, killed through the splitting field rather than through the triviality of
`BrauerGroup ℂ`: `TauCeti.Algebra.isSplittingField_of_isAlgClosed` says `ℂ` splits every
finite-dimensional central simple `ℝ`-algebra, and a split algebra lies in the kernel. -/
example : BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) ∈ (BrauerGroup.baseChange ℝ ℂ).ker :=
  BrauerGroup.mk_mem_ker_baseChange_of_isSplittingField ℝ ℂ
    (Algebra.isSplittingField_of_isAlgClosed ℝ ℍ[ℝ] ℂ)

end TauCeti
