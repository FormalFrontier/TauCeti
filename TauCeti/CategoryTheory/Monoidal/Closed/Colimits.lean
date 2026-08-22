/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Tensoring in a monoidal closed category preserves colimits

In a monoidal closed category the functor `X ⊗ -` is a left adjoint, so it preserves all
colimits; in a braided one the same then holds for `- ⊗ X`.  Mathlib has the adjunction
`MonoidalClosed.ihom.adjunction` and the natural isomorphism
`BraidedCategory.tensorLeftIsoTensorRight`, but records neither consequence as an instance.

They are needed to build monoidal structures by totalization: `HomologicalComplex.monoidalCategory`
asks that tensoring commute with the coproducts indexed by the pairs of degrees summing to a fixed
degree, and without the instances below that hypothesis is not discharged for a category as
ordinary as `ModuleCat R`.  In particular they are what makes `CochainComplex (ModuleCat R) ℤ`
monoidal, as required by `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "complete the
symmetric monoidal structure on unbounded `CochainComplex (ModuleCat k) ℤ`".
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

universe w w' v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- In a monoidal closed category, `X ⊗ -` is a left adjoint, hence preserves all colimits. -/
instance preservesColimitsOfSize_tensorLeft (X : C) :
    PreservesColimitsOfSize.{w, w'} (tensorLeft X) :=
  (ihom.adjunction X).leftAdjoint_preservesColimits

/-- In a braided monoidal closed category, `- ⊗ X` preserves all colimits, being isomorphic to
`X ⊗ -`. -/
instance preservesColimitsOfSize_tensorRight [BraidedCategory C] (X : C) :
    PreservesColimitsOfSize.{w, w'} (tensorRight X) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

end TauCeti
