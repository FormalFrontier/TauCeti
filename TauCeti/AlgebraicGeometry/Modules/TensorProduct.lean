/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# The tensor product of `𝒪ₓ`-modules on a scheme

The site-level sheafified tensor product of sheaves of modules
(`TauCeti/Algebra/Category/ModuleCat/Sheaf/TensorProduct.lean`) specializes to a scheme
`X` by taking the sheaf of commutative rings to be the structure sheaf of `X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.tensorProduct` is the tensor product of two
  `𝒪ₓ`-modules on a scheme; its congruence, unit, and symmetry isomorphisms are the
  site-level ones of `TauCeti.SheafOfModules`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible
sheaves on a scheme; the Picard group `Pic X` under `⊗`": the tensor product is the
operation from which the Picard group will be built.
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe v

noncomputable section

variable (X : Scheme.{v})

/-- The tensor product of two `𝒪ₓ`-modules, obtained from the site-level sheafified tensor
product of `TauCeti.SheafOfModules` by taking the sheaf of commutative rings to be the
structure sheaf of `X`. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct
    (M N : X.Modules) : X.Modules :=
  SheafOfModules.tensorProduct X.sheaf M N

end

end TauCeti
