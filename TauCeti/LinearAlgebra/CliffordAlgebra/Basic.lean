/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Basic Clifford algebra API

This file records general scalar properties of a Clifford algebra obtained from Mathlib's
linear equivalence with the exterior algebra.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti.CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- `CliffordAlgebra.equivExterior` sends a scalar to the corresponding scalar of the exterior
algebra. -/
theorem equivExterior_algebraMap (Q : QuadraticForm R M) [Invertible (2 : R)] (r : R) :
    equivExterior Q (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (ExteriorAlgebra R M) r :=
  changeForm_algebraMap changeForm.associated_neg_proof r

/-- **The scalars of a Clifford algebra are a faithful copy of `R`.** -/
theorem algebraMap_injective (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s hrs
  have h := congrArg (equivExterior Q) hrs
  rwa [equivExterior_algebraMap, equivExterior_algebraMap,
    ExteriorAlgebra.algebraMap_inj M] at h

/-- The scalar action on a Clifford algebra is faithful when `2` is invertible. With this
instance, Mathlib's scalar `iff` lemmas apply directly. -/
instance faithfulSMul (Q : QuadraticForm R M) [Invertible (2 : R)] :
    FaithfulSMul R (CliffordAlgebra Q) :=
  (faithfulSMul_iff_algebraMap_injective R (CliffordAlgebra Q)).2 (algebraMap_injective Q)

end TauCeti.CliffordAlgebra
