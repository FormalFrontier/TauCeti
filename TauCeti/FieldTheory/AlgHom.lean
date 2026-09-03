/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Algebra homomorphisms between finite-dimensional fields

This file contains a dimension criterion for promoting an algebra homomorphism between fields to
an algebra equivalence.
-/

public section

namespace TauCeti

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional K M]

/-- An algebra homomorphism between finite-dimensional field extensions of equal finrank promotes
to an algebra equivalence. -/
noncomputable def algEquivOfFinrankEq (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) : L ≃ₐ[K] M :=
  AlgEquiv.ofBijective f
    ⟨f.injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
        (f := f.toLinearMap)).mp f.injective⟩

@[simp]
theorem algEquivOfFinrankEq_apply (f : L →ₐ[K] M)
    (hfin : Module.finrank K L = Module.finrank K M) (x : L) :
    algEquivOfFinrankEq f hfin x = f x :=
  AlgEquiv.ofBijective_apply f _ x

end TauCeti
