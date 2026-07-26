/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Basic abstract simplicial complex API

This file contains general-purpose lemmas supplementing Mathlib's basic abstract simplicial
complex API.
-/

public section

namespace TauCeti

namespace AbstractSimplicialComplex

/-- A face of an abstract simplicial complex, bundled with its membership proof. -/
abbrev Face {ι : Type*} (K : AbstractSimplicialComplex ι) := {σ : Finset ι // σ ∈ K}

/-- A finite set is a face of the underlying precomplex exactly when it is a face of the abstract
simplicial complex itself. This is the single place where the two `SetLike` instances are
identified. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex {ι : Type*} {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} : σ ∈ K.toPreAbstractSimplicialComplex ↔ σ ∈ K :=
  Iff.rfl

end AbstractSimplicialComplex

end TauCeti
