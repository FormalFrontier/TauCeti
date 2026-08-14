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

namespace AbstractSimplicialComplex

/-- A face of a set-like collection of finite sets, bundled with its membership proof. -/
abbrev Face {ι S : Type*} [SetLike S (Finset ι)] (K : S) := {σ : Finset ι // σ ∈ K}

/-- A finite set is a face of the underlying precomplex exactly when it is a face of the abstract
simplicial complex itself. This is the single place where the two `SetLike` instances are
identified. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex {ι : Type*} {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} : σ ∈ K.toPreAbstractSimplicialComplex ↔ σ ∈ K :=
  Iff.rfl

end AbstractSimplicialComplex

namespace TauCeti.AbstractSimplicialComplex

/-- The order on bundled faces is inclusion of their underlying finite sets. -/
theorem face_le_iff {ι S : Type*} [SetLike S (Finset ι)] {K : S}
    {σ τ : _root_.AbstractSimplicialComplex.Face K} :
    σ ≤ τ ↔ (σ : Finset ι) ⊆ τ :=
  Iff.rfl

/-- A finite set belongs to the full abstract simplicial complex exactly when it is nonempty. -/
theorem mem_top_iff {ι : Type*} {σ : Finset ι} :
    σ ∈ (⊤ : _root_.AbstractSimplicialComplex ι) ↔ σ.Nonempty :=
  Iff.rfl

end TauCeti.AbstractSimplicialComplex
