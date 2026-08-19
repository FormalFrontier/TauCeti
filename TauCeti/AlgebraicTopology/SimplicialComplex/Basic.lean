/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Basic abstract simplicial complex API

This file contains general-purpose lemmas supplementing Mathlib's basic abstract simplicial
complex API.

Faces are bundled by `TauCeti.SetLike.Face`, stated for an arbitrary set-like collection of
finite sets so that the same type describes the faces of an `AbstractSimplicialComplex` and of a
`PreAbstractSimplicialComplex`; hence its neutral namespace.
-/

public section

namespace TauCeti.SetLike

/-- A face of a set-like collection of finite sets, bundled with its membership proof. -/
abbrev Face {ι S : Type*} [_root_.SetLike S (Finset ι)] (K : S) := {σ : Finset ι // σ ∈ K}

/-- The order on bundled faces is inclusion of their underlying finite sets. -/
theorem face_le_iff {ι S : Type*} [_root_.SetLike S (Finset ι)] {K : S} {σ τ : Face K} :
    σ ≤ τ ↔ (σ : Finset ι) ⊆ τ :=
  Iff.rfl

end TauCeti.SetLike

namespace AbstractSimplicialComplex

/-- A finite set is a face of the underlying precomplex exactly when it is a face of the abstract
simplicial complex itself. This is the single place where the two `SetLike` instances are
identified. -/
@[simp]
theorem mem_toPreAbstractSimplicialComplex {ι : Type*} {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} : σ ∈ K.toPreAbstractSimplicialComplex ↔ σ ∈ K :=
  Iff.rfl

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- A finite set is a face of an intersection of two precomplexes exactly when it is a face of
both. -/
@[simp]
theorem mem_inf {ρ : Finset ι} : ρ ∈ K ⊓ L ↔ ρ ∈ K ∧ ρ ∈ L :=
  Iff.rfl

/-- Every vertex of a face spans a singleton face. -/
theorem singleton_mem_of_mem (hσ : σ ∈ K) (hv : v ∈ σ) : ({v} : Finset ι) ∈ K :=
  (K.isRelLowerSet_faces hσ).2 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

/-- A vertex whose singleton is not a face occurs in no face at all.  This is the convenient way
to say that a vertex is *unused* by a complex, as needed when a construction adjoins a fresh
vertex. -/
theorem notMem_of_singleton_notMem (hv : ({v} : Finset ι) ∉ K) (hσ : σ ∈ K) : v ∉ σ :=
  fun h => hv (singleton_mem_of_mem hσ h)

end PreAbstractSimplicialComplex

namespace TauCeti.AbstractSimplicialComplex

/-- A finite set belongs to the full abstract simplicial complex exactly when it is nonempty. -/
theorem mem_top_iff {ι : Type*} {σ : Finset ι} :
    σ ∈ (⊤ : _root_.AbstractSimplicialComplex ι) ↔ σ.Nonempty :=
  Iff.rfl

end TauCeti.AbstractSimplicialComplex
