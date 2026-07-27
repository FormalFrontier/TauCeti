/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Representations of a quiver

A representation of a quiver over a field assigns a vector space to every vertex and a linear map
to every arrow, compatibly with path composition. This is precisely a functor from Mathlib's free
path category to its category of modules.

This file introduces only the standard abbreviation. The equivalence with modules over the path
algebra is developed separately.

## References

This implements the category-of-representations part of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

/-- The category of representations of a quiver `Q` over a field `k`. -/
abbrev QuiverRep (k : Type u) (Q : Type v) [Field k] [Quiver Q] :=
  Paths Q ⥤ ModuleCat k

end TauCeti
