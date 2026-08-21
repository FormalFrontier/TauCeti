/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Sets.Opens

/-!
# Carrying a basis from families of sets to families of opens

A basis of a topological space is presented in two ways in Mathlib, and neither is canonical:
`TopologicalSpace.IsTopologicalBasis` takes a `Set (Set X)`, while `TopologicalSpace.Opens.IsBasis`
takes a `Set (Opens X)`. This file bridges the first form to the second, for consumers stated in
terms of `Opens` — the sheaf-theoretic ones, since `Opens X` is the category a presheaf on `X` is
indexed by.

## Main results

* `TauCeti.TopologicalSpace.Opens.isBasis_of_isTopologicalBasis` : a basis presented as a family
  of sets yields one presented as a family of `Opens`.
-/

namespace TauCeti

open _root_.TopologicalSpace

public section

universe u

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X]

/-- **A basis of sets is a basis of opens.** A basis presented as a `Set (Set X)`, the form
`TopologicalSpace.IsTopologicalBasis` takes, yields one presented as a `Set (Opens X)`, the form
`Opens.IsBasis` takes: keep the opens whose underlying set is a member. Nothing is lost, since
every member of a topological basis is open.

Both presentations occur in Mathlib and each has its own API, so this is a bridge between two
existing forms rather than a claim that either is the standard one. -/
theorem isBasis_of_isTopologicalBasis {S : Set (Set X)} (hS : IsTopologicalBasis S) :
    Opens.IsBasis {U : Opens X | (U : Set X) ∈ S} := by
  have himg : ((↑) : Opens X → Set X) '' {U : Opens X | (U : Set X) ∈ S} = S := by
    ext V
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact hU
    · exact fun hV ↦ ⟨⟨V, hS.isOpen hV⟩, hV, rfl⟩
  rw [Opens.IsBasis, himg]
  exact hS

end TopologicalSpace.Opens

end

end TauCeti
