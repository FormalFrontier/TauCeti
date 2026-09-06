/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Numbering the roots of a polynomial

This file relates an explicit numbering of a polynomial's root set to its multiset of roots.

## Main results

* `Polynomial.Separable.roots_map_eq_map_numbering`: for a separable polynomial, a numbering of
  its root set enumerates its full root multiset after base change.

The numbering lemma lets root-product formulas be expressed as finite products indexed by
`Fin f.natDegree`, without choosing a global order on the root set.
-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- A numbering of the root set of a separable polynomial enumerates the whole root multiset:
separability makes the roots simple, so the multiset is the image of the numbering. -/
theorem _root_.Polynomial.Separable.roots_map_eq_map_numbering (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    (f.map (algebraMap F E)).roots = Multiset.map (fun i ↦ ((e i : E))) univ.val := by
  have hmem : ∀ {a : E}, a ∈ (f.map (algebraMap F E)).roots ↔ a ∈ f.rootSet E := fun {_} ↦
    Polynomial.mem_aroots'.trans Polynomial.mem_rootSet'.symm
  refine (Multiset.Nodup.ext (nodup_roots hsep.map) ?_).mpr ?_
  · exact univ.nodup.map fun i j h ↦ e.injective (Subtype.ext h)
  · intro a
    simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and]
    exact ⟨fun ha ↦ ⟨e.symm ⟨a, hmem.mp ha⟩, by simp⟩, fun ⟨i, hi⟩ ↦ hi ▸ hmem.mpr (e i).2⟩

end TauCeti
