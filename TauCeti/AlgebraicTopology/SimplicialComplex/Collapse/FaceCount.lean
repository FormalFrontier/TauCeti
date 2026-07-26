/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic
public import Mathlib.Data.Set.Card

/-!
# Face counts under simplicial collapse

An elementary simplicial collapse removes exactly its free face and unique coface.  This file
turns that description into cardinality control: every elementary collapse removes two faces,
while an arbitrary collapse can only decrease the face cardinality.  For finite complexes this
also gives subtraction, strictness, and parity results for natural-valued face counts.

These facts are basic bookkeeping for the collapse track in layer 11 of the geometric-topology
roadmap.  In particular, they provide a termination measure for finite collapse arguments and
the parity obstruction that any proposed collapse certificate must satisfy.  The definitions of
free pairs and collapse are those in `ElementaryCollapse` and `Collapse.Basic`, following
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3.

## Main results

* `ElementaryCollapsesTo.encard_faces_add_two`: the face counts before and after an elementary
  collapse differ by two.
* `CollapsesTo.encard_faces_le`: an arbitrary collapse can only decrease the face cardinality.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*}
  {K L : _root_.PreAbstractSimplicialComplex ι}

namespace ElementaryCollapsesTo

/-- An elementary collapse removes exactly two faces. -/
theorem encard_faces_add_two (h : ElementaryCollapsesTo K L) :
    L.faces.encard + 2 = K.faces.encard := by
  obtain ⟨σ, τ, hfree, hστ, hmem⟩ := h.exists_pair
  have hpair : ({σ, τ} : Set (Finset ι)) ⊆ K.faces := by
    rw [Set.pair_subset_iff]
    exact ⟨hfree.lower_mem, hfree.upper_mem⟩
  have hfaces : L.faces = K.faces \ {σ, τ} := by
    ext ω
    -- `faces` is the set-valued view of a complex, so this exposes its definitional membership
    -- before rewriting membership in the pair as two inequalities.
    change (ω ∈ L ↔ ω ∈ K ∧ ω ∉ ({σ, τ} : Set (Finset ι)))
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hmem ω
  rw [hfaces]
  calc
    (K.faces \ {σ, τ}).encard + 2 =
        (K.faces \ {σ, τ}).encard + ({σ, τ} : Set (Finset ι)).encard := by
          rw [Set.encard_pair hστ.ne]
    _ = K.faces.encard := Set.encard_sdiff_add_encard_of_subset hpair

/-- An elementary collapse of a finite complex removes exactly two faces. -/
theorem ncard_faces_add_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces + 2 = Set.ncard K.faces := by
  have hL : L.faces.Finite := hK.subset h.le
  rw [← ENat.coe_inj]
  simpa only [← hK.cast_ncard_eq, ← hL.cast_ncard_eq, Nat.cast_add, Nat.cast_ofNat] using
    h.encard_faces_add_two

/-- The face count after an elementary collapse is the original face count minus two. -/
theorem ncard_faces_eq_sub_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces = Set.ncard K.faces - 2 := by
  have hcount := h.ncard_faces_add_two hK
  omega

/-- An elementary collapse strictly decreases the number of faces of a finite complex. -/
theorem ncard_faces_lt (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces < Set.ncard K.faces := by
  have hcount := h.ncard_faces_add_two hK
  omega

/-- An elementary collapse preserves the parity of the number of faces. -/
theorem ncard_faces_mod_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces % 2 = Set.ncard K.faces % 2 := by
  have hcount := h.ncard_faces_add_two hK
  omega

end ElementaryCollapsesTo

namespace CollapsesTo

/-- A collapse can only decrease the face cardinality. -/
theorem encard_faces_le (h : CollapsesTo K L) : L.faces.encard ≤ K.faces.encard :=
  Set.encard_mono h.le

/-- A collapse of a finite complex can only decrease its number of faces. -/
theorem ncard_faces_le (h : CollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces ≤ Set.ncard K.faces :=
  Set.ncard_le_ncard h.le hK

/-- A collapse of a finite complex preserves the parity of its number of faces. -/
theorem ncard_faces_mod_two (h : CollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces % 2 = Set.ncard K.faces % 2 := by
  exact (h.property_of_elementaryCollapsesTo
    (p := fun M => M.faces.Finite ∧ Set.ncard M.faces % 2 = Set.ncard K.faces % 2)
    (fun {_ _} hAB ⟨hA, hparity⟩ =>
      ⟨hA.subset hAB.le, (hAB.ncard_faces_mod_two hA).trans hparity⟩)
    ⟨hK, rfl⟩).2

end CollapsesTo

end PreAbstractSimplicialComplex

end TauCeti
