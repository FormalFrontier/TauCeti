/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of the double-coset quotient

A double coset `HgK` is a union of left cosets of `K`, so the double cosets `H \ G / K` are a
quotient of `G ⧸ K`: the map `gK ↦ HgK` is well defined and surjective
(`TauCeti.doubleCosetMk_out_mk` is the well-definedness, in the form the surjection uses).
Consequently `H \ G / K` is finite as soon as `K` has finite index, with no finiteness assumption
on `G` itself.

This is the instance that lets a sum be taken over `H \ G / K`; the Mackey decomposition
(`TauCeti.RepresentationTheory.Induction.Mackey.Basic`) is its first consumer, where the index of
the subgroup being induced from is the only finiteness available.

## Main statements

* `TauCeti.finite_doubleCosetQuotient`: `H \ G / K` is finite when `K` has finite index in `G`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- Replacing an element by the chosen representative of its left `K`-coset does not change its
double coset. -/
theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (Quotient.out (QuotientGroup.mk g : G ⧸ K)) = DoubleCoset.mk H K g := by
  have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g))
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, _, hmem, by simp⟩

/-- **The double cosets `H \ G / K` are finite when `K` has finite index**: they are the image of
the finite set `G ⧸ K` under `gK ↦ HgK`. -/
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' H K d)⟩

end TauCeti
