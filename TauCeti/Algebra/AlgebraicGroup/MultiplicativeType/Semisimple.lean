/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic

/-!
# Semisimple points of groups of multiplicative type

A finite-type affine group over a field is of multiplicative type when its coordinate Hopf
algebra becomes diagonalizable after extension to an algebraic closure. Every point of a
diagonalizable group is semisimple, so the geometric fibre of a group of multiplicative type has
only semisimple geometric points.

This is the semisimple-point input for comparing groups of multiplicative type with unipotent
groups. In particular, a smooth unipotent closed subgroup of a torus becomes both semisimple and
unipotent on geometric points; reduced point separation will then force that subgroup to be
trivial.

## Main declarations

* `TauCeti.multiplicativeTypeCommHopfAlgProperty.geometricFiberSemisimplePoints`: the geometric
  fibre of a group of multiplicative type has only semisimple geometric points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 4, "Diagonalizable groups and groups of multiplicative type", and supplies a
prerequisite for the torus worked example in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The geometric fibre of a finite-type group of multiplicative type has only semisimple
geometric points. -/
@[grind →]
theorem multiplicativeTypeCommHopfAlgProperty.geometricFiberSemisimplePoints
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    geometricallySemisimplePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hH
  obtain ⟨G, ⟨i⟩⟩ := hH
  exact (geometricallySemisimplePointsCommHopfAlgProperty
    (AlgebraicClosure k)).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
        (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
      (DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty
        (AlgebraicClosure k) G)

end TauCeti
