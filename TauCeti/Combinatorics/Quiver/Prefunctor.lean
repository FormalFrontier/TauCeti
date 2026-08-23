/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path

public section

/-!
# Prefunctors on paths and on vertices

Two elementary facts about a prefunctor `φ : Q ⥤q R` which `Prefunctor.mapPath` and
`Prefunctor.comp` leave unrecorded: pushing a path along `φ` preserves its length, and a
prefunctor with a two-sided inverse prefunctor is bijective on vertices.

## Main results

* `Prefunctor.length_mapPath`: pushing a path along a prefunctor preserves its length.
* `Prefunctor.bijective_obj_of_comp_eq_id`: mutually inverse prefunctors are bijective on vertices.

## References

Both feed `TauCeti.PathAlgebra.mapAlgHom` in
`TauCeti/RepresentationTheory/Quiver/PathAlgebra/Map.lean`, whose hypothesis is exactly
bijectivity on vertices, and the transport of the zigzag relations in
`TauCeti/RepresentationTheory/Quiver/Zigzag/Isomorphism.lean`, which is stated in terms of path
lengths.
-/

namespace TauCeti

universe u u' v v'

variable {Q : Type u} {R : Type u'} [Quiver.{v} Q] [Quiver.{v'} R]

/-- **Pushing a path along a prefunctor preserves its length**: the image path traverses the image
of each arrow of the original, in order. -/
theorem _root_.Prefunctor.length_mapPath (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    (φ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih,
      Quiver.Path.length_cons]

/-- **Mutually inverse prefunctors are bijective on vertices.** -/
theorem _root_.Prefunctor.bijective_obj_of_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q)
    (hφψ : φ.comp ψ = Prefunctor.id Q) (hψφ : ψ.comp φ = Prefunctor.id R) :
    Function.Bijective φ.obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ψ.obj, fun a ↦ congrArg (fun F : Q ⥤q Q ↦ F.obj a) hφψ,
      fun b ↦ congrArg (fun F : R ⥤q R ↦ F.obj b) hψφ⟩

end TauCeti
