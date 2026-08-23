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

Elementary facts about a prefunctor `φ : Q ⥤q R` which `Prefunctor.mapPath` and `Prefunctor.comp`
leave unrecorded: pushing a path along `φ` preserves its length, a prefunctor with a two-sided
inverse is bijective on vertices, and a pair of composable one-sided inverse pairs composes to a
one-sided inverse pair.

## Main results

* `Prefunctor.length_mapPath`: pushing a path along a prefunctor preserves its length.
* `Prefunctor.obj_bijective_of_comp_eq_id`: mutually inverse prefunctors are bijective on vertices.
* `Prefunctor.comp_comp_comp_eq_id`: composing two one-sided inverse pairs of prefunctors gives a
  one-sided inverse pair.

## References

They all feed `TauCeti.PathAlgebra.mapAlgHom` in
`TauCeti/RepresentationTheory/Quiver/PathAlgebra/Map.lean`, whose uniform hypothesis is
bijectivity on vertices, and the transport of the zigzag relations in
`TauCeti/RepresentationTheory/Quiver/Zigzag/Isomorphism.lean`, which is stated in terms of path
lengths.
-/

namespace TauCeti

universe u u' u'' v v' v''

variable {Q : Type u} {R : Type u'} {S : Type u''} [Quiver.{v} Q] [Quiver.{v'} R] [Quiver.{v''} S]

/-- **Pushing a path along a prefunctor preserves its length**: the image path traverses the image
of each arrow of the original, in order. -/
@[simp]
theorem _root_.Prefunctor.length_mapPath (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    (φ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih,
      Quiver.Path.length_cons]

/-- **Mutually inverse prefunctors are bijective on vertices.** -/
theorem _root_.Prefunctor.obj_bijective_of_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q)
    (hφψ : φ.comp ψ = Prefunctor.id Q) (hψφ : ψ.comp φ = Prefunctor.id R) :
    Function.Bijective φ.obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ψ.obj, fun a ↦ congrArg (fun F : Q ⥤q Q ↦ F.obj a) hφψ,
      fun b ↦ congrArg (fun F : R ⥤q R ↦ F.obj b) hψφ⟩

/-- **One-sided inverse pairs of prefunctors compose**: if `ψ` is a right inverse of `φ` and `ψ'`
one of `φ'`, then `ψ' ⋙q ψ` is a right inverse of `φ ⋙q φ'`. Applying this to a mutually inverse
pair in each order gives both inverse laws for the composite pair. -/
theorem _root_.Prefunctor.comp_comp_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q) (φ' : R ⥤q S)
    (ψ' : S ⥤q R) (hφψ : φ.comp ψ = Prefunctor.id Q) (hφψ' : φ'.comp ψ' = Prefunctor.id R) :
    (φ.comp φ').comp (ψ'.comp ψ) = Prefunctor.id Q := by
  rw [Prefunctor.comp_assoc, ← Prefunctor.comp_assoc φ' ψ' ψ, hφψ', Prefunctor.id_comp, hφψ]

end TauCeti
