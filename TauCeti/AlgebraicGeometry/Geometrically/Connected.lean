/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness of affine products

This file proves that the spectrum of a tensor product of commutative algebras over a field is
geometrically connected when the spectra of both factors are geometrically connected. The tensor
product spectrum is identified with the fibre product of the two spectra over the ground field.

## Main declarations

* `TauCeti.geometricallyConnected_tensorProduct`: the tensor product of two commutative algebras
  with geometrically connected spectra is geometrically connected.

This is an affine-scheme prerequisite for the product constructions in Layer 5, "The unipotent
radical", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

private instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable {k : Type u} [Field k]

/-- The spectrum of a tensor product of commutative algebras over a field is geometrically
connected when the spectra of both factors are geometrically connected over that field. -/
theorem geometricallyConnected_tensorProduct
    (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    (hS : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (hT : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k T)))) :
    GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (S ⊗[k] T)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k S))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k T))
  let _ : GeometricallyConnected f := hS
  let _ : GeometricallyConnected g := hT
  let _ : UniversallyOpen f := inferInstance
  let _ : UniversallyOpen g := inferInstance
  have hproduct : GeometricallyConnected (pullback.fst f g ≫ f) :=
    GeometricallyConnected.comp (pullback.fst f g) f
  have hproduct' : GeometricallyConnected
      ((pullbackSpecIso k S T).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (S ⊗[k] T)))) := by
    rw [pullbackSpecIso_hom_base]
    exact hproduct
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) (pullbackSpecIso k S T).hom] at hproduct'
  exact hproduct'

end TauCeti
