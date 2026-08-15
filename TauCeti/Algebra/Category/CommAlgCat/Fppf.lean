/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The affine fppf site

For a commutative ring `R`, this file equips `(CommAlgCat R)ᵒᵖ` with the topology induced by
Mathlib's fppf topology on schemes over `Spec R`. This is the category of affine schemes over
`Spec R`, presented contravariantly through their coordinate algebras.

The induced affine topology is subcanonical by full faithfulness of the relative spectrum functor.

## Main declarations

* `TauCeti.CommAlgCat.fppfTopology`: the fppf topology on opposite commutative `R`-algebras.
* `TauCeti.CommAlgCat.fppfTopology_subcanonical`: affine representable functors are fppf sheaves.

This advances the cross-cutting sheaves-and-descent prerequisite in the ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

namespace CommAlgCat

/-- The fppf topology on affine schemes over `Spec R`, expressed on the equivalent category
`(CommAlgCat R)ᵒᵖ`.

It is the topology induced along the relative spectrum functor from the fppf topology on schemes
over `Spec R`. -/
noncomputable def fppfTopology (R : Type u) [CommRing R] :
    GrothendieckTopology (CommAlgCat.{u} R)ᵒᵖ :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).inducedTopology
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

/-- The affine fppf topology is induced from the fppf topology on schemes over `Spec R`. -/
theorem fppfTopology_def (R : Type u) [CommRing R] :
    fppfTopology R =
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).inducedTopology
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) :=
  by
    unfold fppfTopology
    rfl

/-- **The affine fppf topology is subcanonical.** Every presheaf represented by an affine scheme
over `Spec R` is an fppf sheaf. -/
noncomputable instance fppfTopology_subcanonical (R : Type u) [CommRing R] :
    (fppfTopology R).Subcanonical := by
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Full :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Faithful :=
    (AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fppfTopology_def]
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (AlgebraicGeometry.algSpec (CommRingCat.of R)) _
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

end CommAlgCat

end TauCeti
