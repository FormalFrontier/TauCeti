/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The affine fppf site

For a commutative ring `R`, this file equips `(CommAlgCat R)ᵒᵖ` with the topology induced by
Mathlib's fppf topology on schemes over `Spec R`. This is the category of affine schemes over
`Spec R`, presented contravariantly through their coordinate algebras.

The induced affine topology is subcanonical. The proof restricts each representable presheaf on
schemes over `Spec R` along the fully faithful relative spectrum functor and identifies the result
with the corresponding affine representable presheaf.

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

/-- Relative spectrum is continuous from the affine fppf site to the fppf site of schemes over
the base. -/
instance algSpec_isContinuous_fppfTopology (R : Type u) [CommRing R] :
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).IsContinuous
      (fppfTopology R)
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) := by
  unfold fppfTopology
  infer_instance

/-- **The affine fppf topology is subcanonical.** Every presheaf represented by an affine scheme
over `Spec R` is an fppf sheaf. -/
noncomputable instance fppfTopology_subcanonical (R : Type u) [CommRing R] :
    (fppfTopology R).Subcanonical := by
  let K := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let _ : K.Subcanonical := by
    dsimp only [K]
    infer_instance
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  let P := yoneda.obj
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj X)
  have hP : Presieve.IsSheaf K P :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P
  let S : Sheaf K (Type u) :=
    ⟨P, (isSheaf_iff_isSheaf_of_type K P).mpr hP⟩
  have hpull' : Presieve.IsSheaf (fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    Functor.op_comp_isSheaf_of_types
      (AlgebraicGeometry.algSpec (CommRingCat.of R)) (fppfTopology R) K S
  have hpull : Presheaf.IsSheaf (fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr hpull'
  let e : yoneda.obj X ≅
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P :=
    NatIso.ofComponents
      (fun _ =>
        (AlgebraicGeometry.algSpec.fullyFaithful
          (R := CommRingCat.of R)).homEquiv.toIso)
      (by
        intro Y Z f
        ext g
        exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).map_comp f.unop g)
  exact (isSheaf_iff_isSheaf_of_type _ _).mp <|
    (Presheaf.isSheaf_of_iso_iff e).mpr hpull

end CommAlgCat

end TauCeti
