/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# Closed immersions of diagonalizable group schemes

A surjective homomorphism of finitely generated commutative character groups induces a
surjective map of their group algebras. Relative spectrum reverses this map, so the resulting
morphism of diagonalizable group schemes is a closed immersion.

## Main declarations

* `TauCeti.DiagonalizableGroup.isClosedImmersion_groupSchemeMap_of_surjective`: the
  contravariant diagonalizable-group image of a surjective character-group homomorphism is a
  closed immersion.
-/

public section

open CategoryTheory
open AlgebraicGeometry

namespace TauCeti

universe u

namespace DiagonalizableGroup

variable (R : Type u) [CommRing R]

/-- A surjective homomorphism of character groups induces a closed immersion of the associated
diagonalizable group schemes. -/
theorem isClosedImmersion_groupSchemeMap_of_surjective {G H : FGCommGrpCat.{u}} (φ : G ⟶ H)
    (hφ : Function.Surjective (FGCommGrpCat.toMonoidHom φ)) :
    IsClosedImmersion (groupSchemeMap R φ).hom.hom.left := by
  let e₁ := (eqToHom (groupScheme_def R H)).hom.hom.left
  let e₂ := (eqToHom (groupScheme_def R G).symm).hom.hom.left
  let c := ((hopfSpec (CommRingCat.of R)).map (coordinateMap R φ).hom.op).hom.hom.left
  have he₁ : IsIso e₁ :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (groupScheme_def R H)))).isIso_hom
  have he₂ : IsIso e₂ :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (groupScheme_def R G).symm))).isIso_hom
  have hc : IsClosedImmersion c :=
    (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff _).2
      (coordinateMap_surjective_of_surjective R φ hφ)
  have hc₂ : IsClosedImmersion (c ≫ e₂) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ c e₂ he₂).2 hc
  have he₁c₂ : IsClosedImmersion (e₁ ≫ (c ≫ e₂)) :=
    (@MorphismProperty.cancel_left_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ e₁ (c ≫ e₂) he₁).2 hc₂
  rw [groupSchemeMap_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact he₁c₂

end DiagonalizableGroup

end TauCeti
