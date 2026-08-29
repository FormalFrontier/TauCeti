/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus

/-!
# The diagonal torus as a closed subgroup of the general linear group

The diagonal morphism from the rank-`n` split torus to `GL_n` is a closed immersion over every
commutative base ring. This file packages its image as a closed subgroup scheme.

The proof identifies the diagonal morphism with the general diagonal representation whose
weights are the standard basis of the character lattice. Those weights span, so the general
closed-immersion criterion for diagonalizable-group representations applies. This avoids a
second coordinate-by-coordinate proof that the restriction map on coordinate rings is
surjective.

The resulting closed subgroup is the torus in the split root datum of `GL_n`. Proving that it is
maximal among tori is a separate geometric step in Layer 7 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.GeneralLinear.diagonalTorus_eq_weightTorus`: the diagonal torus is the weight torus
  for the standard basis of its character lattice.
* `TauCeti.GeneralLinear.diagonalTorus_eq_diagonalGroupSchemeHom`: its equivalent description as
  a diagonalizable-group representation.
* `TauCeti.GeneralLinear.diagonalTorusCoordinateMap_surjective`: the restriction map from the
  coordinate ring of `GL_n` onto that of the diagonal torus is surjective.
* `TauCeti.GeneralLinear.isClosedImmersion_diagonalTorus`: the diagonal torus morphism is a
  closed immersion.
* `TauCeti.GeneralLinear.diagonalTorusClosedSubgroup`: the diagonal torus as a closed subgroup
  scheme of `GL_n`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
* `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Torus` and
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus`, whose
  weight-torus closedness constructions supplied the internal template.
* `TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.GeneralLinear`, in particular
  `DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom`.

This advances the split maximal-torus and root-datum target in Layer 7 of the ReductiveGroups
roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R] (N : ℕ)

/-- The coordinate morphism of the diagonal torus is the weight-torus coordinate morphism for the
standard basis of its character lattice. -/
private theorem diagonalTorusCoordinateMap_eq_weightTorusCoordinateMap :
    diagonalTorusCoordinateMap (R := R) (N := N) =
      weightTorusCoordinateMap (R := R) (fun i =>
        Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)) := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply coordinateHopfAlgebra_bialgHom_ext R N
  intro i j
  rw [diagonalTorusCoordinateMap_X, hom_weightTorusCoordinateMap,
    weightTorusCoordinateBialgHom_X]
  rcases eq_or_ne i j with rfl | hij
  · have hweight :
        Finsupp.equivFunOnFinite.symm
            (Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)) =
          Finsupp.single (ULift.up i) 1 := by
      ext k
      simp [Pi.basisFun_apply, Finsupp.single_apply, eq_comm]
    rw [hweight]
  · simp [hij]

/-- The diagonal torus is the weight torus prescribed by the standard basis of its character
lattice. -/
theorem diagonalTorus_eq_weightTorus :
    diagonalTorus (R := R) (N := N) =
      weightTorus (R := R) (fun i =>
        Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)) := by
  rw [diagonalTorus_def, weightTorus_def,
    diagonalTorusCoordinateMap_eq_weightTorusCoordinateMap]

/-- The diagonal torus is the general diagonalizable-group representation specialized to the
standard basis of its character lattice. -/
theorem diagonalTorus_eq_diagonalGroupSchemeHom :
    diagonalTorus (R := R) (N := N) =
      DiagonalizableGroup.diagonalGroupSchemeHom
        (SplitTorus.characterGroup (ULift.{u} (Fin N))) (Pi.basisFun R (Fin N)) fun i =>
          SplitTorus.weightCharacter
            (Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)) := by
  rw [diagonalTorus_eq_weightTorus, weightTorus_eq_diagonalGroupSchemeHom]

/-- The coordinate morphism restricting functions on `GL_n` to the diagonal torus is
surjective. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap (R := R) (N := N)).hom := by
  rw [diagonalTorusCoordinateMap_eq_weightTorusCoordinateMap]
  apply weightTorusCoordinateMap_surjective
  rw [Set.range_comp', ULift.up_surjective.range_eq, Set.image_univ,
    (Pi.basisFun ℤ (ULift.{u} (Fin N))).span_eq]

/-- **The diagonal split torus is a closed subgroup scheme of `GL_n` over every commutative
base ring.** -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus (R := R) (N := N)).hom.hom.left := by
  rw [diagonalTorus_eq_weightTorus]
  apply isClosedImmersion_weightTorus
  rw [Set.range_comp', ULift.up_surjective.range_eq, Set.image_univ,
    (Pi.basisFun ℤ (ULift.{u} (Fin N))).span_eq]

/-- The diagonal split torus as a closed subgroup scheme of `GL_n`. -/
noncomputable def diagonalTorusClosedSubgroup :
    ClosedSubgroupScheme (groupScheme R N) :=
  ClosedSubgroupScheme.mk (diagonalTorus (R := R) (N := N))

/-- The underlying subobject of the closed diagonal torus is represented by the diagonal torus
morphism. -/
@[simp]
theorem coe_diagonalTorusClosedSubgroup :
    (diagonalTorusClosedSubgroup R N).1 =
      Subobject.mk (diagonalTorus (R := R) (N := N)) := by
  rw [diagonalTorusClosedSubgroup]
  exact ClosedSubgroupScheme.coe_mk _

end TauCeti.GeneralLinear
