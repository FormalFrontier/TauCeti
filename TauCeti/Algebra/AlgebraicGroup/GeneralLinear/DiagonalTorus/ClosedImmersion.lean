/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.GeneralLinear
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

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

* `TauCeti.GeneralLinear.diagonalTorus_eq_diagonalGroupSchemeHom`: the diagonal torus is the
  diagonalizable-group representation with the standard character weights.
* `TauCeti.GeneralLinear.isClosedImmersion_diagonalTorus`: the diagonal torus morphism is a
  closed immersion.
* `TauCeti.GeneralLinear.diagonalTorusClosedSubgroup`: the diagonal torus as a closed subgroup
  scheme of `GL_n`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.

This advances the split maximal-torus and root-datum target in Layer 7 of the ReductiveGroups
roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R : Type u) [CommRing R] (N : ℕ)

/-- The coordinate morphism of the diagonal torus is the coordinate morphism of the standard
diagonal representation of its character group. -/
private theorem diagonalTorusCoordinateMap_eq_diagonalCoordinateMap :
    diagonalTorusCoordinateMap (R := R) (N := N) =
      CommHopfAlgCat.ofHom
        (DiagonalizableGroup.diagonalCoordinateMap (Pi.basisFun R (Fin N)) fun i =>
          SplitTorus.weightCharacter
            (Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i))) := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply coordinateHopfAlgebra_bialgHom_ext R N
  intro i j
  rw [diagonalTorusCoordinateMap_X]
  -- Expose the underlying algebra map hidden by `CommHopfAlgCat.ofHom` so that the
  -- diagonal-coordinate formula can rewrite the right-hand side.
  change _ = DiagonalizableGroup.diagonalCoordinateMap (Pi.basisFun R (Fin N))
    (fun i => SplitTorus.weightCharacter
      (Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i))) _
  rw [DiagonalizableGroup.diagonalCoordinateMap_X]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.diagonal_apply_eq]
    simp only [↓reduceIte]
    congr 2
    apply Multiplicative.toAdd.injective
    ext x
    rw [SplitTorus.toAdd_weightCharacter]
    simp [Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  · simp [hij, Matrix.diagonal_apply_ne]

/-- The diagonal torus is the general diagonalizable-group representation specialized to the
standard basis of its character lattice. -/
theorem diagonalTorus_eq_diagonalGroupSchemeHom :
    diagonalTorus (R := R) (N := N) =
      DiagonalizableGroup.diagonalGroupSchemeHom
        (SplitTorus.characterGroup (ULift.{u} (Fin N))) (Pi.basisFun R (Fin N)) fun i =>
          SplitTorus.weightCharacter
            (Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)) := by
  rw [diagonalTorus_def, DiagonalizableGroup.diagonalGroupSchemeHom_def]
  rw [diagonalTorusCoordinateMap_eq_diagonalCoordinateMap]

/-- **The diagonal split torus is a closed subgroup scheme of `GL_n` over every commutative
base ring.** -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus (R := R) (N := N)).hom.hom.left := by
  rw [diagonalTorus_eq_diagonalGroupSchemeHom]
  apply DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom
  let wt : Fin N → ULift.{u} (Fin N) → ℤ := fun i =>
    Pi.basisFun ℤ (ULift.{u} (Fin N)) (ULift.up i)
  have hrange : Set.range wt = Set.range (Pi.basisFun ℤ (ULift.{u} (Fin N))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ULift.up i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, congrArg (Pi.basisFun ℤ (ULift.{u} (Fin N))) i.up_down.symm⟩
  have hspan : Submodule.span ℤ (Set.range wt) = ⊤ := by
    rw [hrange, (Pi.basisFun ℤ (ULift.{u} (Fin N))).span_eq]
  exact SplitTorus.closure_range_weightCharacter_eq_top wt hspan

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
