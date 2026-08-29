/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

/-!
# The diagonal torus in the upper-triangular group

The standard diagonal torus of `GLₙ` factors through its upper-triangular subgroup scheme. In
Hopf coordinates, the diagonal-torus morphism kills every generic matrix coordinate strictly
below the diagonal, so it descends uniquely through the quotient defining the upper-triangular
group. Applying relative spectrum gives the inclusion `T → B`, whose composite with `B → GLₙ`
is the standard diagonal torus.

This supplies the containment of the standard maximal torus in the standard Borel candidate for
the general-rank `GLₙ` example in Layer 7 of the ReductiveGroups roadmap. It supersedes the
rank-two-only construction formerly in `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel`.

## Main declarations

* `TauCeti.GeneralLinear.UpperTriangular.diagonalTorusCoordinateMap`: the coordinate morphism
  from the upper-triangular coordinate algebra to the diagonal-torus coordinate algebra.
* `TauCeti.GeneralLinear.UpperTriangular.diagonalTorus`: the diagonal torus as a group-scheme
  morphism into the upper-triangular group.
* `TauCeti.GeneralLinear.UpperTriangular.diagonalTorus_comp_inclusion`: the factorization recovers
  the standard diagonal torus in `GLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 12 and 21.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Sections 6.2 and 8.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.UpperTriangular

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Every diagonal-torus point belongs to the upper-triangular subgroup. -/
theorem diagonalTorusPoints_mem
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[R] A)) :
    GeneralLinear.diagonalTorusPoints (R := R) (N := n) f ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) := by
  rw [mem_definingPointsSubgroup_iff,
    GeneralLinear.pointsMulEquiv_diagonalTorusPoints, UpperTriangularGroup.mem_iff]
  intro i j hji
  rw [diagGL_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

end Points

section DiagonalTorus

/-- The coordinate morphism of the diagonal torus factored through the upper-triangular
coordinate algebra. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R n ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R n)
    (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := n)) (by
      rw [definingHopfIdeal_toIdeal, Ideal.span_le]
      intro x hx
      rw [mem_definingRelationSet_iff] at hx
      obtain ⟨i, j, hji, rfl⟩ := hx
      rw [SetLike.mem_coe, RingHom.mem_ker]
      -- `RingHom.mem_ker` displays the bundled morphism through two underlying-map coercions;
      -- restate it in the `BialgHom` form used by the coordinate computation lemma.
      change (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := n)).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) = 0
      have hij : i ≠ j := ne_of_gt hji
      simpa only [hij, ↓reduceIte] using
        GeneralLinear.diagonalTorusCoordinateMap_X (R := R) (N := n) i j)

/-- Precomposing the factored diagonal-torus coordinate morphism with the upper-triangular
quotient map recovers the ambient diagonal-torus coordinate morphism. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R n ≫ diagonalTorusCoordinateMap R n =
      GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := n) := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The standard diagonal torus as a morphism into the upper-triangular subgroup scheme. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin n)) ⟶ groupScheme R n :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin n)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap R n).op ≫
    eqToHom (groupScheme_def R n).symm

/-- The diagonal torus into the upper-triangular group is relative spectrum applied
contravariantly to its factored coordinate morphism. -/
theorem diagonalTorus_def :
    diagonalTorus R n =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin n)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap R n).op ≫
        eqToHom (groupScheme_def R n).symm :=
  (rfl)

/-- Composing the diagonal torus inside the upper-triangular subgroup with its inclusion into
`GLₙ` gives the standard diagonal torus of `GLₙ`. -/
@[simp]
theorem diagonalTorus_comp_inclusion :
    diagonalTorus R n ≫ inclusion R n =
      GeneralLinear.diagonalTorus (R := R) (N := n) := by
  rw [diagonalTorus_def, inclusion, GeneralLinear.diagonalTorus_def,
    GeneralLinear.weightParabolicInclusion_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  have hmap :
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap R n).op ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
            (definingHopfIdeal R n)).op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := n)).op := by
    rw [← Functor.map_comp, ← op_comp, ← coordinateMap_def R n,
      coordinateMap_comp_diagonalTorusCoordinateMap]
  congr 1
  rw [← Category.assoc, hmap]
  rfl

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Under the upper-triangular and general-linear point equivalences, the factored coordinate
morphism gives the same diagonal matrix as the ambient diagonal-torus morphism. -/
@[simp]
theorem pointsMulEquiv_diagonalTorusCoordinateMap
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[R] A)) :
    ((pointsMulEquiv (R := R) (n := n) (A := A)
        (WithConv.toConv (f.ofConv.comp (diagonalTorusCoordinateMap R n).hom)) :
      upperTriangularGroup (Fin n) A) : GL (Fin n) A) =
      GeneralLinear.pointsMulEquiv n
        (GeneralLinear.diagonalTorusPoints (R := R) (N := n) f) := by
  have hcoe := pointsMulEquiv_coe (R := R) (n := n) (A := A)
    (WithConv.toConv (f.ofConv.comp (diagonalTorusCoordinateMap R n).hom))
  rw [← hcoe, GeneralLinear.pointsMulEquiv_apply]
  congr 1
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  rw [WithConv.ofConv_toConv, AlgHom.comp_assoc, ← coordinateMap_def R n,
    ← BialgHom.comp_toAlgHom, ← CommHopfAlgCat.hom_comp,
    coordinateMap_comp_diagonalTorusCoordinateMap]
  have hmap := GeneralLinear.mapPointsFunctor_diagonalTorusCoordinateMap_app
    (R := R) (N := n) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hmap
  exact hmap

end DiagonalTorus

end TauCeti.GeneralLinear.UpperTriangular
