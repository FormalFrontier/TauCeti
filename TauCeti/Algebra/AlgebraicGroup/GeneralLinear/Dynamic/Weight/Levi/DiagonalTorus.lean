/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Basic

/-!
# Injective-weight Levis and the diagonal torus

For a weight `w : Fin N → ℤ`, the weight Levi consists of the invertible matrices whose
`(i,j)` entry vanishes when `w i ≠ w j`. If `w` is injective, these are precisely the diagonal
matrices. This file identifies the corresponding coordinate Hopf algebra with that of the
diagonal split torus.

## Main declarations

* `TauCeti.GeneralLinear.weightLeviDiagonalCoordinateIso`: the coordinate Hopf algebra of an
  injective-weight Levi is that of the diagonal split torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This advances the dynamic approach to parabolics and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

private theorem weightLeviDefiningHopfIdeal_le_ker_diagonalTorusCoordinateMap
    (w : Fin N → ℤ) :
    (weightLeviDefiningHopfIdeal R w).toIdeal ≤
      RingHom.ker
        (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.toRingHom := by
  rw [weightLeviDefiningHopfIdeal_def, HopfIdeal.sup_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal]
  apply sup_le
  · rw [Ideal.span_le]
    intro x hx
    rw [mem_weightParabolicRelationSet_iff] at hx
    obtain ⟨i, j, hij, rfl⟩ := hx
    rw [SetLike.mem_coe, RingHom.mem_ker]
    -- The kernel API exposes the underlying `RingHom`; the coordinate API uses the bundled map.
    change (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (coordinateHopfAlgebraAlgEquiv R N
        (coordinateRingMap R N (MvPolynomial.X (i, j)))) = 0
    have hne : i ≠ j := fun h ↦ hij.ne (congrArg w h)
    simpa only [hne, ↓reduceIte] using
      diagonalTorusCoordinateMap_X (R := R) (N := N) i j
  · rw [Ideal.span_le]
    intro x hx
    rw [mem_weightParabolicRelationSet_iff] at hx
    obtain ⟨i, j, hij, rfl⟩ := hx
    rw [SetLike.mem_coe, RingHom.mem_ker]
    -- The kernel API exposes the underlying `RingHom`; the coordinate API uses the bundled map.
    change (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (coordinateHopfAlgebraAlgEquiv R N
        (coordinateRingMap R N (MvPolynomial.X (i, j)))) = 0
    have hne : i ≠ j := fun h ↦ hij.ne (congrArg (-w) h)
    simpa only [hne, ↓reduceIte] using
      diagonalTorusCoordinateMap_X (R := R) (N := N) i j

/-- Restriction from a weight Levi to the diagonal torus. The construction exists for every
weight because diagonal matrices preserve every weight space. -/
private noncomputable def weightLeviDiagonalCoordinateMap (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w ⟶
      CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) :=
  CommHopfAlgCat.liftQuotient (weightLeviDefiningHopfIdeal R w)
    (diagonalTorusCoordinateMap (R := R) (N := N))
    (weightLeviDefiningHopfIdeal_le_ker_diagonalTorusCoordinateMap R w)

@[simp]
private theorem weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateMap
    (w : Fin N → ℤ) :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) ≫
      weightLeviDiagonalCoordinateMap R w =
        diagonalTorusCoordinateMap (R := R) (N := N) := by
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

private theorem mapPointsFunctor_weightLeviDiagonalCoordinateMap_app
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points
      (R := R)
      (H := CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))) A) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) A
        ((CommHopfAlgCat.mapPointsFunctor
          (weightLeviDiagonalCoordinateMap R w)).app A f) =
      diagonalTorusPoints f := by
  -- `quotientPointsHom` and `mapPointsFunctor` use definitionally equal presentations of the
  -- quotient point type, but no theorem rewrites across the residual `GrpCat` wrapper.
  change (CommHopfAlgCat.mapPointsFunctor
      (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w))).app A
      ((CommHopfAlgCat.mapPointsFunctor
        (weightLeviDiagonalCoordinateMap R w)).app A f) = _
  rw [← CommHopfAlgCat.mapPointsFunctor_comp_app_apply,
    weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateMap]
  exact mapPointsFunctor_diagonalTorusCoordinateMap_app A f

private theorem bijective_mapPointsFunctor_weightLeviDiagonalCoordinateMap_app
    (w : Fin N → ℤ) (hw : Function.Injective w) (A : CommAlgCat.{u} R) :
    Function.Bijective
      ((CommHopfAlgCat.mapPointsFunctor
        (weightLeviDiagonalCoordinateMap R w)).app A) := by
  constructor
  · intro f g hfg
    apply diagonalTorusPoints_injective
    rw [← mapPointsFunctor_weightLeviDiagonalCoordinateMap_app R w A f,
      ← mapPointsFunctor_weightLeviDiagonalCoordinateMap_app R w A g, hfg]
  · intro g
    let gGL := CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) A g
    have hgGL : gGL ∈ CommHopfAlgCat.quotientPointsSubgroup
        (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w) A :=
      CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
        (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w) A g
    have hdiag : (pointsMulEquiv N gGL : Matrix (Fin N) (Fin N) A).IsDiag := by
      intro i j hij
      exact (mem_weightLeviDefiningPointsSubgroup_iff_apply_eq_zero R w gGL).mp hgGL
        i j (hw.ne hij)
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (mem_diagonalTorus_iff.mpr hdiag)
    let f : HopfAlgebra.points
        (R := R)
        (H := CommHopfAlgCat.of R
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))) A :=
      (SplitTorus.pointsMulEquiv (R := R) (A := A)).symm (fun i ↦ d i.down)
    have hfGL : diagonalTorusPoints f = gGL := by
      apply (pointsMulEquiv (R := R) (A := A) N).injective
      rw [pointsMulEquiv_diagonalTorusPoints]
      calc
        diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f)) =
            diagGL d := by
          congr 1
          funext i
          simpa only [diagonalTorusCoordinates_apply, ULift.up_down] using
            congrFun ((SplitTorus.pointsMulEquiv (R := R) (A := A)).apply_symm_apply
              (fun i : ULift.{u} (Fin N) ↦ d i.down)) (ULift.up i)
        _ = pointsMulEquiv N gGL := hd
    refine ⟨f, ?_⟩
    apply CommHopfAlgCat.quotientPointsHom_injective
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w) A
    rw [mapPointsFunctor_weightLeviDiagonalCoordinateMap_app R w, hfGL]

private theorem isIso_mapPointsFunctor_weightLeviDiagonalCoordinateMap
    (w : Fin N → ℤ) (hw : Function.Injective w) :
    IsIso (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (weightLeviDiagonalCoordinateMap R w)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact bijective_mapPointsFunctor_weightLeviDiagonalCoordinateMap_app R w hw A

/-- The coordinate Hopf algebra of an injective-weight Levi is the coordinate ring of the
diagonal split torus. -/
noncomputable def weightLeviDiagonalCoordinateIso
    (w : Fin N → ℤ) (hw : Function.Injective w) :
    weightLeviCoordinateHopfAlgebra R w ≅
      CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) := by
  let f := weightLeviDiagonalCoordinateMap R w
  let _ : IsIso (CommHopfAlgCat.mapPointsFunctor.{u, u, u} f) := by
    dsimp only [f]
    exact isIso_mapPointsFunctor_weightLeviDiagonalCoordinateMap R w hw
  let _ : IsIso f := CommHopfAlgCat.isIso_of_isIso_mapPointsFunctor f
  exact asIso f

/-- The injective-weight Levi coordinate isomorphism restricts the ambient general-linear
coordinate map to the diagonal-torus coordinate map. -/
@[simp]
theorem weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateIso_hom
    (w : Fin N → ℤ) (hw : Function.Injective w) :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) ≫
      (weightLeviDiagonalCoordinateIso R w hw).hom =
        diagonalTorusCoordinateMap (R := R) (N := N) := by
  -- Expose the isomorphism's defining morphism inside its characteristic API theorem.
  change CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) ≫
    weightLeviDiagonalCoordinateMap R w = _
  exact weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateMap R w

end

end TauCeti.GeneralLinear
