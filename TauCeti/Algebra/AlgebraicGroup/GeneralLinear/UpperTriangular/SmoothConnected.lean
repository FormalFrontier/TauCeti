/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Geometry
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Geometry of the upper-triangular subgroup scheme

The standard upper-triangular subgroup of `GL_n` is the weight parabolic for the strictly
decreasing weights `i ↦ n - 1 - i`.  Its weight Levi is therefore the diagonal split torus.
This file proves that identification over an arbitrary commutative base ring and combines it
with the represented weight-parabolic Levi decomposition

```text
U(w) ⋊ L(w) ≅ P(w)
```

to establish the two basic geometric properties of the upper-triangular group: smoothness over
every field and geometric connectedness.

## Main declarations

* `TauCeti.GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is smooth.
* `TauCeti.GeneralLinear.UpperTriangular.
    geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This advances the Borel-subgroup milestone in Layer 7, "Structure theory", of the
ReductiveGroups roadmap: together with the existing solvability theorem, it supplies the smooth
connected solvable standard subgroup that will be shown maximal among such subgroups.
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
    change (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (coordinateHopfAlgebraAlgEquiv R N
        (coordinateRingMap R N (MvPolynomial.X (i, j)))) = 0
    have hne : i ≠ j := fun h ↦ hij.ne (congrArg (-w) h)
    simpa only [hne, ↓reduceIte] using
      diagonalTorusCoordinateMap_X (R := R) (N := N) i j

/-- Restriction from a weight Levi to the diagonal torus.  When the weights are injective this
is an isomorphism; the construction itself exists for every weight because diagonal matrices
preserve every weight space. -/
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
  rcases A with ⟨A⟩
  constructor
  · intro f g hfg
    change HopfAlgebra.points
      (R := R)
      (H := CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
      (CommAlgCat.of R A) at f g
    apply diagonalTorusPoints_injective
    rw [← mapPointsFunctor_weightLeviDiagonalCoordinateMap_app
        R w (CommAlgCat.of R A) f,
      ← mapPointsFunctor_weightLeviDiagonalCoordinateMap_app
        R w (CommAlgCat.of R A) g, hfg]
  · intro g
    change HopfAlgebra.points
      (R := R) (H := weightLeviCoordinateHopfAlgebra R w)
        (CommAlgCat.of R A) at g
    let gGL := CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) g
    have hgGL : gGL ∈ CommHopfAlgCat.quotientPointsSubgroup
        (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
        (CommAlgCat.of R A) :=
      CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
        (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
          (CommAlgCat.of R A) g
    have hdiag : (pointsMulEquiv N gGL : Matrix (Fin N) (Fin N) A).IsDiag := by
      intro i j hij
      exact (mem_weightLeviDefiningPointsSubgroup_iff_apply_eq_zero R w gGL).mp hgGL
        i j (hw.ne hij)
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (mem_diagonalTorus_iff.mpr hdiag)
    let f : HopfAlgebra.points
        (R := R)
        (H := CommHopfAlgCat.of R
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
        (CommAlgCat.of R A) :=
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
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
        (CommAlgCat.of R A)
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
private noncomputable def weightLeviDiagonalCoordinateIso
    (w : Fin N → ℤ) (hw : Function.Injective w) :
    weightLeviCoordinateHopfAlgebra R w ≅
      CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) := by
  let f := weightLeviDiagonalCoordinateMap R w
  let _ : IsIso ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map f.op) := by
    rw [CommHopfAlgCat.pointsFunctor_map, Quiver.Hom.unop_op]
    dsimp only [f]
    exact isIso_mapPointsFunctor_weightLeviDiagonalCoordinateMap R w hw
  let _ : IsIso f.op :=
    (Functor.FullyFaithful.ofFullyFaithful
      (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R))).isIso_of_isIso_map f.op
  let _ : IsIso f := isIso_of_op f
  exact asIso f

private theorem smooth_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    smoothCommHopfAlgProperty k (weightLeviCoordinateHopfAlgebra k w) := by
  apply (smoothCommHopfAlgProperty k).prop_of_iso
    (weightLeviDiagonalCoordinateIso k w hw).symm
  let H := DiagonalizableGroup.coordinateRing k
    (SplitTorus.characterGroup (ULift.{u} (Fin N)))
  exact torusCommHopfAlgProperty.smooth k H
    ((SplitTorus.splitTorus_coordinateRing k (ULift.{u} (Fin N))).torus)

private theorem geometricallyConnected_weightLeviCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    geometricallyConnectedCommHopfAlgProperty k (weightLeviCoordinateHopfAlgebra k w) := by
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (weightLeviDiagonalCoordinateIso k w hw).symm
  let H := DiagonalizableGroup.coordinateRing k
    (SplitTorus.characterGroup (ULift.{u} (Fin N)))
  exact torusCommHopfAlgProperty.geometricallyConnected k H
    ((SplitTorus.splitTorus_coordinateRing k (ULift.{u} (Fin N))).torus)

private theorem smooth_weightParabolicCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    smoothCommHopfAlgProperty k (weightParabolicCoordinateHopfAlgebra k w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra k w)
    (Dynamic.weightUnipotentInParabolicHopfIdeal k w)
    (Dynamic.weightLeviInParabolicHopfIdeal k w)
    (Dynamic.isNormal_weightUnipotentInParabolicHopfIdeal k w)
  apply (smoothCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso k w).symm
  apply (smoothCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductActionCoordinateIso k w).symm
  apply smoothCommHopfAlgProperty.semidirectProduct _ _ A
  · apply (smoothCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightUnipotentInParabolicCoordinateIso k w)
    rw [smoothCommHopfAlgProperty_iff]
    infer_instance
  · apply (smoothCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightLeviInParabolicCoordinateIso k w)
    exact smooth_weightLeviCoordinateHopfAlgebra k w hw

private theorem geometricallyConnected_weightParabolicCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) (hw : Function.Injective w) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightParabolicCoordinateHopfAlgebra k w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra k w)
    (Dynamic.weightUnipotentInParabolicHopfIdeal k w)
    (Dynamic.weightLeviInParabolicHopfIdeal k w)
    (Dynamic.isNormal_weightUnipotentInParabolicHopfIdeal k w)
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso k w).symm
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductActionCoordinateIso k w).symm
  apply geometricallyConnectedCommHopfAlgProperty.semidirectProduct _ _ A
  · apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightUnipotentInParabolicCoordinateIso k w)
    exact geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra k w
  · apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (Dynamic.weightLeviInParabolicCoordinateIso k w)
    exact geometricallyConnected_weightLeviCoordinateHopfAlgebra k w hw

namespace UpperTriangular

variable (n : ℕ)

private theorem weights_injective : Function.Injective (weights n) := by
  intro i j hij
  apply Fin.ext
  rw [weights_apply, weights_apply] at hij
  omega

/-- **The standard upper-triangular subgroup of `GL_n` is smooth over every field.** -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  smooth_weightParabolicCoordinateHopfAlgebra k (weights n) (weights_injective n)

/-- **The standard upper-triangular subgroup of `GL_n` is geometrically connected over every
field.** -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  geometricallyConnected_weightParabolicCoordinateHopfAlgebra
    k (weights n) (weights_injective n)

end UpperTriangular

end

end TauCeti.GeneralLinear
