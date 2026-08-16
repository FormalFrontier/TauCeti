/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme

/-!
# Representations with upper-unitriangular coefficient matrices

Let `M` be a finite free comodule over a commutative Hopf algebra `H`. If the coefficient matrix
of `M` in a basis `b` is upper unitriangular, evaluation at its strict-upper entries defines a
coordinate Hopf-algebra morphism

```text
O(U_n) ⟶ H.
```

This morphism factors the usual coordinate morphism `O(GL_n) ⟶ H` through the quotient
`O(GL_n) ⟶ O(U_n)`. Consequently, if `M` is faithful, the represented affine group embeds as
a closed subgroup of `U_n`.

This is the coordinate-algebra bridge needed for the upper-unitriangular embedding
characterization in Layer 5, "Unipotent groups", of the ReductiveGroups roadmap. The remaining
Kolchin step must produce a basis with upper-unitriangular coefficient matrix for a faithful
representation of a unipotent group.

## Main declarations

* `TauCeti.Comodule.upperUnitriangularCoordinateBialgHom`: the coordinate morphism to an
  upper-unitriangular representation.
* `TauCeti.Comodule.upperUnitriangularCoordinateBialgHom_comp_coordinateMap`: its factorization of
  the general-linear coordinate morphism.
* `TauCeti.Comodule.upperUnitriangularGroupSchemeHom`: the corresponding group-scheme morphism.
* `TauCeti.Comodule.isClosedImmersion_upperUnitriangularGroupSchemeHom_of_isFaithful`: a faithful
  upper-unitriangular representation is a closed immersion into `U_n`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open CategoryTheory AlgebraicGeometry Module

universe u

noncomputable section

variable {R H M : Type u} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Evaluate the strict-upper coordinates of `O(U_n)` at the corresponding entries of the
coefficient matrix. The upper-unitriangular hypothesis is used below to prove this algebra map
respects the coalgebra structure. -/
private def upperUnitriangularCoordinateAlgHom (b : Basis (Fin n) R M) :
    UpperUnitriangular.coordinateHopfAlgebra R (Fin n) →ₐ[R] H :=
  (MvPolynomial.aeval fun ij : UpperUnitriangular.Index (Fin n) ↦
      coefficientMatrix (C := H) b ij.1.1 ij.1.2).comp
    (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)).symm.toAlgHom

private theorem upperUnitriangularCoordinateAlgHom_genericMatrix_apply
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (i j : Fin n) :
    upperUnitriangularCoordinateAlgHom (H := H) b
        (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)
          (UpperUnitriangular.genericMatrix R (Fin n) i j)) =
      coefficientMatrix (C := H) b i j := by
  rw [upperUnitriangularCoordinateAlgHom, AlgHom.comp_apply]
  calc
    _ = (MvPolynomial.aeval fun ij : UpperUnitriangular.Index (Fin n) ↦
          coefficientMatrix (C := H) b ij.1.1 ij.1.2)
        (UpperUnitriangular.genericMatrix R (Fin n) i j) :=
      congrArg _ ((UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)).symm_apply_apply _)
    _ = _ := congrFun
      (congrFun (UpperUnitriangular.map_aeval_genericMatrix R (Fin n) _ h) i) j

private theorem upperUnitriangularCoordinateAlgHom_X
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (ij : UpperUnitriangular.Index (Fin n)) :
    upperUnitriangularCoordinateAlgHom (H := H) b
        (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)
          (MvPolynomial.X ij)) =
      coefficientMatrix (C := H) b ij.1.1 ij.1.2 := by
  rw [← UpperUnitriangular.genericMatrix_apply_of_lt R (Fin n) ij.2]
  exact upperUnitriangularCoordinateAlgHom_genericMatrix_apply b h _ _

private theorem upperUnitriangularCoordinateAlgHom_counit
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (Bialgebra.counitAlgHom R H).comp
        (upperUnitriangularCoordinateAlgHom (H := H) b) =
      Bialgebra.counitAlgHom R
        (UpperUnitriangular.coordinateHopfAlgebra R (Fin n)) := by
  apply UpperUnitriangular.coordinateHopfAlgebra_algHom_ext R (Fin n)
  intro ij
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
    upperUnitriangularCoordinateAlgHom_X b h, counit_coefficientMatrix]
  simp [Bialgebra.counitAlgHom_apply, ij.2.ne]

private theorem upperUnitriangularCoordinateAlgHom_comul
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (Algebra.TensorProduct.map
        (upperUnitriangularCoordinateAlgHom (H := H) b)
        (upperUnitriangularCoordinateAlgHom (H := H) b)).comp
        (Bialgebra.comulAlgHom R
          (UpperUnitriangular.coordinateHopfAlgebra R (Fin n))) =
      (Bialgebra.comulAlgHom R H).comp
        (upperUnitriangularCoordinateAlgHom (H := H) b) := by
  apply UpperUnitriangular.coordinateHopfAlgebra_algHom_ext R (Fin n)
  intro ij
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    UpperUnitriangular.coordinateHopfAlgebra_comul_X, map_sum,
    Algebra.TensorProduct.map_tmul,
    upperUnitriangularCoordinateAlgHom_genericMatrix_apply b h,
    upperUnitriangularCoordinateAlgHom_X b h]
  exact (comul_coefficientMatrix_eq_sum (C := H) b ij.1.1 ij.1.2).symm

/-- The coordinate Hopf-algebra morphism of a comodule whose coefficient matrix is upper
unitriangular in the chosen basis. It sends each strict-upper coordinate of `U_n` to the
corresponding matrix coefficient. -/
def upperUnitriangularCoordinateBialgHom
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    UpperUnitriangular.coordinateHopfAlgebra R (Fin n) →ₐc[R] H :=
  BialgHom.ofAlgHom (upperUnitriangularCoordinateAlgHom b)
    (upperUnitriangularCoordinateAlgHom_counit b h)
    (upperUnitriangularCoordinateAlgHom_comul b h)

/-- The upper-unitriangular coordinate morphism sends every entry of the generic matrix to the
corresponding coefficient-matrix entry. -/
@[simp]
theorem upperUnitriangularCoordinateBialgHom_genericMatrix_apply
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (i j : Fin n) :
    upperUnitriangularCoordinateBialgHom (H := H) b h
        (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)
          (UpperUnitriangular.genericMatrix R (Fin n) i j)) =
      coefficientMatrix (C := H) b i j := by
  exact upperUnitriangularCoordinateAlgHom_genericMatrix_apply b h i j

/-- The coordinate morphism of an upper-unitriangular representation factors the ordinary
general-linear coordinate morphism through `O(U_n)`. -/
theorem upperUnitriangularCoordinateBialgHom_comp_coordinateMap
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (upperUnitriangularCoordinateBialgHom (H := H) b h).comp
        (UpperUnitriangular.coordinateMap R n).hom =
      coordinateBialgHom (H := H) b := by
  apply BialgHom.ext
  intro x
  have hAlg :
      ((upperUnitriangularCoordinateBialgHom (H := H) b h).comp
        (UpperUnitriangular.coordinateMap R n).hom).toAlgHom =
        (coordinateBialgHom (H := H) b).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    rw [BialgHom.comp_toAlgHom, AlgHom.comp_apply]
    calc
      _ = upperUnitriangularCoordinateBialgHom (H := H) b h
          (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin n)
            (UpperUnitriangular.genericMatrix R (Fin n) i j)) :=
        congrArg (upperUnitriangularCoordinateBialgHom (H := H) b h)
          (UpperUnitriangular.coordinateMap_genericMatrix_apply R n i j)
      _ = coefficientMatrix (C := H) b i j :=
        upperUnitriangularCoordinateBialgHom_genericMatrix_apply b h i j
      _ = _ := (coordinateBialgHom_X b i j).symm
  exact AlgHom.congr_fun hAlg x

/-- For an upper-unitriangular representation, faithfulness makes its coordinate morphism
`O(U_n) ⟶ H` surjective. -/
theorem upperUnitriangularCoordinateBialgHom_surjective_of_isFaithful
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hM : IsFaithful (k := R) (H := H) (V := M)) :
    Function.Surjective (upperUnitriangularCoordinateBialgHom (H := H) b h) := by
  have hb : IsClosedImmersion (coordinateGroupSchemeHom (H := H) b).hom.hom.left :=
    (isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mp hM
  have hsurj : Function.Surjective (coordinateBialgHom (H := H) b) :=
    (isClosedImmersion_coordinateGroupSchemeHom_iff b).mp hb
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  refine ⟨(UpperUnitriangular.coordinateMap R n).hom x, ?_⟩
  exact DFunLike.congr_fun
    (upperUnitriangularCoordinateBialgHom_comp_coordinateMap b h) x

/-- The morphism from the affine group represented by `H` to `U_n` associated to a basis in
which the coefficient matrix is upper unitriangular. -/
def upperUnitriangularGroupSchemeHom
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
      UpperUnitriangular.groupScheme R (Fin n) :=
  (hopfSpec (CommRingCat.of R)).map
      (CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom b h)).op ≫
    eqToHom (UpperUnitriangular.groupScheme_def R (Fin n)).symm

/-- The upper-unitriangular representation morphism is relative spectrum applied to its
coordinate morphism, followed by the defining identification of `U_n`. -/
theorem upperUnitriangularGroupSchemeHom_def
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    upperUnitriangularGroupSchemeHom (H := H) b h =
      (hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom b h)).op ≫
        eqToHom (UpperUnitriangular.groupScheme_def R (Fin n)).symm :=
  (rfl)

/-- Composing the upper-unitriangular representation with `U_n ⟶ GL_n` recovers the usual
general-linear representation. -/
theorem upperUnitriangularGroupSchemeHom_comp_inclusion
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    upperUnitriangularGroupSchemeHom (H := H) b h ≫
        UpperUnitriangular.inclusion R n =
      coordinateGroupSchemeHom (H := H) b := by
  rw [upperUnitriangularGroupSchemeHom_def, UpperUnitriangular.inclusion_def,
    coordinateGroupSchemeHom_def]
  simp only [Category.assoc]
  rw [← Category.assoc
    (eqToHom (UpperUnitriangular.groupScheme_def R (Fin n)).symm)
    (eqToHom (UpperUnitriangular.groupScheme_def R (Fin n)))]
  simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  simp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op]
  apply CommHopfAlgCat.hom_ext
  exact upperUnitriangularCoordinateBialgHom_comp_coordinateMap b h

/-- The upper-unitriangular representation morphism is a closed immersion exactly when its
coordinate Hopf-algebra morphism is surjective. -/
@[simp]
theorem isClosedImmersion_upperUnitriangularGroupSchemeHom_iff
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    IsClosedImmersion (upperUnitriangularGroupSchemeHom (H := H) b h).hom.hom.left ↔
      Function.Surjective (upperUnitriangularCoordinateBialgHom (H := H) b h) := by
  let _ : IsIso
      (eqToHom (UpperUnitriangular.groupScheme_def R (Fin n)).symm).hom.hom.left :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (UpperUnitriangular.groupScheme_def R (Fin n)).symm))).isIso_hom
  rw [upperUnitriangularGroupSchemeHom]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  exact CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff _

/-- A faithful comodule whose coefficient matrix is upper unitriangular defines a closed
immersion of the represented affine group into `U_n`. -/
theorem isClosedImmersion_upperUnitriangularGroupSchemeHom_of_isFaithful
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hM : IsFaithful (k := R) (H := H) (V := M)) :
    IsClosedImmersion (upperUnitriangularGroupSchemeHom (H := H) b h).hom.hom.left := by
  rw [isClosedImmersion_upperUnitriangularGroupSchemeHom_iff]
  exact upperUnitriangularCoordinateBialgHom_surjective_of_isFaithful b h hM

end

end TauCeti.Comodule
