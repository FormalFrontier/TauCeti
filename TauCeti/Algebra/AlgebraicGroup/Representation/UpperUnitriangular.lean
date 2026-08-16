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
* `TauCeti.Comodule.upperUnitriangularCoordinateBialgHom_X`: its value on strict-upper
  coordinate generators.
* `TauCeti.Comodule.upperUnitriangularCoordinateBialgHom_comp_coordinateMap`: its factorization of
  the general-linear coordinate morphism.
* `TauCeti.Comodule.upperUnitriangularCoordinateGroupSchemeHom`: the corresponding group-scheme
  morphism into `U_n`.
* `TauCeti.Comodule.isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff_isFaithful`:
  the morphism into `U_n` is a closed immersion exactly when the comodule is faithful.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open CategoryTheory AlgebraicGeometry Module

universe u v w x

noncomputable section

section CoordinateAlgebra

variable {R : Type u} {H : Type v} {M : Type w} {m : Type x} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Fintype m] [LinearOrder m]

/-- Evaluate the strict-upper coordinates of `O(U_n)` at the corresponding entries of the
coefficient matrix. The upper-unitriangular hypothesis is used below to prove this algebra map
respects the coalgebra structure. -/
private def upperUnitriangularCoordinateAlgHom
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    UpperUnitriangular.coordinateHopfAlgebra R m →ₐ[R] H :=
  (UpperUnitriangular.upperUnitriangularToPoint R m
    ⟨h.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h⟩).ofConv

private theorem upperUnitriangularCoordinateAlgHom_counit
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (Bialgebra.counitAlgHom R H).comp
        (upperUnitriangularCoordinateAlgHom (H := H) b h) =
      Bialgebra.counitAlgHom R
        (UpperUnitriangular.coordinateHopfAlgebra R m) := by
  apply UpperUnitriangular.coordinateHopfAlgebra_algHom_ext R m
  intro ij
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
    upperUnitriangularCoordinateAlgHom, UpperUnitriangular.upperUnitriangularToPoint_apply,
    h.coe_toGL, counit_coefficientMatrix]
  simp [Bialgebra.counitAlgHom_apply, ij.2.ne]

private theorem upperUnitriangularCoordinateAlgHom_comul
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (Algebra.TensorProduct.map
        (upperUnitriangularCoordinateAlgHom (H := H) b h)
        (upperUnitriangularCoordinateAlgHom (H := H) b h)).comp
        (Bialgebra.comulAlgHom R
          (UpperUnitriangular.coordinateHopfAlgebra R m)) =
      (Bialgebra.comulAlgHom R H).comp
        (upperUnitriangularCoordinateAlgHom (H := H) b h) := by
  have hgeneric (i j : m) :
      upperUnitriangularCoordinateAlgHom (H := H) b h
          (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R m
            (UpperUnitriangular.genericMatrix R m i j)) =
        coefficientMatrix (C := H) b i j := by
    rw [upperUnitriangularCoordinateAlgHom]
    rw [← UpperUnitriangular.pointToUpperUnitriangular_apply]
    simp only [UpperUnitriangular.pointToUpperUnitriangular_upperUnitriangularToPoint,
      h.coe_toGL]
  have hX (ij : UpperUnitriangular.Index m) :
      upperUnitriangularCoordinateAlgHom (H := H) b h
          (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
        coefficientMatrix (C := H) b ij.1.1 ij.1.2 := by
    rw [upperUnitriangularCoordinateAlgHom,
      UpperUnitriangular.upperUnitriangularToPoint_apply, h.coe_toGL]
  apply UpperUnitriangular.coordinateHopfAlgebra_algHom_ext R m
  intro ij
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    UpperUnitriangular.coordinateHopfAlgebra_comul_X, map_sum,
    Algebra.TensorProduct.map_tmul,
    hgeneric, hX]
  exact (comul_coefficientMatrix_eq_sum (C := H) b ij.1.1 ij.1.2).symm

/-- The coordinate Hopf-algebra morphism of a comodule whose coefficient matrix is upper
unitriangular in the chosen basis. It sends each strict-upper coordinate of `U_n` to the
corresponding matrix coefficient. -/
def upperUnitriangularCoordinateBialgHom
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    UpperUnitriangular.coordinateHopfAlgebra R m →ₐc[R] H :=
  BialgHom.ofAlgHom (upperUnitriangularCoordinateAlgHom b h)
    (upperUnitriangularCoordinateAlgHom_counit b h)
    (upperUnitriangularCoordinateAlgHom_comul b h)

/-- The upper-unitriangular coordinate morphism sends each strict-upper coordinate generator
to the corresponding coefficient-matrix entry. -/
@[simp]
theorem upperUnitriangularCoordinateBialgHom_X
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (ij : UpperUnitriangular.Index m) :
    upperUnitriangularCoordinateBialgHom (H := H) b h
        (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
      coefficientMatrix (C := H) b ij.1.1 ij.1.2 := by
  simp only [upperUnitriangularCoordinateBialgHom, BialgHom.ofAlgHom_apply,
    upperUnitriangularCoordinateAlgHom, UpperUnitriangular.upperUnitriangularToPoint_apply,
    h.coe_toGL]

/-- The upper-unitriangular coordinate morphism sends every entry of the generic matrix to the
corresponding coefficient-matrix entry. -/
@[simp]
theorem upperUnitriangularCoordinateBialgHom_genericMatrix_apply
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (i j : m) :
    upperUnitriangularCoordinateBialgHom (H := H) b h
        (UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R m
          (UpperUnitriangular.genericMatrix R m i j)) =
      coefficientMatrix (C := H) b i j := by
  simp only [upperUnitriangularCoordinateBialgHom, BialgHom.ofAlgHom_apply]
  rw [upperUnitriangularCoordinateAlgHom]
  rw [← UpperUnitriangular.pointToUpperUnitriangular_apply]
  simp only [UpperUnitriangular.pointToUpperUnitriangular_upperUnitriangularToPoint,
    h.coe_toGL]

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

/-- If the ordinary coordinate morphism of an upper-unitriangular representation is surjective,
then its factored coordinate morphism `O(U_n) ⟶ H` is surjective. -/
theorem upperUnitriangularCoordinateBialgHom_surjective_of_coordinateBialgHom_surjective
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hsurj : Function.Surjective (coordinateBialgHom (H := H) b)) :
    Function.Surjective (upperUnitriangularCoordinateBialgHom (H := H) b h) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  refine ⟨(UpperUnitriangular.coordinateMap R n).hom x, ?_⟩
  exact DFunLike.congr_fun
    (upperUnitriangularCoordinateBialgHom_comp_coordinateMap b h) x

end CoordinateAlgebra

section GroupScheme

variable {R H M : Type u} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The upper-unitriangular coordinate morphism is surjective exactly when the comodule is
faithful. -/
theorem upperUnitriangularCoordinateBialgHom_surjective_iff_isFaithful
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    Function.Surjective (upperUnitriangularCoordinateBialgHom (H := H) b h) ↔
      IsFaithful (k := R) (H := H) (V := M) := by
  rw [isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
    isClosedImmersion_coordinateGroupSchemeHom_iff]
  constructor
  · intro hsurj
    rw [← upperUnitriangularCoordinateBialgHom_comp_coordinateMap b h]
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    obtain ⟨z, hz⟩ := UpperUnitriangular.coordinateMap_surjective R n x
    refine ⟨z, ?_⟩
    simpa only [BialgHom.comp_apply, hz] using hx
  · exact
      upperUnitriangularCoordinateBialgHom_surjective_of_coordinateBialgHom_surjective b h

variable {m : Type} [Fintype m] [LinearOrder m]

/-- The morphism from the affine group represented by `H` to the upper-unitriangular group
associated to a basis in which the coefficient matrix is upper unitriangular. -/
def upperUnitriangularCoordinateGroupSchemeHom
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    (hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
      UpperUnitriangular.groupScheme R m :=
  (hopfSpec (CommRingCat.of R)).map
      (CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom b h)).op ≫
    eqToHom (UpperUnitriangular.groupScheme_def R m).symm

/-- The upper-unitriangular representation morphism is relative spectrum applied to its
coordinate morphism, followed by the defining identification of the upper-unitriangular group. -/
theorem upperUnitriangularCoordinateGroupSchemeHom_def
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    upperUnitriangularCoordinateGroupSchemeHom (H := H) b h =
      (hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom b h)).op ≫
        eqToHom (UpperUnitriangular.groupScheme_def R m).symm :=
  (rfl)

/-- Composing the upper-unitriangular representation with `U_n ⟶ GL_n` recovers the usual
general-linear representation. -/
theorem upperUnitriangularCoordinateGroupSchemeHom_comp_inclusion
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    upperUnitriangularCoordinateGroupSchemeHom (H := H) b h ≫
        UpperUnitriangular.inclusion R n =
      coordinateGroupSchemeHom (H := H) b := by
  rw [upperUnitriangularCoordinateGroupSchemeHom_def, UpperUnitriangular.inclusion_def,
    coordinateGroupSchemeHom_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hcoordinate :
      CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b) =
        UpperUnitriangular.coordinateMap R n ≫
          CommHopfAlgCat.ofHom (upperUnitriangularCoordinateBialgHom (H := H) b h) := by
    rw [← CommHopfAlgCat.ofHom_hom (UpperUnitriangular.coordinateMap R n),
      ← CommHopfAlgCat.ofHom_comp]
    exact congrArg CommHopfAlgCat.ofHom
      (upperUnitriangularCoordinateBialgHom_comp_coordinateMap b h).symm
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ← hcoordinate]

/-- The upper-unitriangular representation morphism is a closed immersion exactly when its
coordinate Hopf-algebra morphism is surjective. -/
@[simp]
theorem isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff
    (b : Basis m R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    IsClosedImmersion
        (upperUnitriangularCoordinateGroupSchemeHom (H := H) b h).hom.hom.left ↔
      Function.Surjective (upperUnitriangularCoordinateBialgHom (H := H) b h) := by
  rw [upperUnitriangularCoordinateGroupSchemeHom]
  exact CommHopfAlgCat.isClosedImmersion_hopfSpec_map_comp_eqToHom_iff
    (UpperUnitriangular.groupScheme_def R m) _

/-- The morphism into `U_n` defined by an upper-unitriangular coefficient matrix is a closed
immersion exactly when the comodule is faithful. -/
theorem isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff_isFaithful
    (b : Basis (Fin n) R M) (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    IsClosedImmersion
        (upperUnitriangularCoordinateGroupSchemeHom (H := H) b h).hom.hom.left ↔
      IsFaithful (k := R) (H := H) (V := M) := by
  rw [isClosedImmersion_upperUnitriangularCoordinateGroupSchemeHom_iff,
    upperUnitriangularCoordinateBialgHom_surjective_iff_isFaithful]

end GroupScheme

end

end TauCeti.Comodule
