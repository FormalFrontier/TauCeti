/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.PointRepresentation

/-!
# Scheme morphisms from Kostant root subgroups

Let a Kostant integral form act on a rational representation, preserving an integral lattice
`M`. A finite basis of `M` turns the divided-power exponential attached to a nilpotent root vector
into a natural family of homomorphisms

```text
𝔾ₐ(A) → GLₙ(A).
```

The associated polynomial comodule determines a coordinate Hopf-algebra morphism
`O(GLₙ) → O(𝔾ₐ)`. Relative spectrum then gives a genuine affine group-scheme morphism
`𝔾ₐ → GLₙ` over `ℤ`. This file proves that its action on points is exactly the original Kostant
exponential matrix.

Integral PBW must still produce the finite free admissible lattices used by the
Chevalley--Demazure construction. The results here apply once such a lattice and basis are given.
The representation carrier is universe-zero because the current group-scheme reconstruction API
requires the base, coordinate Hopf algebra, and comodule to inhabit the same universe.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap`: the coordinate
  Hopf-algebra morphism represented by the Kostant polynomial coaction.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup`: the affine group-scheme morphism
  `𝔾ₐ → GLₙ`.
* `TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap`: the
  induced matrix is the original Kostant exponential matrix.
* `TauCeti.UniversalEnvelopingAlgebra.schemePointsMulEquiv_kostantRootSubgroup`: the same
  compatibility for scheme-valued points.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (i : I)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

/-- The coordinate Hopf-algebra morphism of the Kostant root subgroup in the basis `b`.

It sends the generic matrix to the coefficient matrix of the finite polynomial comodule
`kostantRootSubgroupComodule`. -/
noncomputable def kostantRootSubgroupCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra ℤ n ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ := by
  let : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  exact CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom b)

/-- A generic matrix coordinate pulls back to the corresponding matrix coefficient of the
Kostant polynomial comodule. -/
theorem kostantRootSubgroupCoordinateMap_X (r s : Fin n) :
    (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s)))) =
      letI : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
        kostantRootSubgroupComodule e h ρ M hM i hnil
      Comodule.coefficientMatrix
        (C := AdditiveGroup.coordinateHopfAlgebra ℤ) b r s := by
  let : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  exact Comodule.coordinateBialgHom_X b r s

/-- The affine group-scheme morphism `𝔾ₐ → GLₙ` represented by the Kostant divided-power
exponential in the basis `b`. -/
noncomputable def kostantRootSubgroup :
    AdditiveGroup.groupScheme ℤ ⟶ GeneralLinear.groupScheme ℤ n := by
  let : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  exact eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
    Comodule.coordinateGroupSchemeHom b

/-- The Kostant root subgroup is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism, transported across the named presentation of `𝔾ₐ`. -/
theorem kostantRootSubgroup_def :
    kostantRootSubgroup e h ρ M hM i hnil b =
      eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).op ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ n).symm := by
  let : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  rw [kostantRootSubgroup, Comodule.coordinateGroupSchemeHom_def]
  rfl

section Points

variable (A : Type) [CommRing A]

/-- On algebra-valued points, precomposition with the Kostant coordinate morphism gives the
original divided-power exponential matrix. -/
theorem pointsMulEquiv_kostantRootSubgroupCoordinateMap_apply
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) (r s : Fin n) :
    (GeneralLinear.pointsMulEquiv n
        (toConv (q.ofConv.comp
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom))).val r s =
      (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil q).val
          (b.baseChange A s)) r := by
  let : Comodule ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
    WithConv.ofConv_toConv, AlgHom.comp_apply]
  change q.ofConv
      ((kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s))))) = _
  rw [kostantRootSubgroupCoordinateMap_X]
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    kostantRootSubgroupComodule_coact]
  rw [Module.Basis.baseChange_apply, kostantRootSubgroupPoints_tmul]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    AdditiveGroup.toAdd_gaPointsMulEquiv, mul_one]
  -- Evaluation of a `Finsupp` sum does not normalize to the sum of its evaluations by
  -- definitional equality, so expose the evaluation linear map before using `map_sum`.
  change
    (∑ x ∈ Finset.range
        (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
      q.ofConv
        ((b.coord r) (integralDividedPower
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M x
          (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
            e h ρ hM i x hv) (b s)) •
          (SymmetricAlgebra.ι ℤ ℤ 1) ^ x)) =
      (Finsupp.lapply r : (Fin n →₀ A) →ₗ[A] A)
        (∑ x ∈ Finset.range
          (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
          (b.baseChange A).repr
            ((q.ofConv (SymmetricAlgebra.ι ℤ ℤ 1) ^ x) ⊗ₜ[ℤ]
              integralDividedPower
                (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M x
                (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
                  e h ρ hM i x hv) (b s)))
  rw [map_sum (Finsupp.lapply r : (Fin n →₀ A) →ₗ[A] A)]
  simp only [Finsupp.lapply_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_pow,
    Module.Basis.baseChange_repr_tmul]
  simp only [Module.Basis.coord_apply, Algebra.smul_def]

/-- On algebra-valued points, the matrix induced by the Kostant coordinate morphism is the
original divided-power exponential matrix. -/
@[simp]
theorem pointsMulEquiv_kostantRootSubgroupCoordinateMap
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    GeneralLinear.pointsMulEquiv n
        (toConv (q.ofConv.comp
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom)) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b q := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [kostantRootSubgroupMatrix_apply]
  exact pointsMulEquiv_kostantRootSubgroupCoordinateMap_apply
    e h ρ M hM i hnil b A q r s

private theorem groupSchemePointMulEquiv_comp_kostantRootSubgroup
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    AdditiveGroup.groupSchemePointMulEquiv A q ≫
        (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv n A
        ((CommHopfAlgCat.mapPointsFunctor
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b)).app
            (CommAlgCat.of ℤ A) q) := by
  rw [kostantRootSubgroup_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ℤ) A (GeneralLinear.groupScheme_def ℤ n)
      (AdditiveGroup.groupScheme_def ℤ)
      (GeneralLinear.groupSchemePointMulEquiv n A)
      (AdditiveGroup.groupSchemePointMulEquiv A)
      (GeneralLinear.groupSchemePointMulEquiv_apply_left n A)
      (AdditiveGroup.groupSchemePointMulEquiv_apply_left A)
      (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b) q

/-- On scheme-valued points, the represented Kostant root subgroup is exactly the
divided-power exponential matrix in the basis `b`. -/
theorem schemePointsMulEquiv_kostantRootSubgroup_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) (r s : Fin n) :
    (GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom)).val r s =
      (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil
          ((AdditiveGroup.groupSchemePointMulEquiv A).symm p)).val
            (b.baseChange A s)) r := by
  obtain ⟨q, rfl⟩ := (AdditiveGroup.groupSchemePointMulEquiv A).surjective p
  erw [groupSchemePointMulEquiv_comp_kostantRootSubgroup,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    pointsMulEquiv_kostantRootSubgroupCoordinateMap_apply,
    MulEquiv.symm_apply_apply]

/-- On scheme-valued points, the represented Kostant root subgroup is the original
divided-power exponential matrix in the basis `b`. -/
@[simp]
theorem schemePointsMulEquiv_kostantRootSubgroup
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        ((AdditiveGroup.groupSchemePointMulEquiv A).symm p) := by
  obtain ⟨q, rfl⟩ := (AdditiveGroup.groupSchemePointMulEquiv A).surjective p
  erw [groupSchemePointMulEquiv_comp_kostantRootSubgroup,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    CommHopfAlgCat.mapPointsFunctor_app_apply,
    pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    MulEquiv.symm_apply_apply]

end Points

end TauCeti.UniversalEnvelopingAlgebra
