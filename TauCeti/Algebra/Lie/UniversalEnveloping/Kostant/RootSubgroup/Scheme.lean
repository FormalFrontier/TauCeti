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
import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Kostant root-subgroup scheme morphisms

Let an integral module `M` be stable under a Kostant form, and suppose that a chosen root vector
acts nilpotently. The divided-power exponential has already been constructed as a natural
homomorphism on points and as a polynomial comodule over `ℤ[X]`. A finite basis of `M` turns that
comodule into a coordinate Hopf-algebra morphism

```text
O(GLₙ) ⟶ ℤ[X].
```

Taking relative spectrum constructs the represented root-subgroup morphism
`𝔾ₐ → GLₙ`. This file proves that its action on points is exactly the previously constructed
Kostant exponential matrix, so the coordinate, group-scheme, and functor-of-points descriptions
agree.

The same-universe restriction on `M` is inherited from Mathlib's current relative-spectrum
construction. It is harmless for the finite free integral lattices used in the
Chevalley--Demazure construction.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateBialgHom`: the coordinate
  morphism `O(GLₙ) ⟶ ℤ[X]`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupSchemeHom`: the represented morphism
  `𝔾ₐ → GLₙ`.
* `TauCeti.UniversalEnvelopingAlgebra.mapDomain_kostantRootSubgroupCoordinateBialgHom`: the
  induced map on algebra-valued points is the Kostant exponential matrix.
* `TauCeti.UniversalEnvelopingAlgebra.schemePoints_kostantRootSubgroupSchemeHom`: the same
  compatibility for scheme-valued points.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This is the represented root-subgroup-map step in Layer 9, "Root subgroup maps", of the
ReductiveGroups roadmap. It is the bridge from integral Kostant exponentials to the root
subgroups of the eventual pinned Chevalley--Demazure group scheme.
-/

public section

open CategoryTheory MonObj TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {α : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : α → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ x ∈ kostantForm e h, ∀ m ∈ M, ρ x m ∈ M)
variable (a : α)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e a))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

/-- The coordinate Hopf-algebra morphism of the Kostant root subgroup in a finite integral
basis. Contravariantly, it represents `𝔾ₐ → GLₙ`. -/
noncomputable def kostantRootSubgroupCoordinateBialgHom :
    GeneralLinear.coordinateHopfAlgebra ℤ n →ₐc[ℤ] SymmetricAlgebra ℤ ℤ :=
  let _ : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM a hnil
  Comodule.coordinateBialgHom b

/-- A generic matrix coordinate pulls back along the Kostant root subgroup to the corresponding
matrix coefficient of its polynomial comodule. -/
@[simp]
theorem kostantRootSubgroupCoordinateBialgHom_X (r s : Fin n) :
    kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s)))) =
      @Comodule.coefficientMatrix ℤ (SymmetricAlgebra ℤ ℤ) M (Fin n)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        (kostantRootSubgroupComodule e h ρ M hM a hnil) b r s := by
  let _ : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM a hnil
  exact Comodule.coordinateBialgHom_X b r s

/-- The Kostant root-subgroup morphism from the additive group scheme to the general linear
group scheme determined by the chosen integral basis. -/
noncomputable def kostantRootSubgroupSchemeHom :
    AdditiveGroup.groupScheme ℤ ⟶ GeneralLinear.groupScheme ℤ n :=
  eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
      (CommHopfAlgCat.ofHom
        (kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b)).op ≫
    eqToHom (GeneralLinear.groupScheme_def ℤ n).symm

/-- The Kostant root-subgroup scheme morphism is relative spectrum applied contravariantly to
its coordinate Hopf-algebra morphism, with the named source and target presentations. -/
theorem kostantRootSubgroupSchemeHom_def :
    kostantRootSubgroupSchemeHom e h ρ M hM a hnil b =
      eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (CommHopfAlgCat.ofHom
            (kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b)).op ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ n).symm :=
  (rfl)

private theorem endOfPoint_rootSubgroupComodule {A : Type} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    letI : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
      kostantRootSubgroupComodule e h ρ M hM a hnil
    Comodule.endOfPoint M f.ofConv =
        (kostantRootSubgroupPoints e h ρ M hM a hnil f).val := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c m
  rw [Comodule.endOfPoint_tmul, kostantRootSubgroupComodule_coact,
    kostantRootSubgroupPoints_tmul]
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    TensorProduct.comm_tmul, map_pow, AdditiveGroup.toAdd_gaPointsMulEquiv]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [TensorProduct.smul_tmul', smul_eq_mul]
  congr 1
  ac_rfl

/-- On algebra-valued points, precomposition with the coordinate morphism gives exactly the
matrix of the Kostant divided-power exponential in the chosen basis. -/
@[simp]
theorem mapDomain_kostantRootSubgroupCoordinateBialgHom {A : Type} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    GeneralLinear.pointToGeneralLinear n
        (WithConv.toConv
          (f.ofConv.comp
            ↑(kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b))) =
      kostantRootSubgroupMatrix e h ρ M hM a hnil b f := by
  let _ : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM a hnil
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [GeneralLinear.pointToGeneralLinear_apply, kostantRootSubgroupMatrix_apply]
  change f.ofConv
      (kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s))))) = _
  rw [kostantRootSubgroupCoordinateBialgHom_X,
    Comodule.coefficientMatrix_apply]
  calc
    f.ofConv (Comodule.matrixCoefficient (b.coord r) (b s)) =
        TauCeti.Module.Dual.baseChangeEvaluation (1 ⊗ₜ[ℤ] b.coord r)
          (Comodule.endOfPoint M f.ofConv (1 ⊗ₜ[ℤ] b s)) := by
      symm
      simp [Comodule.baseChangeEvaluation_endOfPoint_tmul]
    _ = TauCeti.Module.Dual.baseChangeEvaluation (1 ⊗ₜ[ℤ] b.coord r)
          ((kostantRootSubgroupPoints e h ρ M hM a hnil f).val (1 ⊗ₜ[ℤ] b s)) := by
      rw [endOfPoint_rootSubgroupComodule]
    _ = (b.baseChange A).repr
          ((kostantRootSubgroupPoints e h ρ M hM a hnil f).val
            (b.baseChange A s)) r := by
      rw [TauCeti.Module.Dual.baseChangeEvaluation_one_tmul,
        Module.Basis.baseChange_apply]
      have hcoord (z : A ⊗[ℤ] M) :
          Module.Dual.baseChange A (b.coord r) z =
            (b.baseChange A).repr z r := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hx hy
        | tmul c m =>
            simp [Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
      exact hcoord _

/-- On scheme-valued points, postcomposition with the represented root-subgroup morphism is the
Kostant divided-power exponential matrix. This synchronizes the group-scheme and
functor-of-points descriptions of the root subgroup. -/
@[simp]
theorem schemePoints_kostantRootSubgroupSchemeHom {A : Type} [CommRing A]
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroupSchemeHom e h ρ M hM a hnil b).hom.hom) =
      kostantRootSubgroupMatrix e h ρ M hM a hnil b
        ((AdditiveGroup.groupSchemePointMulEquiv A).symm p) := by
  let f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) :=
    (AdditiveGroup.groupSchemePointMulEquiv A).symm p
  have hp : AdditiveGroup.groupSchemePointMulEquiv A f = p :=
    (AdditiveGroup.groupSchemePointMulEquiv A).apply_symm_apply p
  have hmap := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := ℤ) (A := A)
    (GeneralLinear.groupScheme_def ℤ n)
    (AdditiveGroup.groupScheme_def ℤ)
    (GeneralLinear.groupSchemePointMulEquiv n A)
    (AdditiveGroup.groupSchemePointMulEquiv A)
    (GeneralLinear.groupSchemePointMulEquiv_apply_left n A)
    (AdditiveGroup.groupSchemePointMulEquiv_apply_left A)
    (CommHopfAlgCat.ofHom
      (kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b)) f
  rw [hp] at hmap
  rw [kostantRootSubgroupSchemeHom_def, hmap]
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  rw [GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv]
  simp only [CommHopfAlgCat.hom_ofHom]
  rw [GeneralLinear.pointsMulEquiv_apply]
  simpa only [f] using
    mapDomain_kostantRootSubgroupCoordinateBialgHom e h ρ M hM a hnil b f

end TauCeti.UniversalEnvelopingAlgebra
