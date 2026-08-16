/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.HopfAlgebra.Augmentation

/-!
# Translations of an affine group

A `k`-point of an affine group acts on its coordinate algebra by translation. For a
commutative Hopf algebra `H` over `k`, a point `g : H →ₐ[k] k` defines the algebra endomorphism

```text
x ↦ ∑ x₍₁₎ g(x₍₂₎).
```

The regular-comodule action shows that this endomorphism is bijective, with inverse obtained from
the convolution inverse point. This file packages it as an algebra equivalence, records its group
action laws, and identifies its action on the prime spectrum.

## Main declarations

* `TauCeti.HopfAlgebra.rightTranslationAlgHom`: pullback by right translation by a point.
* `TauCeti.HopfAlgebra.rightTranslationAlgEquiv`: right translation as an algebra automorphism.
* `TauCeti.HopfAlgebra.rightTranslationAlgEquiv_mul`: right translation respects the convolution
  product of points.
* `TauCeti.HopfAlgebra.comap_rightTranslationAlgEquiv_augmentationPoint`: the translated counit
  point is the given point.
* `TauCeti.HopfAlgebra.rightTranslationHomeomorph`: right translation on the prime spectrum.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This is translation infrastructure for Layer 3, "Identity component `G°` and component group
`π₀(G)`", of the ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

section CommRing

variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]

/-- Pullback by right translation by a `k`-point of an affine group, on its coordinate algebra. -/
noncomputable def rightTranslationAlgHom (g : WithConv (H →ₐ[k] k)) : H →ₐ[k] H :=
  (WithConv.toConv (AlgHom.id k H) *
    WithConv.toConv ((Algebra.ofId k H).comp g.ofConv)).ofConv

/-- Right translation evaluates by applying the point to the second tensor factor of the
comultiplication. -/
theorem rightTranslationAlgHom_apply (g : WithConv (H →ₐ[k] k)) (x : H) :
    rightTranslationAlgHom g x =
      TensorProduct.rid k H
        (TensorProduct.map LinearMap.id g.ofConv.toLinearMap (Coalgebra.comul x)) := by
  rw [rightTranslationAlgHom, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) x using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul z w => simp [Algebra.smul_def, mul_comm]

/-- The linear equivalence underlying right translation. -/
private noncomputable def rightTranslationLinearEquiv (g : WithConv (H →ₐ[k] k)) :
    H ≃ₗ[k] H :=
  (TensorProduct.lid k H).symm.trans
    ((Comodule.pointsAction H g).trans (TensorProduct.lid k H))

private theorem rightTranslationLinearEquiv_toLinearMap
    (g : WithConv (H →ₐ[k] k)) :
    (rightTranslationLinearEquiv g).toLinearMap = (rightTranslationAlgHom g).toLinearMap := by
  ext x
  rw [rightTranslationLinearEquiv]
  -- Composition of the three linear equivalences is intentionally reduced to application here;
  -- the public comparison theorem below prevents consumers from relying on this representation.
  change TensorProduct.lid k H
      (Comodule.pointsAction H g ((TensorProduct.lid k H).symm x)) =
    rightTranslationAlgHom g x
  rw [TensorProduct.lid_symm_apply]
  have haction : Comodule.pointsAction H g (1 ⊗ₜ[k] x) =
      Comodule.endOfPoint H g.ofConv (1 ⊗ₜ[k] x) :=
    DFunLike.congr_fun (Comodule.pointsAction_toLinearMap H g) (1 ⊗ₜ[k] x)
  rw [haction, Comodule.endOfPoint_tmul, Comodule.instSelf_coact,
    rightTranslationAlgHom_apply]
  simp [LinearMap.lTensor_def]

private theorem rightTranslationAlgHom_bijective (g : WithConv (H →ₐ[k] k)) :
    Function.Bijective (rightTranslationAlgHom g) := by
  -- An algebra hom and its underlying linear map have definitionally the same function.
  change Function.Bijective (rightTranslationAlgHom g).toLinearMap
  rw [← rightTranslationLinearEquiv_toLinearMap g]
  exact (rightTranslationLinearEquiv g).bijective

/-- Pullback by right translation by a `k`-point, as an algebra automorphism of the coordinate
algebra. -/
noncomputable def rightTranslationAlgEquiv (g : WithConv (H →ₐ[k] k)) : H ≃ₐ[k] H :=
  AlgEquiv.ofBijective (rightTranslationAlgHom g) (rightTranslationAlgHom_bijective g)

/-- The algebra equivalence underlying right translation is the right-translation algebra
homomorphism. -/
@[simp]
theorem rightTranslationAlgEquiv_toAlgHom (g : WithConv (H →ₐ[k] k)) :
    (rightTranslationAlgEquiv g).toAlgHom = rightTranslationAlgHom g :=
  AlgEquiv.toAlgHom_ofBijective _ _

private theorem rightTranslationAlgEquiv_toLinearEquiv
    (g : WithConv (H →ₐ[k] k)) :
    (rightTranslationAlgEquiv g).toLinearEquiv = rightTranslationLinearEquiv g := by
  ext x
  -- Both bundled equivalences have the algebra hom's function as their reducible carrier.
  change rightTranslationAlgEquiv g x = rightTranslationLinearEquiv g x
  rw [show rightTranslationAlgEquiv g x = (rightTranslationAlgEquiv g).toAlgHom x from rfl,
    rightTranslationAlgEquiv_toAlgHom]
  exact (LinearMap.congr_fun (rightTranslationLinearEquiv_toLinearMap g) x).symm

private theorem rightTranslationLinearEquiv_one :
    rightTranslationLinearEquiv (1 : WithConv (H →ₐ[k] k)) = 1 := by
  ext x
  simp [rightTranslationLinearEquiv]

private theorem rightTranslationLinearEquiv_mul
    (g h : WithConv (H →ₐ[k] k)) :
    rightTranslationLinearEquiv (g * h) =
      rightTranslationLinearEquiv g * rightTranslationLinearEquiv h := by
  ext x
  simp [rightTranslationLinearEquiv]

/-- Translation by the identity point is the identity algebra automorphism. -/
@[simp]
theorem rightTranslationAlgEquiv_one :
    rightTranslationAlgEquiv (1 : WithConv (H →ₐ[k] k)) = 1 := by
  apply AlgEquiv.ext
  intro x
  calc
    rightTranslationAlgEquiv (1 : WithConv (H →ₐ[k] k)) x =
        rightTranslationLinearEquiv (1 : WithConv (H →ₐ[k] k)) x :=
      LinearEquiv.congr_fun
        (rightTranslationAlgEquiv_toLinearEquiv (1 : WithConv (H →ₐ[k] k))) x
    _ = x := by rw [rightTranslationLinearEquiv_one]; simp
    _ = (1 : H ≃ₐ[k] H) x := (AlgEquiv.one_apply x).symm

/-- Translation by a convolution product is the composite of the two translations. -/
@[simp]
theorem rightTranslationAlgEquiv_mul (g h : WithConv (H →ₐ[k] k)) :
    rightTranslationAlgEquiv (g * h) =
      rightTranslationAlgEquiv g * rightTranslationAlgEquiv h := by
  apply AlgEquiv.ext
  intro x
  calc
    rightTranslationAlgEquiv (g * h) x = rightTranslationLinearEquiv (g * h) x :=
      LinearEquiv.congr_fun (rightTranslationAlgEquiv_toLinearEquiv (g * h)) x
    _ = (rightTranslationLinearEquiv g * rightTranslationLinearEquiv h) x :=
      LinearEquiv.congr_fun (rightTranslationLinearEquiv_mul g h) x
    _ = rightTranslationLinearEquiv g (rightTranslationLinearEquiv h x) :=
      LinearEquiv.mul_apply _ _ x
    _ = rightTranslationLinearEquiv g (rightTranslationAlgEquiv h x) :=
      congrArg (rightTranslationLinearEquiv g)
        (LinearEquiv.congr_fun (rightTranslationAlgEquiv_toLinearEquiv h) x).symm
    _ = rightTranslationAlgEquiv g (rightTranslationAlgEquiv h x) :=
      (LinearEquiv.congr_fun (rightTranslationAlgEquiv_toLinearEquiv g)
        (rightTranslationAlgEquiv h x)).symm
    _ = (rightTranslationAlgEquiv g * rightTranslationAlgEquiv h) x :=
      (AlgEquiv.mul_apply _ _ x).symm

/-- Translation by an inverse point is the inverse algebra automorphism. -/
@[simp]
theorem rightTranslationAlgEquiv_inv (g : WithConv (H →ₐ[k] k)) :
    rightTranslationAlgEquiv g⁻¹ = (rightTranslationAlgEquiv g)⁻¹ := by
  exact map_inv (MonoidHom.mk' rightTranslationAlgEquiv rightTranslationAlgEquiv_mul) g

/-- Right translation as an algebra equivalence has the expected evaluation formula. -/
theorem rightTranslationAlgEquiv_apply (g : WithConv (H →ₐ[k] k)) (x : H) :
    rightTranslationAlgEquiv g x =
      TensorProduct.rid k H
        (TensorProduct.map LinearMap.id g.ofConv.toLinearMap (Coalgebra.comul x)) := by
  calc
    rightTranslationAlgEquiv g x = (rightTranslationAlgEquiv g).toAlgHom x :=
      (rightTranslationAlgEquiv g).toAlgHom_apply x |>.symm
    _ = rightTranslationAlgHom g x :=
      DFunLike.congr_fun (rightTranslationAlgEquiv_toAlgHom g) x
    _ = _ := rightTranslationAlgHom_apply g x

/-- Evaluating a right-translated function at the identity evaluates the original function at
the translating point. -/
@[simp]
theorem counitAlgHom_comp_rightTranslationAlgHom (g : WithConv (H →ₐ[k] k)) :
    (_root_.Bialgebra.counitAlgHom k H).comp (rightTranslationAlgHom g) = g.ofConv := by
  rw [rightTranslationAlgHom, AlgHom.comp_convMul_distrib]
  have hcounit :
      (_root_.Bialgebra.counitAlgHom k H).comp (AlgHom.id k H) =
        _root_.Bialgebra.counitAlgHom k H := by
    rw [AlgHom.comp_id]
  have hpoint :
      (_root_.Bialgebra.counitAlgHom k H).comp
          ((Algebra.ofId k H).comp g.ofConv) = g.ofConv := by
    ext x
    simp
  rw [hcounit, hpoint]
  -- `WithConv.ofConv` is the wrapper field, so expose it once to use the point-group identity.
  change (1 * g).ofConv = g.ofConv
  rw [one_mul]

/-- Right translation on the prime spectrum. The inverse algebra equivalence occurs because
`Spec` is contravariant. -/
noncomputable def rightTranslationHomeomorph (g : WithConv (H →ₐ[k] k)) :
    Spec (CommRingCat.of H) ≃ₜ Spec (CommRingCat.of H) :=
  PrimeSpectrum.homeomorphOfRingEquiv (rightTranslationAlgEquiv g).symm.toRingEquiv

/-- Right translation on the prime spectrum is contraction along the right-translation algebra
automorphism. -/
@[simp]
theorem rightTranslationHomeomorph_apply (g : WithConv (H →ₐ[k] k))
    (x : Spec (CommRingCat.of H)) :
    rightTranslationHomeomorph g x =
      PrimeSpectrum.comap ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H) x := by
  rw [rightTranslationHomeomorph]
  rfl

end CommRing

section Field

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]

/-- Contraction of the augmentation point along right translation gives the translating point. -/
@[simp]
theorem comap_rightTranslationAlgEquiv_augmentationPoint
    (g : WithConv (H →ₐ[k] k)) :
    PrimeSpectrum.comap (rightTranslationAlgEquiv g)
        (Bialgebra.augmentationPoint k H) =
      AlgHom.kernelPoint g.ofConv := by
  -- These abbreviations reduce `Spec H` points to kernels of their representing algebra maps.
  change PrimeSpectrum.comap
      ((rightTranslationAlgEquiv g).toAlgHom : H →+* H)
        (AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)) =
    AlgHom.kernelPoint g.ofConv
  rw [rightTranslationAlgEquiv_toAlgHom, AlgHom.comap_kernelPoint,
    counitAlgHom_comp_rightTranslationAlgHom]

end Field

end TauCeti.HopfAlgebra
