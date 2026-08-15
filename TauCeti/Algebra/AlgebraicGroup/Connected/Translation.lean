/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-!
# Translations of an affine group

An algebra-valued point of an affine group acts on its coordinate algebra by translation.  For a
commutative Hopf algebra `H` over `k`, a `k`-point `g : H →ₐ[k] k` defines the algebra
endomorphism

```text
x ↦ ∑ x₍₁₎ g(x₍₂₎).
```

The regular-comodule action shows that this endomorphism is bijective, with inverse obtained from
the convolution inverse point.  This file packages it as an algebra equivalence and identifies its
action on prime spectra.  In particular, translating by a point in the connected component of the
counit preserves that component.

## Main declarations

* `TauCeti.HopfAlgebra.rightTranslationAlgHom`: pullback by right translation by a point.
* `TauCeti.HopfAlgebra.rightTranslationAlgEquiv`: right translation as an algebra automorphism.
* `TauCeti.HopfAlgebra.comap_rightTranslationAlgEquiv_augmentationPoint`: the translated counit
  point is the given point.
* `TauCeti.HopfAlgebra.rightTranslation_preserves_augmentationPoint_connectedComponent`: a point
  in the identity component translates that component to itself.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This is the translation prerequisite for Layer 3, "Identity component `G°` and component group
`π₀(G)`", of the ReductiveGroups roadmap.  The next step uses these automorphisms to prove
that multiplication carries the product of the identity component with itself into the identity
component, giving comultiplication closure of its defining ideal.
-/

public section

open AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k]
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

/-- Right translation as an algebra equivalence has the expected evaluation formula. -/
theorem rightTranslationAlgEquiv_apply (g : WithConv (H →ₐ[k] k)) (x : H) :
    rightTranslationAlgEquiv g x =
      TensorProduct.rid k H
        (TensorProduct.map LinearMap.id g.ofConv.toLinearMap (Coalgebra.comul x)) := by
  rw [← rightTranslationAlgHom_apply]
  rfl

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
  change (1 * g).ofConv = g.ofConv
  rw [one_mul]

/-- Contraction of the augmentation point along right translation gives the translating point. -/
@[simp]
theorem comap_rightTranslationAlgEquiv_augmentationPoint
    (g : WithConv (H →ₐ[k] k)) :
    PrimeSpectrum.comap (rightTranslationAlgEquiv g)
        (Bialgebra.augmentationPoint k H) =
      AlgHom.kernelPoint g.ofConv := by
  change PrimeSpectrum.comap
      ((rightTranslationAlgEquiv g).toAlgHom : H →+* H)
        (AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)) =
    AlgHom.kernelPoint g.ofConv
  rw [rightTranslationAlgEquiv_toAlgHom, AlgHom.comap_kernelPoint,
    counitAlgHom_comp_rightTranslationAlgHom]

/-- Right translation on the prime spectrum.  The inverse algebra equivalence occurs because
`Spec` is contravariant. -/
@[expose] noncomputable def rightTranslationHomeomorph (g : WithConv (H →ₐ[k] k)) :
    Spec (CommRingCat.of H) ≃ₜ Spec (CommRingCat.of H) :=
  PrimeSpectrum.homeomorphOfRingEquiv (rightTranslationAlgEquiv g).symm.toRingEquiv

/-- Right translation on the prime spectrum is contraction along the right-translation algebra
automorphism. -/
@[simp]
theorem rightTranslationHomeomorph_apply (g : WithConv (H →ₐ[k] k))
    (x : Spec (CommRingCat.of H)) :
    rightTranslationHomeomorph g x =
      PrimeSpectrum.comap ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H) x :=
  rfl

/-- Right translation sends the identity point to the translating point. -/
@[simp]
theorem rightTranslationHomeomorph_augmentationPoint
    (g : WithConv (H →ₐ[k] k)) :
    PrimeSpectrum.comap (rightTranslationAlgEquiv g)
        (Bialgebra.augmentationPoint k H) =
      AlgHom.kernelPoint g.ofConv := by
  rw [comap_rightTranslationAlgEquiv_augmentationPoint]

/-- Right translation transports the connected component of a point to the connected component
of its translate. -/
theorem rightTranslationHomeomorph_image_connectedComponent
    (g : WithConv (H →ₐ[k] k)) (x : Spec (CommRingCat.of H)) :
    rightTranslationHomeomorph g '' connectedComponent x =
      connectedComponent (rightTranslationHomeomorph g x) := by
  simpa only [connectedComponentIn_univ,
    Set.image_univ_of_surjective (rightTranslationHomeomorph g).surjective] using
    (rightTranslationHomeomorph g).image_connectedComponentIn
      (s := Set.univ) (x := x) (Set.mem_univ x)

/-- A point in the identity component right-translates that component onto itself. -/
theorem rightTranslation_preserves_augmentationPoint_connectedComponent
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    rightTranslationHomeomorph g ''
        connectedComponent (Bialgebra.augmentationPoint k H) =
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  rw [rightTranslationHomeomorph_image_connectedComponent,
    rightTranslationHomeomorph_apply, AlgEquiv.toRingEquiv_toRingHom,
    rightTranslationHomeomorph_augmentationPoint]
  exact (connectedComponent_eq hg).symm

variable [LocallyConnectedSpace (PrimeSpectrum H)]

private theorem connectedComponentIdempotent_kernelPoint_eq_augmentationPoint
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint g.ofConv) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  let p : PrimeSpectrum H := AlgHom.kernelPoint g.ofConv
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  change PrimeSpectrum.connectedComponentIdempotent p =
    PrimeSpectrum.connectedComponentIdempotent e
  change p ∈ connectedComponent e at hg
  apply (PrimeSpectrum.eq_connectedComponentIdempotent_iff
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p) e).mpr
  rw [PrimeSpectrum.basicOpen_connectedComponentIdempotent]
  exact (connectedComponent_eq hg).symm

/-- The inverse coordinate-algebra automorphism of translation by an identity-component point
fixes the idempotent selecting the identity component. -/
theorem rightTranslationAlgEquiv_symm_connectedComponentIdempotent_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    (rightTranslationAlgEquiv g).symm
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  change (rightTranslationAlgEquiv g).symm
      (PrimeSpectrum.connectedComponentIdempotent e) =
    PrimeSpectrum.connectedComponentIdempotent e
  have he : PrimeSpectrum.comap
      ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H) e =
      AlgHom.kernelPoint g.ofConv :=
    comap_rightTranslationAlgEquiv_augmentationPoint g
  calc
    (rightTranslationAlgEquiv g).symm
        (PrimeSpectrum.connectedComponentIdempotent e) =
      PrimeSpectrum.connectedComponentIdempotent
        (PrimeSpectrum.comap
          (((rightTranslationAlgEquiv g).symm.toRingEquiv).symm : H →+* H) e) :=
      PrimeSpectrum.map_connectedComponentIdempotent
        (rightTranslationAlgEquiv g).symm.toRingEquiv e
    _ = PrimeSpectrum.connectedComponentIdempotent
        (PrimeSpectrum.comap
          ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H) e) := by rfl
    _ = PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint g.ofConv) :=
      congrArg PrimeSpectrum.connectedComponentIdempotent he
    _ = PrimeSpectrum.connectedComponentIdempotent e :=
      connectedComponentIdempotent_kernelPoint_eq_augmentationPoint g hg

/-- The coordinate-algebra automorphism of translation by an identity-component point fixes the
idempotent selecting the identity component. -/
theorem rightTranslationAlgEquiv_connectedComponentIdempotent_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    rightTranslationAlgEquiv g
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  have h := congrArg (rightTranslationAlgEquiv g)
    (rightTranslationAlgEquiv_symm_connectedComponentIdempotent_eq_self g hg)
  simpa using h.symm

/-- Membership in the identity-component ideal is invariant under translation by a point of the
identity component. -/
theorem rightTranslationAlgEquiv_mem_connectedComponentIdeal_iff
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) {x : H} :
    rightTranslationAlgEquiv g x ∈
        PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) ↔
      x ∈ PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  change rightTranslationAlgEquiv g x ∈
      PrimeSpectrum.connectedComponentIdeal e ↔
    x ∈ PrimeSpectrum.connectedComponentIdeal e
  rw [PrimeSpectrum.mem_connectedComponentIdeal_iff,
    PrimeSpectrum.mem_connectedComponentIdeal_iff]
  have hsymm : (rightTranslationAlgEquiv g).symm
      (PrimeSpectrum.connectedComponentIdempotent e) =
      PrimeSpectrum.connectedComponentIdempotent e :=
    rightTranslationAlgEquiv_symm_connectedComponentIdempotent_eq_self g hg
  have hforward : rightTranslationAlgEquiv g
      (PrimeSpectrum.connectedComponentIdempotent e) =
      PrimeSpectrum.connectedComponentIdempotent e :=
    rightTranslationAlgEquiv_connectedComponentIdempotent_eq_self g hg
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(rightTranslationAlgEquiv g).symm a, ?_⟩
    have h := congrArg (rightTranslationAlgEquiv g).symm ha
    simpa [hsymm] using h
  · rintro ⟨a, ha⟩
    refine ⟨rightTranslationAlgEquiv g a, ?_⟩
    have h := congrArg (rightTranslationAlgEquiv g) ha
    simpa [hforward] using h

/-- Translation by a point in the identity component fixes the ideal cutting out that
component. -/
@[simp]
theorem map_rightTranslationAlgEquiv_connectedComponentIdeal_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    Ideal.map (rightTranslationAlgEquiv g)
        (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  apply Ideal.ext
  intro y
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (rightTranslationAlgEquiv_mem_connectedComponentIdeal_iff g hg).mpr hx
  · intro hy
    refine ⟨(rightTranslationAlgEquiv g).symm y, ?_, ?_⟩
    · exact (rightTranslationAlgEquiv_mem_connectedComponentIdeal_iff g hg).mp
        (by simpa using hy)
    · exact (rightTranslationAlgEquiv g).apply_symm_apply y

end TauCeti.HopfAlgebra
