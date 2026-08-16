/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Idempotents
import TauCeti.Algebra.AlgebraicGroup.Connected.Translation
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Normality of the identity component

Let `H` be a commutative Hopf algebra of finite type over an algebraically closed field. The
connected component of the counit point is preserved by conjugation, so its defining Hopf ideal
is normal.

The proof first constructs the homeomorphism of `Spec H` induced by conjugation by a rational
point, using inversion and right translation. It then tests the universal conjugate of the
component idempotent on algebraically closed points of

```text
H ⊗[k] (H / I),
```

where `I` cuts out the identity component. Conjugation preserves that component, so every such
evaluation is one. The affine Nullstellensatz and idempotence promote this pointwise calculation
to membership in `H ⊗ I`.

## Main declaration

* `TauCeti.HopfAlgebra.isNormal_identityComponentHopfIdeal`: the Hopf ideal defining the identity
  component is stable under conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This supplies the normal-subgroup input for the component-group quotient in Layer 3, “Identity
component `G°` and component group `π₀(G)`”, of the ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]

/-- Inversion on the prime spectrum of a commutative Hopf algebra. -/
private noncomputable def inversionHomeomorph :
    Spec (CommRingCat.of H) ≃ₜ Spec (CommRingCat.of H) :=
  PrimeSpectrum.homeomorphOfRingEquiv
    (antipodeAlgEquiv (R := k) (A := H)).symm.toRingEquiv

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem inversionHomeomorph_apply (x : Spec (CommRingCat.of H)) :
    inversionHomeomorph (k := k) (H := H) x =
      PrimeSpectrum.comap
        ((antipodeAlgEquiv (R := k) (A := H)).toRingEquiv : H →+* H) x := by
  rw [inversionHomeomorph]
  rfl

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem inversionHomeomorph_kernelPoint (g : WithConv (H →ₐ[k] k)) :
    inversionHomeomorph (k := k) (H := H)
        (AlgHom.kernelPoint g.ofConv) = AlgHom.kernelPoint g⁻¹.ofConv := by
  rw [inversionHomeomorph_apply, AlgEquiv.toRingEquiv_toRingHom,
    antipodeAlgEquiv_toRingHom, AlgHom.comap_kernelPoint]
  congr 1

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem rightTranslationHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    rightTranslationHomeomorph h (AlgHom.kernelPoint g.ofConv) =
      AlgHom.kernelPoint (g * h).ofConv := by
  rw [rightTranslationHomeomorph_apply]
  -- `Spec (CommRingCat.of H)` has `PrimeSpectrum H` as its reducible carrier; expose that carrier
  -- and the algebra-hom composition before applying the kernel-point API.
  change PrimeSpectrum.comap
      ((rightTranslationAlgEquiv h).toAlgHom : H →+* H)
        (AlgHom.kernelPoint g.ofConv) = _
  rw [AlgHom.comap_kernelPoint, rightTranslationAlgEquiv_toAlgHom]
  congr 1
  ext x
  -- Composition of algebra homomorphisms must be exposed at application level before the
  -- translation formula can rewrite it.
  change g.ofConv (rightTranslationAlgHom h x) = (g * h).ofConv x
  rw [rightTranslationAlgHom_apply, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [TensorProduct.map_tmul, TensorProduct.rid_tmul,
        Algebra.TensorProduct.lift_tmul, Algebra.smul_def, mul_comm]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- Left translation, expressed as inversion followed by right translation and inversion. -/
private noncomputable def leftTranslationHomeomorph (g : WithConv (H →ₐ[k] k)) :
    Spec (CommRingCat.of H) ≃ₜ Spec (CommRingCat.of H) :=
  (inversionHomeomorph (k := k) (H := H)).trans
    ((rightTranslationHomeomorph g⁻¹).trans
      (inversionHomeomorph (k := k) (H := H)))

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem leftTranslationHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    leftTranslationHomeomorph g (AlgHom.kernelPoint h.ofConv) =
      AlgHom.kernelPoint (g * h).ofConv := by
  have hinv : (h⁻¹ * g⁻¹)⁻¹ = g * h := by group
  rw [leftTranslationHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, inversionHomeomorph_kernelPoint,
    rightTranslationHomeomorph_kernelPoint, inversionHomeomorph_kernelPoint, hinv]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- Conjugation by a rational point, as a homeomorphism of the prime spectrum. -/
private noncomputable def conjugationHomeomorph (g : WithConv (H →ₐ[k] k)) :
    Spec (CommRingCat.of H) ≃ₜ Spec (CommRingCat.of H) :=
  (leftTranslationHomeomorph g).trans (rightTranslationHomeomorph g⁻¹)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem conjugationHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    conjugationHomeomorph g (AlgHom.kernelPoint h.ofConv) =
      AlgHom.kernelPoint (g * h * g⁻¹).ofConv := by
  rw [conjugationHomeomorph, Homeomorph.trans_apply,
    leftTranslationHomeomorph_kernelPoint, rightTranslationHomeomorph_kernelPoint]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem conjugationHomeomorph_image_identityComponent (g : WithConv (H →ₐ[k] k)) :
    conjugationHomeomorph g ''
        connectedComponent (Bialgebra.augmentationPoint k H) =
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  let z : Spec (CommRingCat.of H) := Bialgebra.augmentationPoint k H
  have himage : conjugationHomeomorph g '' connectedComponent z =
      connectedComponent (conjugationHomeomorph g z) := by
    simpa only [connectedComponentIn_univ,
      Set.image_univ_of_surjective (conjugationHomeomorph g).surjective] using
      (conjugationHomeomorph g).image_connectedComponentIn
        (s := Set.univ) (x := z) (Set.mem_univ _)
  have hfix : conjugationHomeomorph g z = z := by
    dsimp only [z]
    rw [conjugationHomeomorph_kernelPoint]
    -- The convolution identity is the counit algebra homomorphism only after unfolding `ofConv`.
    change AlgHom.kernelPoint (g * 1 * g⁻¹).ofConv =
      AlgHom.kernelPoint (1 : WithConv (H →ₐ[k] k)).ofConv
    simp
  rw [himage, hfix]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem kernelPoint_conj_mem_identityComponent
    (g h : WithConv (H →ₐ[k] k))
    (hh : AlgHom.kernelPoint h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    AlgHom.kernelPoint (g * h * g⁻¹).ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  rw [← conjugationHomeomorph_image_identityComponent g]
  exact ⟨AlgHom.kernelPoint h.ofConv, hh, conjugationHomeomorph_kernelPoint g h⟩

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem kernelPoint_comp_componentQuotient_mem_identityComponent
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (f : (H ⧸ PrimeSpectrum.connectedComponentIdeal
      (Bialgebra.augmentationPoint k H)) →ₐ[k] k) :
    AlgHom.kernelPoint
        (f.comp (Ideal.Quotient.mkₐ k
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))) ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let y : PrimeSpectrum (H ⧸ PrimeSpectrum.connectedComponentIdeal z) :=
    AlgHom.kernelPoint f
  have hy := (PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent z y).property
  rw [PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent_apply_coe] at hy
  dsimp only [y, z] at hy
  have hcomap :
      PrimeSpectrum.comap
          (Ideal.Quotient.mk
            (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))
          (AlgHom.kernelPoint f) =
        AlgHom.kernelPoint
          (f.comp (Ideal.Quotient.mkₐ k
            (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))) :=
    AlgHom.comap_kernelPoint f (Ideal.Quotient.mkₐ k
      (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))
  rw [hcomap] at hy
  exact hy

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem map_connectedComponentIdempotent_eq_one_of_mem
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    g.ofConv
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) = 1 := by
  rw [← connectedComponentIdempotent_kernelPoint_eq_augmentationPoint g hg]
  exact AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one g.ofConv

private theorem map_id_quotient_conjugation_componentIdempotent_eq_one
    [LocallyConnectedSpace (PrimeSpectrum H)] :
    let I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
    let q : H →ₐ[k] H ⧸ I := Ideal.Quotient.mkₐ k I
    Algebra.TensorProduct.map (AlgHom.id k H) q
        (conjugationAlgHom (R := k) (H := H)
          (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H))) = 1 := by
  dsimp only
  let I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
  let e := PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)
  let Q := H ⧸ I
  let q : H →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let F : H ⊗[k] H →ₐ[k] H ⊗[k] Q :=
    Algebra.TensorProduct.map (AlgHom.id k H) q
  let _ : Algebra.FiniteType k (H ⊗[k] Q) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := H ⊗[k] Q) inferInstance inferInstance
  have ha_idem : IsIdempotentElem (F (conjugationAlgHom (R := k) (H := H) e)) :=
    ((PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent
      (Bialgebra.augmentationPoint k H)).map
        (conjugationAlgHom (R := k) (H := H)).toRingHom).map F.toRingHom
  apply _root_.eq_of_isNilpotent_sub_of_isIdempotentElem ha_idem IsIdempotentElem.one
  rw [← forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k)]
  intro f
  let g : WithConv (H →ₐ[k] k) :=
    toConv (f.comp (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := Q)))
  let hQ : Q →ₐ[k] k :=
    f.comp (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := Q))
  let h : WithConv (H →ₐ[k] k) := toConv (hQ.comp q)
  have hh : AlgHom.kernelPoint h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
    exact kernelPoint_comp_componentQuotient_mem_identityComponent hQ
  have hconj := kernelPoint_conj_mem_identityComponent g h hh
  have heval := map_connectedComponentIdempotent_eq_one_of_mem (g * h * g⁻¹) hconj
  rw [map_sub, map_one, sub_eq_zero]
  have hproduct : f.comp F =
      Algebra.TensorProduct.productMap g.ofConv h.ofConv := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [F, g, h, hQ, q, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.productMap_apply_tmul]
    rw [← map_mul]
    congr 1
    simp
  rw [← AlgHom.comp_apply, hproduct]
  exact (AlgHom.congr_fun
    (productMap_comp_conjugationAlgHom (R := k) (H := H) g h) e).trans heval

/-- The Hopf ideal cutting out the identity component is normal: its coordinate ideal is stable
under conjugation. Consequently it may be used in the normal fppf quotient construction. -/
theorem isNormal_identityComponentHopfIdeal :
    letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
    letI : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
    (identityComponentHopfIdeal (k := k) (H := H)).IsNormal := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  rw [HopfIdeal.isNormal_iff_conjugation_mem]
  intro x hx
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let I := PrimeSpectrum.connectedComponentIdeal z
  let e := PrimeSpectrum.connectedComponentIdempotent z
  let Q := H ⧸ I
  let q : H →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let F : H ⊗[k] H →ₐ[k] H ⊗[k] Q :=
    Algebra.TensorProduct.map (AlgHom.id k H) q
  have hxI : x ∈ I := by
    exact (mem_identityComponentHopfIdeal (k := k) (H := H)).mp hx
  rw [identityComponentHopfIdeal_toIdeal]
  -- Unfold the Hopf-ideal carrier and the local abbreviation `I` to state the elementwise
  -- conjugation condition in the ideal expected by the kernel lemma below.
  change conjugationAlgHom (R := k) (H := H) x ∈
    HopfIdeal.rightTensorIdeal (R := k) (H := H) I
  obtain ⟨a, rfl⟩ :=
    (PrimeSpectrum.mem_connectedComponentIdeal_iff (x := z) (r := x)).mp hxI
  rw [map_mul]
  apply Ideal.mul_mem_left
  have hker : F (conjugationAlgHom (R := k) (H := H) (1 - e)) = 0 := by
    rw [map_sub, map_one, map_sub, map_one]
    -- Expose the local tensor-map abbreviation at its argument so the pointwise identity rewrites.
    change 1 - F (conjugationAlgHom (R := k) (H := H) e) = 0
    rw [map_id_quotient_conjugation_componentIdempotent_eq_one, sub_self]
  have hmem : conjugationAlgHom (R := k) (H := H) (1 - e) ∈ RingHom.ker F.toRingHom :=
    RingHom.mem_ker.mpr hker
  have hker_eq : RingHom.ker F.toRingHom =
      HopfIdeal.rightTensorIdeal (R := k) (H := H) I := by
    -- Unfold `F` and its ring-hom coercion to match the tensor-product quotient kernel API.
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k H) q) = _
    rw [HopfIdeal.ker_tensorProduct_map_id_quotient]
  rw [hker_eq] at hmem
  exact hmem

end TauCeti.HopfAlgebra
