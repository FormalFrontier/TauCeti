/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
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
    exact TauCeti.Homeomorph.image_connectedComponent (conjugationHomeomorph g) z
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
  apply eq_one_of_isIdempotentElem_of_forall_algHom_apply_eq_one
    (k := k) (A := H ⊗[k] Q) (K := k) ha_idem
  intro f
  let g : WithConv (H →ₐ[k] k) :=
    toConv (f.comp (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := Q)))
  let hQ : Q →ₐ[k] k :=
    f.comp (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := Q))
  let h : WithConv (H →ₐ[k] k) := toConv (hQ.comp q)
  have hh : AlgHom.kernelPoint h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
    exact AlgHom.kernelPoint_comp_connectedComponentQuotient_mem
      (Bialgebra.augmentationPoint k H) hQ
  have hconj := kernelPoint_conj_mem_identityComponent g h hh
  have heval := map_connectedComponentIdempotent_augmentationPoint_eq_one_of_mem
    (g * h * g⁻¹) hconj
  have hleft : (f.comp F).comp Algebra.TensorProduct.includeLeft = g.ofConv := by
    simp [F, g, AlgHom.comp_assoc]
  have hright : (f.comp F).comp Algebra.TensorProduct.includeRight = h.ofConv := by
    simp [F, h, hQ, q, AlgHom.comp_assoc]
  have hcomp := AlgHom.congr_fun (comp_conjugationAlgHom (f.comp F)) e
  rw [hleft, hright, toConv_ofConv] at hcomp
  exact hcomp.trans heval

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
