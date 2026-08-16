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

* `TauCeti.HopfAlgebra.identityComponentHopfIdeal_isNormal`: the Hopf ideal defining the identity
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

/-- The prime of `H` cut out by a `k`-valued point, with the carrier stated directly as
`PrimeSpectrum H` rather than through the definitionally equal scheme carrier. -/
private def kernelPrime {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : A →ₐ[K] K) : PrimeSpectrum A :=
  PrimeSpectrum.comap (f : A →+* K) (IsLocalRing.closedPoint K)

/-- Inversion on the prime spectrum of a commutative Hopf algebra. -/
private noncomputable def inversionHomeomorph :
    PrimeSpectrum H ≃ₜ PrimeSpectrum H :=
  PrimeSpectrum.homeomorphOfRingEquiv
    (antipodeAlgEquiv (R := k) (A := H)).symm.toRingEquiv

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem inversionHomeomorph_kernelPoint (g : WithConv (H →ₐ[k] k)) :
    inversionHomeomorph (k := k) (H := H)
        (kernelPrime g.ofConv) = kernelPrime g⁻¹.ofConv := by
  change PrimeSpectrum.comap
      ((antipodeAlgEquiv (R := k) (A := H)).toRingEquiv : H →+* H)
        (kernelPrime g.ofConv) = kernelPrime g⁻¹.ofConv
  rw [AlgEquiv.toRingEquiv_toRingHom, antipodeAlgEquiv_toRingHom]
  rw [kernelPrime, kernelPrime]
  calc
    PrimeSpectrum.comap
          (_root_.HopfAlgebra.antipodeAlgHom k H : H →+* H)
          (PrimeSpectrum.comap (g.ofConv : H →+* k) (IsLocalRing.closedPoint k)) =
        PrimeSpectrum.comap
          ((g.ofConv : H →+* k).comp
            (_root_.HopfAlgebra.antipodeAlgHom k H : H →+* H))
          (IsLocalRing.closedPoint k) :=
      (PrimeSpectrum.comap_comp_apply _ _ _).symm
    _ = PrimeSpectrum.comap (g⁻¹.ofConv : H →+* k) (IsLocalRing.closedPoint k) := by
      congr 1

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- Right translation on `PrimeSpectrum H`, without the scheme carrier wrapper. -/
private noncomputable def rightTranslationPrimeHomeomorph (g : WithConv (H →ₐ[k] k)) :
    PrimeSpectrum H ≃ₜ PrimeSpectrum H :=
  PrimeSpectrum.homeomorphOfRingEquiv (rightTranslationAlgEquiv g).symm.toRingEquiv

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem rightTranslationPrimeHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    rightTranslationPrimeHomeomorph h (kernelPrime g.ofConv) =
      kernelPrime (g * h).ofConv := by
  change PrimeSpectrum.comap
      ((rightTranslationAlgEquiv h).toAlgHom : H →+* H)
        (kernelPrime g.ofConv) = _
  rw [rightTranslationAlgEquiv_toAlgHom]
  rw [kernelPrime, kernelPrime]
  calc
    PrimeSpectrum.comap (rightTranslationAlgHom h : H →+* H)
          (PrimeSpectrum.comap (g.ofConv : H →+* k) (IsLocalRing.closedPoint k)) =
        PrimeSpectrum.comap
          ((g.ofConv : H →+* k).comp (rightTranslationAlgHom h : H →+* H))
          (IsLocalRing.closedPoint k) := (PrimeSpectrum.comap_comp_apply _ _ _).symm
    _ = PrimeSpectrum.comap ((g * h).ofConv : H →+* k) (IsLocalRing.closedPoint k) := by
      congr 1
      ext x
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
    PrimeSpectrum H ≃ₜ PrimeSpectrum H :=
  (inversionHomeomorph (k := k) (H := H)).trans
    ((rightTranslationPrimeHomeomorph g⁻¹).trans
      (inversionHomeomorph (k := k) (H := H)))

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem leftTranslationHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    leftTranslationHomeomorph g (kernelPrime h.ofConv) =
      kernelPrime (g * h).ofConv := by
  rw [leftTranslationHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply, inversionHomeomorph_kernelPoint,
    rightTranslationPrimeHomeomorph_kernelPoint, inversionHomeomorph_kernelPoint]
  have hinv : (h⁻¹ * g⁻¹)⁻¹ = g * h := by group
  rw [hinv]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- Conjugation by a rational point, as a homeomorphism of the prime spectrum. -/
private noncomputable def conjugationHomeomorph (g : WithConv (H →ₐ[k] k)) :
    PrimeSpectrum H ≃ₜ PrimeSpectrum H :=
  (leftTranslationHomeomorph g).trans (rightTranslationPrimeHomeomorph g⁻¹)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem conjugationHomeomorph_kernelPoint
    (g h : WithConv (H →ₐ[k] k)) :
    conjugationHomeomorph g (kernelPrime h.ofConv) =
      kernelPrime (g * h * g⁻¹).ofConv := by
  rw [conjugationHomeomorph, Homeomorph.trans_apply,
    leftTranslationHomeomorph_kernelPoint, rightTranslationPrimeHomeomorph_kernelPoint]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem conjugationHomeomorph_image_identityComponent (g : WithConv (H →ₐ[k] k)) :
    conjugationHomeomorph g ''
        connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H) =
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H) := by
  let z : PrimeSpectrum H := kernelPrime (_root_.Bialgebra.counitAlgHom k H)
  have hz : (Bialgebra.augmentationPoint k H : PrimeSpectrum H) = z := by
    apply PrimeSpectrum.ext
    change (AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)).asIdeal = z.asIdeal
    rw [AlgHom.kernelPoint_asIdeal]
    change RingHom.ker (_root_.Bialgebra.counitAlgHom k H : H →+* k) = z.asIdeal
    dsimp only [z, kernelPrime]
    rw [PrimeSpectrum.comap_asIdeal]
    dsimp only [IsLocalRing.closedPoint]
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [hz]
  have himage : conjugationHomeomorph g '' connectedComponent z =
      connectedComponent (conjugationHomeomorph g z) := by
    simpa only [connectedComponentIn_univ,
      Set.image_univ_of_surjective (conjugationHomeomorph g).surjective] using
      (conjugationHomeomorph g).image_connectedComponentIn
        (s := Set.univ) (x := z) (Set.mem_univ _)
  have hfix : conjugationHomeomorph g z = z := by
    dsimp only [z]
    rw [conjugationHomeomorph_kernelPoint]
    change kernelPrime (g * 1 * g⁻¹).ofConv =
      kernelPrime (1 : WithConv (H →ₐ[k] k)).ofConv
    simp
  rw [himage, hfix]
  rfl

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem kernelPoint_conj_mem_identityComponent
    (g h : WithConv (H →ₐ[k] k))
    (hh : kernelPrime h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H)) :
    kernelPrime (g * h * g⁻¹).ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H) := by
  rw [← conjugationHomeomorph_image_identityComponent g]
  exact ⟨kernelPrime h.ofConv, hh, conjugationHomeomorph_kernelPoint g h⟩

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem kernelPoint_comp_componentQuotient_mem_identityComponent
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (f : (H ⧸ PrimeSpectrum.connectedComponentIdeal
      (Bialgebra.augmentationPoint k H)) →ₐ[k] k) :
    kernelPrime
        (f.comp (Ideal.Quotient.mkₐ k
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))) ∈
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H) := by
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let y : PrimeSpectrum (H ⧸ PrimeSpectrum.connectedComponentIdeal z) :=
    kernelPrime f
  have hy := (PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent z y).property
  rw [PrimeSpectrum.primeSpectrumQuotientHomeomorphConnectedComponent_apply_coe] at hy
  change PrimeSpectrum.comap
      (Ideal.Quotient.mk (PrimeSpectrum.connectedComponentIdeal z)) (kernelPrime f) ∈
    connectedComponent z at hy
  rw [kernelPrime, ← PrimeSpectrum.comap_comp_apply] at hy
  exact hy

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem map_connectedComponentIdempotent_eq_one_of_mem
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (g : WithConv (H →ₐ[k] k))
    (hg : kernelPrime g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H)) :
    g.ofConv
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) = 1 := by
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let p : PrimeSpectrum H := kernelPrime g.ofConv
  have hpz : connectedComponent p = connectedComponent z := (connectedComponent_eq hg).symm
  have he : PrimeSpectrum.connectedComponentIdempotent p =
      PrimeSpectrum.connectedComponentIdempotent z := by
    apply (PrimeSpectrum.eq_connectedComponentIdempotent_iff
      (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p) z).mpr
    rw [PrimeSpectrum.basicOpen_connectedComponentIdempotent]
    exact hpz
  rw [← he]
  have hnot : PrimeSpectrum.connectedComponentIdempotent p ∉ p.asIdeal :=
    PrimeSpectrum.connectedComponentIdempotent_notMem_asIdeal p
  have hpker : p.asIdeal = RingHom.ker (g.ofConv : H →+* k) := by
    change Ideal.comap (g.ofConv : H →+* k) (IsLocalRing.maximalIdeal k) =
      RingHom.ker (g.ofConv : H →+* k)
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [hpker, RingHom.mem_ker] at hnot
  have hidem : IsIdempotentElem
      (g.ofConv (PrimeSpectrum.connectedComponentIdempotent p)) :=
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p).map g.ofConv.toRingHom
  exact (IsIdempotentElem.iff_eq_zero_or_one.mp hidem).resolve_left hnot

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
  have hh : kernelPrime h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H : PrimeSpectrum H) := by
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
theorem identityComponentHopfIdeal_isNormal :
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
  change conjugationAlgHom (R := k) (H := H) x ∈
    HopfIdeal.rightTensorIdeal (R := k) (H := H) I
  obtain ⟨a, rfl⟩ :=
    (PrimeSpectrum.mem_connectedComponentIdeal_iff (x := z) (r := x)).mp hxI
  rw [map_mul]
  apply Ideal.mul_mem_left
  have hker : F (conjugationAlgHom (R := k) (H := H) (1 - e)) = 0 := by
    rw [map_sub, map_one, map_sub, map_one]
    change 1 - F (conjugationAlgHom (R := k) (H := H) e) = 0
    rw [map_id_quotient_conjugation_componentIdempotent_eq_one, sub_self]
  have hmem : conjugationAlgHom (R := k) (H := H) (1 - e) ∈ RingHom.ker F.toRingHom :=
    RingHom.mem_ker.mpr hker
  have hker_eq : RingHom.ker F.toRingHom =
      HopfIdeal.rightTensorIdeal (R := k) (H := H) I := by
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k H) q) = _
    rw [HopfIdeal.ker_tensorProduct_map_id_quotient]
  rw [hker_eq] at hmem
  exact hmem

end TauCeti.HopfAlgebra
