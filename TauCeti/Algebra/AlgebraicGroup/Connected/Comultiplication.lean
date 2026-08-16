/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.IdentityComponent
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.Translation
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent
import TauCeti.RingTheory.FiniteType.PointSeparation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Idempotents

/-!
# The identity component as a Hopf ideal

Let `H` be a commutative Hopf algebra of finite type over an algebraically closed field.  The
connected component of the counit point is stable under multiplication: equivalently, the
comultiplication of the ideal cutting out that component lies in `I ⊗ H + H ⊗ I`.  Together
with the counit and antipode results already available for this ideal, this packages the identity
component as a `HopfIdeal`.

The multiplication argument is carried out on algebraically closed points of the component
quotient.  Translation stability shows that the product of two such points is still in the
identity component.  The affine Nullstellensatz then promotes this pointwise statement to the
required identity in the tensor square; tensor-product right exactness identifies its kernel with
`I ⊗ H + H ⊗ I`.

The algebraically closed hypothesis is the natural one for the geometric identity component in
the reductive-groups roadmap.  Descent of this construction to the ground field and construction
of the component group are separate steps.

## Main declarations

* `TauCeti.HopfAlgebra.comul_mem_connectedComponentIdeal_augmentationPoint`: the component ideal
  is stable under comultiplication.
* `TauCeti.HopfAlgebra.identityComponentHopfIdeal`: the Hopf ideal cutting out the identity
  component.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This advances Layer 3, "Identity component `G°` and component group `π₀(G)`", of the
ReductiveGroups roadmap.  The quotient Hopf algebra now gives the identity component over an
algebraically closed field; descent, geometric connectedness over a general field, and the finite
étale component group remain.
-/

public section

open AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]

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
private theorem kernelPoint_mul_mem_connectedComponent_augmentationPoint
    (g h : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H))
    (hh : AlgHom.kernelPoint h.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    AlgHom.kernelPoint (g * h).ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  have himage :=
    rightTranslationHomeomorph_image_connectedComponent_augmentationPoint_eq_self h hh
  rw [← himage]
  exact ⟨AlgHom.kernelPoint g.ofConv, hg, rightTranslationHomeomorph_kernelPoint g h⟩

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem map_connectedComponentIdempotent_augmentationPoint_eq_one_of_mem
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    g.ofConv
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) = 1 := by
  let p : PrimeSpectrum H := AlgHom.kernelPoint g.ofConv
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let e := PrimeSpectrum.connectedComponentIdempotent z
  -- Reduce the `Spec` carrier and the local abbreviations once so that the basic-open
  -- characterization can compare the component membership with ideal membership.
  change p ∈ connectedComponent z at hg
  have hnot : e ∉ p.asIdeal := by
    have hpopen : p ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) := by
      rw [show e = PrimeSpectrum.connectedComponentIdempotent z from rfl,
        PrimeSpectrum.basicOpen_connectedComponentIdempotent]
      exact hg
    exact (PrimeSpectrum.mem_basicOpen e p).mp hpopen
  change e ∉ (AlgHom.kernelPoint g.ofConv).asIdeal at hnot
  rw [AlgHom.kernelPoint_asIdeal, RingHom.mem_ker] at hnot
  have he : IsIdempotentElem (g.ofConv e) :=
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent
      (Bialgebra.augmentationPoint k H)).map g.ofConv.toRingHom
  exact (IsIdempotentElem.iff_eq_zero_or_one.mp he).resolve_left hnot

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem map_tensorSquare_comul_apply
    {B : Type v} [CommRing B] [Algebra k B]
    (q : H →ₐ[k] B) (f : (B ⊗[k] B) →ₐ[k] k) (x : H) :
    f (Algebra.TensorProduct.map q q (Coalgebra.comul (R := k) x)) =
      ((WithConv.toConv
          ((f.comp (Algebra.TensorProduct.includeLeft
            (R := k) (S := k) (A := B) (B := B))).comp q)) *
        WithConv.toConv
          ((f.comp (Algebra.TensorProduct.includeRight
            (R := k) (A := B) (B := B))).comp q)).ofConv x := by
  rw [AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      -- The convolution wrappers reduce to the two restrictions of `f` only after application.
      change f (q x ⊗ₜ[k] q y) = f (q x ⊗ₜ[k] 1) * f (1 ⊗ₜ[k] q y)
      rw [← map_mul]
      congr 1
      simp

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem kernelPoint_comp_quotient_mem_connectedComponent
    [LocallyConnectedSpace (PrimeSpectrum H)]
    (f : (H ⧸ PrimeSpectrum.connectedComponentIdeal
      (Bialgebra.augmentationPoint k H)) →ₐ[k] k) :
    AlgHom.kernelPoint
        (f.comp (Ideal.Quotient.mkₐ k
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))) ∈
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let I := PrimeSpectrum.connectedComponentIdeal z
  let p : PrimeSpectrum H := AlgHom.kernelPoint
    (f.comp (Ideal.Quotient.mkₐ k I))
  -- Reduce the `Spec` carrier and kernel-point wrapper before using the zero-locus criterion.
  change p ∈ connectedComponent z
  rw [← PrimeSpectrum.zeroLocus_connectedComponentIdeal]
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  change x ∈ I at hx
  change x ∈ (AlgHom.kernelPoint
    (f.comp (Ideal.Quotient.mkₐ k I))).asIdeal
  rw [AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
  change f (Ideal.Quotient.mk I x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem map_tensorSquare_quotient_comul_connectedComponentIdempotent_eq_one
    [LocallyConnectedSpace (PrimeSpectrum H)] :
    Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ k
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))
        (Ideal.Quotient.mkₐ k
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)))
        (Coalgebra.comul (R := k)
          (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H))) = 1 := by
  let I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
  let e := PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)
  let B := H ⧸ I
  let q : H →ₐ[k] B := Ideal.Quotient.mkₐ k I
  let F : (H ⊗[k] H) →ₐ[k] (B ⊗[k] B) := Algebra.TensorProduct.map q q
  let _ : Algebra.FiniteType k (B ⊗[k] B) :=
    Algebra.FiniteType.trans (R := k) (S := B) (A := B ⊗[k] B) inferInstance inferInstance
  have ha_idem : IsIdempotentElem (F (Coalgebra.comul (R := k) e)) := by
    exact ((PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent
      (Bialgebra.augmentationPoint k H)).map
        (_root_.Bialgebra.comulAlgHom k H).toRingHom).map F.toRingHom
  have ha_eq_one : F (Coalgebra.comul (R := k) e) = 1 := by
    apply _root_.eq_of_isNilpotent_sub_of_isIdempotentElem
      ha_idem IsIdempotentElem.one
    rw [← forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k)]
    intro f
    let f₁ : B →ₐ[k] k :=
      f.comp (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := B) (B := B))
    let f₂ : B →ₐ[k] k :=
      f.comp (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := B))
    let g : WithConv (H →ₐ[k] k) := WithConv.toConv (f₁.comp q)
    let h : WithConv (H →ₐ[k] k) := WithConv.toConv (f₂.comp q)
    have hg : AlgHom.kernelPoint g.ofConv ∈
        connectedComponent (Bialgebra.augmentationPoint k H) := by
      exact kernelPoint_comp_quotient_mem_connectedComponent f₁
    have hh : AlgHom.kernelPoint h.ofConv ∈
        connectedComponent (Bialgebra.augmentationPoint k H) := by
      exact kernelPoint_comp_quotient_mem_connectedComponent f₂
    have hmul := kernelPoint_mul_mem_connectedComponent_augmentationPoint g h hg hh
    have heval :=
      map_connectedComponentIdempotent_augmentationPoint_eq_one_of_mem (g * h) hmul
    rw [map_sub, map_one, sub_eq_zero]
    rw [map_tensorSquare_comul_apply q f e]
    exact heval
  -- Expose the local quotient and tensor-square abbreviations to return the public expression.
  change F (Coalgebra.comul (R := k) e) = 1
  exact ha_eq_one

private theorem comul_one_sub_connectedComponentIdempotent_mem
    [LocallyConnectedSpace (PrimeSpectrum H)] :
    Coalgebra.comul (R := k)
        (1 - PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) ∈
      HopfIdeal.leftTensorIdeal (R := k) (H := H)
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) ⊔
        HopfIdeal.rightTensorIdeal (R := k) (H := H)
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) := by
  let I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
  let e := PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)
  let B := H ⧸ I
  let q : H →ₐ[k] B := Ideal.Quotient.mkₐ k I
  let F : (H ⊗[k] H) →ₐ[k] (B ⊗[k] B) := Algebra.TensorProduct.map q q
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective k I
  have ha_eq_one : F (Coalgebra.comul (R := k) e) = 1 :=
    map_tensorSquare_quotient_comul_connectedComponentIdempotent_eq_one
  have hker : Coalgebra.comul (R := k) (1 - e) ∈ RingHom.ker F.toRingHom := by
    rw [RingHom.mem_ker]
    rw [map_sub, Bialgebra.comul_one, map_sub, map_one]
    -- The ring-hom coercion of `F` blocks rewriting by the named equality until application is
    -- exposed.
    change 1 - F (Coalgebra.comul (R := k) e) = 0
    rw [ha_eq_one, sub_self]
  have hker_eq : RingHom.ker F.toRingHom =
      HopfIdeal.leftTensorIdeal (R := k) (H := H) I ⊔
        HopfIdeal.rightTensorIdeal (R := k) (H := H) I := by
    have hqker : RingHom.ker q = I := by
      -- Unfold the local quotient-map abbreviation for Mathlib's kernel theorem.
      change RingHom.ker (Ideal.Quotient.mkₐ k I) = I
      exact Ideal.Quotient.mkₐ_ker k I
    -- Unfold the local tensor-square map abbreviation before tensor-product exactness rewrites it.
    change RingHom.ker (Algebra.TensorProduct.map q q) = _
    rw [Algebra.TensorProduct.map_ker (f := q) (g := q) hq hq, hqker,
      HopfIdeal.leftTensorIdeal_def, HopfIdeal.rightTensorIdeal_def]
    simp only [AlgHom.toRingHom_eq_coe]
    apply congr_arg₂ (fun J K : Ideal (H ⊗[k] H) ↦ J ⊔ K) <;> rfl
  rwa [hker_eq] at hker

/-- The ideal cutting out the augmentation point's connected component is stable under
comultiplication. -/
theorem comul_mem_connectedComponentIdeal_augmentationPoint
    [LocallyConnectedSpace (PrimeSpectrum H)] {x : H}
    (hx : x ∈ PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) :
    Coalgebra.comul (R := k) x ∈
      HopfIdeal.leftTensorIdeal (R := k) (H := H)
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) ⊔
        HopfIdeal.rightTensorIdeal (R := k) (H := H)
          (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) := by
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let I := PrimeSpectrum.connectedComponentIdeal z
  let e := PrimeSpectrum.connectedComponentIdempotent z
  -- Expose the local component ideal so its principal-generator characterization can rewrite.
  change x ∈ I at hx
  change Coalgebra.comul (R := k) x ∈
    HopfIdeal.leftTensorIdeal (R := k) (H := H) I ⊔
      HopfIdeal.rightTensorIdeal (R := k) (H := H) I
  rw [PrimeSpectrum.mem_connectedComponentIdeal_iff] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [Bialgebra.comul_mul]
  exact Ideal.mul_mem_left _ _
    (comul_one_sub_connectedComponentIdempotent_mem (k := k) (H := H))

/-- The Hopf ideal cutting out the connected component of the identity in a finite-type affine
group over an algebraically closed field. -/
@[expose] noncomputable def identityComponentHopfIdeal
    [LocallyConnectedSpace (PrimeSpectrum H)] : HopfIdeal k H :=
  HopfIdeal.ofIdeal
    (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H))
    (fun _ hx ↦ comul_mem_connectedComponentIdeal_augmentationPoint hx)
    (fun x hx ↦ by
      have hx' : x ∈ RingHom.ker
          (_root_.Bialgebra.counitAlgHom k H).toRingHom :=
        TauCeti.AlgHom.connectedComponentIdeal_kernelPoint_le_ker
          (_root_.Bialgebra.counitAlgHom k H) hx
      rw [← Bialgebra.counitAlgHom_apply]
      exact RingHom.mem_ker.mp hx')
    (fun _ hx ↦
      (antipode_mem_connectedComponentIdeal_augmentationPoint_iff (k := k)).mpr hx)

/-- The underlying ideal of the identity-component Hopf ideal is the ideal generated by the
complement of the augmentation point's component idempotent. -/
@[simp]
theorem identityComponentHopfIdeal_toIdeal
    [LocallyConnectedSpace (PrimeSpectrum H)] :
    (identityComponentHopfIdeal (k := k) (H := H)).toIdeal =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) :=
  rfl

/-- Membership in the identity-component Hopf ideal is membership in the ideal cutting out the
augmentation point's connected component. -/
@[simp]
theorem mem_identityComponentHopfIdeal
    [LocallyConnectedSpace (PrimeSpectrum H)] {x : H} :
    x ∈ identityComponentHopfIdeal (k := k) (H := H) ↔
      x ∈ PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) :=
  Iff.rfl

end TauCeti.HopfAlgebra
