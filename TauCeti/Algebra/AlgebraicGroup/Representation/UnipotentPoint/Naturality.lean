/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic

/-!
# Naturality of unipotent points in the value algebra

A point of an affine group remains unipotent after extending its value algebra. More precisely,
postcomposing a point `g : H →ₐ[R] A` with `φ : A →ₐ[R] B` extends every point action
from `A ⊗[R] V` to `B ⊗[R] V`, so nilpotence of the difference from the identity is
preserved. If `φ` is injective and `V` is flat over `R`, this extension also reflects
nilpotence. Consequently, over a field, unipotence of a point is invariant under every injective
extension of its value algebra, in particular under field extensions.

The proof uses the existing intertwining identity
`TauCeti.Comodule.rTensor_comp_endOfPoint`. It first upgrades that identity from point actions to
their powers after subtracting the identity. Preservation follows because pure tensors in the
larger scalar extension are scalar multiples of tensors coming from the smaller one; reflection
uses flatness to make the comparison map injective.

## Main declarations

* `TauCeti.Comodule.isNilpotent_endOfPoint_comp`: nilpotence of a point action is preserved by
  postcomposition in the value algebra.
* `TauCeti.Comodule.isNilpotent_endOfPoint_comp_iff_of_injective`: under flatness, an injective
  postcomposition preserves and reflects nilpotence.
* `TauCeti.HopfAlgebra.IsUnipotentPoint.mapValue`: unipotent points remain unipotent after changing
  the value algebra.
* `TauCeti.HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective`: over a field, injective changes
  of the value algebra preserve and reflect unipotence.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies value-field naturality for the geometric unipotence criterion in Layer 5,
"Unipotent groups", of the ReductiveGroups roadmap. It is needed to compare geometric points
across algebraic closures and field extensions.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y

variable {R : Type u} {H : Type v} {V : Type w} {A : Type x} {B : Type y}
variable [CommRing R] [Semiring H] [HopfAlgebra R H]
variable [AddCommGroup V] [Module R V] [Comodule R H V]
variable [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

private theorem rTensor_iterate_endOfPoint_sub_one (g : H →ₐ[R] A) (φ : A →ₐ[R] B)
    (n : ℕ) (z : A ⊗[R] V) :
    LinearMap.rTensor V φ.toLinearMap
        (((endOfPoint V g - 1) ^ n) z) =
      ((endOfPoint V (φ.comp g) - 1) ^ n)
        (LinearMap.rTensor V φ.toLinearMap z) := by
  let q : A ⊗[R] V →ₗ[R] B ⊗[R] V := LinearMap.rTensor V φ.toLinearMap
  let T : Module.End A (A ⊗[R] V) := endOfPoint V g - 1
  let T' : Module.End B (B ⊗[R] V) := endOfPoint V (φ.comp g) - 1
  have hcomm (z : A ⊗[R] V) : q (T z) = T' (q z) := by
    have h := LinearMap.congr_fun (rTensor_comp_endOfPoint (V := V) φ g) z
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply] at h
    -- Unfold the two local endomorphism abbreviations to apply the action intertwining identity.
    change q (endOfPoint V g z - z) = endOfPoint V (φ.comp g) (q z) - q z
    rw [map_sub, h]
  -- Unfold the local abbreviations once; the induction is the generic power-intertwining step.
  change q ((T ^ n) z) = (T' ^ n) (q z)
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hcomm]

/-- Nilpotence of a point action after subtracting the identity is preserved by postcomposition
with a morphism of value algebras. -/
theorem isNilpotent_endOfPoint_comp (g : H →ₐ[R] A) (φ : A →ₐ[R] B)
    (hg : IsNilpotent (endOfPoint V g - 1)) :
    IsNilpotent (endOfPoint V (φ.comp g) - 1) := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  -- `ext` leaves evaluation of the zero endomorphism on the right; normalize that wrapper.
  change ((endOfPoint V (φ.comp g) - 1) ^ n) (b ⊗ₜ[R] v) = 0
  have hiterate := rTensor_iterate_endOfPoint_sub_one (V := V) g φ n (1 ⊗ₜ[R] v)
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hiterate
  calc
    ((endOfPoint V (φ.comp g) - 1) ^ n) (b ⊗ₜ[R] v) =
        ((endOfPoint V (φ.comp g) - 1) ^ n) (b • (1 ⊗ₜ[R] v)) := by
      congr 1
      symm
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = b • ((endOfPoint V (φ.comp g) - 1) ^ n) (1 ⊗ₜ[R] v) := by
      rw [map_smul]
    _ = b • LinearMap.rTensor V φ.toLinearMap
        (((endOfPoint V g - 1) ^ n) (1 ⊗ₜ[R] v)) := by rw [hiterate]
    _ = 0 := by rw [hn]; simp

/-- If the coefficient module is flat, postcomposition with an injective morphism of value
algebras preserves and reflects nilpotence of a point action after subtracting the identity. -/
theorem isNilpotent_endOfPoint_comp_iff_of_injective [Module.Flat R V]
    (g : H →ₐ[R] A) (φ : A →ₐ[R] B) (hφ : Function.Injective φ) :
    IsNilpotent (endOfPoint V (φ.comp g) - 1) ↔
      IsNilpotent (endOfPoint V g - 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := hg
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro z
    apply Module.Flat.rTensor_preserves_injective_linearMap
      φ.toLinearMap hφ
    rw [rTensor_iterate_endOfPoint_sub_one (V := V) g φ, hn]
    simp
  · exact fun hg ↦ isNilpotent_endOfPoint_comp g φ hg

end Comodule

namespace HopfAlgebra

universe u v w x

section General

variable {k : Type u} {H : Type v} {K : Type w} {L : Type x}
variable [CommRing k] [Semiring H] [_root_.HopfAlgebra k H]
variable [CommRing K] [Algebra k K] [CommRing L] [Algebra k L]

/-- A unipotent point remains unipotent after postcomposition with a morphism of value
algebras. -/
theorem IsUnipotentPoint.mapValue {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) (φ : K →ₐ[k] L) :
    IsUnipotentPoint (AlgHom.mapValue (H := H) φ g) := by
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at hg ⊢
  intro M
  rw [AlgHom.mapValue_apply, WithConv.ofConv_toConv]
  exact Comodule.isNilpotent_endOfPoint_comp g.ofConv φ (hg M)

end General

section Injective

variable {k : Type u} {H : Type v} {K : Type w} {L : Type x}
variable [Field k] [Semiring H] [_root_.HopfAlgebra k H]
variable [CommRing K] [Algebra k K] [CommRing L] [Algebra k L]

/-- Over a field, postcomposition with an injective morphism of value algebras preserves and
reflects unipotence of points. -/
theorem isUnipotentPoint_mapValue_iff_of_injective
    (g : WithConv (H →ₐ[k] K)) (φ : K →ₐ[k] L) (hφ : Function.Injective φ) :
    IsUnipotentPoint (AlgHom.mapValue (H := H) φ g) ↔ IsUnipotentPoint g := by
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one,
    isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  apply forall_congr'
  intro M
  rw [AlgHom.mapValue_apply, WithConv.ofConv_toConv]
  exact Comodule.isNilpotent_endOfPoint_comp_iff_of_injective g.ofConv φ hφ

end Injective

section FieldExtension

variable {k : Type u} {H : Type v} {K : Type w} {L : Type x}
variable [Field k] [Semiring H] [_root_.HopfAlgebra k H]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]

/-- Unipotence of a point is invariant under extension of its value field. -/
@[simp]
theorem isUnipotentPoint_toConv_comp_iff (g : WithConv (H →ₐ[k] K))
    (φ : K →ₐ[k] L) :
    IsUnipotentPoint (WithConv.toConv (φ.comp g.ofConv)) ↔ IsUnipotentPoint g := by
  simpa only [AlgHom.mapValue_apply] using
    isUnipotentPoint_mapValue_iff_of_injective g φ φ.injective

end FieldExtension

end HopfAlgebra

end TauCeti
