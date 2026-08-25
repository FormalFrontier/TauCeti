/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Faithfully flat descent for the functor of points

Let `A → B` be a faithfully flat extension of commutative `R`-algebras. The two maps
`B ⇉ B ⊗[A] B` give two restriction maps on the `B`-points represented by a Hopf algebra `H`.
This file proves that the `A`-points are exactly the `B`-points on which those restrictions agree,
as an equivalence of groups. The coordinate algebra need not be commutative for this algebraic
descent statement; the affine-group-scheme application specializes to commutative `H`.

The proof uses Mathlib's effective-descent theorem
`Algebra.IsEffective.of_faithfullyFlat`: the equalizer of
`B ⇉ B ⊗[A] B` is the image of `A`. Rather than repeating its elementwise argument for
points, we package that equalizer as an algebra equivalence and precompose algebra maps out of
`H`. The resulting equivalence respects convolution because it is induced by postcomposition in
the value algebra.

This is the affine, group-valued faithfully flat descent statement needed by the fppf sheaf and
quotient lane of the reductive-groups roadmap. The finite-presentation part of an fppf cover is
not needed for descent itself, so the result is stated at the natural faithfully flat level.

## Main declarations

* `TauCeti.AlgHom.descentSubgroup`: the subgroup of `B`-points satisfying the
  equalizer condition over `B ⊗[A] B`.
* `TauCeti.AlgHom.faithfullyFlatDescentMulEquiv`: `A`-points are equivalent to that descent
  subgroup.

## References

This is the affine representable case of faithfully flat descent. The algebraic input is
Mathlib's `Algebra.IsEffective.of_faithfullyFlat`, following the standard Amitsur equalizer
`A → B ⇉ B ⊗[A] B`.
-/

public section

open Algebra.TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

namespace AlgHom

universe u v w x

variable {R : Type u} {H : Type v} (A : Type w) (B : Type x)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

section CommSemiring

variable [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B]

private noncomputable def faithfullyFlatDescentLeft : B →ₐ[R] (B ⊗[A] B) :=
  (includeLeft : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

private noncomputable def faithfullyFlatDescentRight : B →ₐ[R] (B ⊗[A] B) :=
  (includeRight : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

/-- The subgroup of `B`-points satisfying the descent equalizer condition along `A → B`.

A point `f : H →ₐ[R] B` belongs to this subgroup exactly when its two postcompositions
`H →ₐ[R] B ⇉ B ⊗[A] B` agree. The subgroup structure comes from functoriality of
convolution in the value algebra. -/
noncomputable def descentSubgroup :
    Subgroup (WithConv (H →ₐ[R] B)) :=
  MonoidHom.eqLocus (mapValue (H := H) (faithfullyFlatDescentLeft (R := R) A (B := B)))
    (mapValue (H := H) (faithfullyFlatDescentRight (R := R) A (B := B)))

private theorem mem_descentSubgroup_iff_maps (f : WithConv (H →ₐ[R] B)) :
    f ∈ descentSubgroup (R := R) (H := H) A B ↔
      mapValue (H := H) (faithfullyFlatDescentLeft (R := R) A (B := B)) f =
        mapValue (H := H) (faithfullyFlatDescentRight (R := R) A (B := B)) f :=
  Iff.rfl

/-- Pointwise form of the descent equalizer condition. -/
@[simp]
theorem mem_descentSubgroup_iff_apply (f : WithConv (H →ₐ[R] B)) :
    f ∈ descentSubgroup (R := R) (H := H) A B ↔
      ∀ h, (includeLeft (R := A) (S := A) (A := B) (B := B)) (f h) =
        (includeRight (R := A) (A := B) (B := B)) (f h) := by
  rw [mem_descentSubgroup_iff_maps]
  constructor
  · intro hf h
    exact DFunLike.congr_fun (congr_arg WithConv.ofConv hf) h
  · intro hf
    apply WithConv.toConv_injective
    ext h
    exact hf h

end CommSemiring

section CommRing

variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B] [Module.FaithfullyFlat A B]

private noncomputable def descentEqualizerHom :
    A →ₐ[R] AlgHom.equalizer (faithfullyFlatDescentLeft (R := R) A (B := B))
      (faithfullyFlatDescentRight (R := R) A (B := B)) :=
  AlgHom.codRestrict (IsScalarTower.toAlgHom R A B) _ fun a => by
    simp [faithfullyFlatDescentLeft, faithfullyFlatDescentRight, tmul_one_eq_one_tmul]

omit [Module.FaithfullyFlat A B] in
@[simp]
private theorem descentEqualizerHom_apply_val (a : A) :
    (descentEqualizerHom (R := R) A B a : B) = algebraMap A B a :=
  rfl

omit [Module.FaithfullyFlat A B] in
private theorem mem_descentEqualizer_iff_eqLocus (b : B) :
    b ∈ AlgHom.equalizer (faithfullyFlatDescentLeft (R := R) A (B := B))
      (faithfullyFlatDescentRight (R := R) A (B := B)) ↔
        b ∈ includeLeftRingHom.eqLocus includeRight.toRingHom (S := B ⊗[A] B) :=
  by
    rw [AlgHom.mem_equalizer, RingHom.mem_eqLocus]
    simp only [faithfullyFlatDescentLeft, faithfullyFlatDescentRight,
      AlgHom.restrictScalars_apply, includeLeft_apply, includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, includeRight_apply]

private theorem descentEqualizerHom_bijective :
    Function.Bijective (descentEqualizerHom (R := R) A B) := by
  constructor
  · intro a b hab
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [descentEqualizerHom_apply_val] using congr_arg Subtype.val hab
  · rintro ⟨b, hb⟩
    have hb' :
        b ∈ includeLeftRingHom.eqLocus includeRight.toRingHom (S := B ⊗[A] B) :=
      (mem_descentEqualizer_iff_eqLocus (R := R) A B b).mp hb
    have hb'' : b ∈ Set.range (algebraMap A B) := by
      rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat A B)]
      exact hb'
    obtain ⟨a, ha⟩ := hb''
    refine ⟨a, Subtype.ext ?_⟩
    simpa only [descentEqualizerHom_apply_val] using ha

private noncomputable def descentEqualizerEquiv :
    A ≃ₐ[R] AlgHom.equalizer (faithfullyFlatDescentLeft (R := R) A (B := B))
      (faithfullyFlatDescentRight (R := R) A (B := B)) :=
  AlgEquiv.ofBijective (descentEqualizerHom (R := R) A B)
    (descentEqualizerHom_bijective (R := R) A B)

@[simp]
private theorem descentEqualizerEquiv_apply_val (a : A) :
    (descentEqualizerEquiv (R := R) A B a : B) = algebraMap A B a := by
  rw [descentEqualizerEquiv, AlgEquiv.ofBijective_apply]
  exact descentEqualizerHom_apply_val (R := R) A B a

private noncomputable def faithfullyFlatDescentHom :
    WithConv (H →ₐ[R] A) →* descentSubgroup (R := R) (H := H) A B :=
  (mapValue (H := H) (IsScalarTower.toAlgHom R A B)).codRestrict _ fun f => by
    rw [mem_descentSubgroup_iff_apply]
    intro h
    simp

omit [Module.FaithfullyFlat A B] in
private theorem faithfullyFlatDescentHom_apply (f : WithConv (H →ₐ[R] A)) :
    (faithfullyFlatDescentHom (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      mapValue (H := H) (IsScalarTower.toAlgHom R A B) f :=
  rfl

omit [Module.FaithfullyFlat A B] in
@[simp]
private theorem faithfullyFlatDescentHom_apply_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    (faithfullyFlatDescentHom (R := R) (H := H) A B f :
      descentSubgroup (R := R) (H := H) A B).1.ofConv h =
        algebraMap A B (f.ofConv h) := by
  rw [faithfullyFlatDescentHom_apply, mapValue_apply, toConv_ofConv]
  rfl

private theorem faithfullyFlatDescentHom_bijective :
    Function.Bijective (faithfullyFlatDescentHom (R := R) (H := H) A B) := by
  constructor
  · intro f g hfg
    apply WithConv.ofConv_injective
    ext h
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [faithfullyFlatDescentHom_apply_apply] using
      congr_arg (fun p : descentSubgroup (R := R) (H := H) A B => p.1.ofConv h) hfg
  · intro f
    let f' : H →ₐ[R]
        AlgHom.equalizer (faithfullyFlatDescentLeft (R := R) A (B := B))
          (faithfullyFlatDescentRight (R := R) A (B := B)) :=
      AlgHom.codRestrict f.1.ofConv _ fun h =>
        (mem_descentSubgroup_iff_apply (R := R) A B f.1).mp f.2 h
    let g : H →ₐ[R] A := (descentEqualizerEquiv (R := R) A B).symm.toAlgHom.comp f'
    refine ⟨toConv g, Subtype.ext ?_⟩
    apply WithConv.ofConv_injective
    ext h
    rw [faithfullyFlatDescentHom_apply_apply, ofConv_toConv]
    have hg : g h = (descentEqualizerEquiv (R := R) A B).symm (f' h) := by
      exact AlgHom.comp_apply _ _ h
    rw [hg]
    have hdesc :=
      congr_arg Subtype.val ((descentEqualizerEquiv (R := R) A B).apply_symm_apply (f' h))
    rw [descentEqualizerEquiv_apply_val] at hdesc
    have hf' : (f' h : B) = f.1.ofConv h := by
      dsimp only [f']
      exact AlgHom.coe_codRestrict f.1.ofConv _ _ h
    rw [hf'] at hdesc
    exact hdesc

/-- **Faithfully flat descent for affine group-valued points.** If `B` is faithfully flat over
`A`, base change identifies the convolution group of `A`-points of `H` with the subgroup of
`B`-points whose two restrictions to `B ⊗[A] B` agree. -/
noncomputable def faithfullyFlatDescentMulEquiv :
    WithConv (H →ₐ[R] A) ≃* descentSubgroup (R := R) (H := H) A B :=
  MulEquiv.ofBijective (faithfullyFlatDescentHom (R := R) (H := H) A B)
    (faithfullyFlatDescentHom_bijective (R := R) (H := H) A B)

/-- The faithfully flat descent equivalence sends an `A`-point to its base change to `B`. -/
@[simp]
theorem faithfullyFlatDescentMulEquiv_apply (f : WithConv (H →ₐ[R] A)) :
    (faithfullyFlatDescentMulEquiv (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      mapValue (H := H) (IsScalarTower.toAlgHom R A B) f :=
  by
    rw [faithfullyFlatDescentMulEquiv, MulEquiv.ofBijective_apply]
    exact faithfullyFlatDescentHom_apply (R := R) A B f

/-- Descending a compatible `B`-point and extending it back to `B` recovers the original
point. -/
@[simp]
theorem mapValue_faithfullyFlatDescentMulEquiv_symm_apply
    (f : descentSubgroup (R := R) (H := H) A B) :
    WithConv.toConv ((IsScalarTower.toAlgHom R A B).comp
      ((faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).symm f).ofConv) = f.1 := by
  rw [← mapValue_apply]
  rw [← faithfullyFlatDescentMulEquiv_apply]
  exact congr_arg Subtype.val
    ((faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).apply_symm_apply f)

end CommRing

end AlgHom

end TauCeti
