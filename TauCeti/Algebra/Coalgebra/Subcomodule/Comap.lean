/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Inverse images of subcomodules

This file adds inverse images of subcomodules under comodule morphisms. If
`f : M → N` is a morphism of right comodules and `B ≤ N` is a subcomodule, then
`B.comap f` has underlying submodule `B.toSubmodule.comap f`. Stability under the
coaction follows by applying tensor-product right exactness to the quotient map
`N → N / B`.

This is Layer 1 infrastructure for the reductive-groups roadmap target on comodules:
subobjects of representations need both images and inverse images before kernels,
finite-subcomodule constructions, and the representation/comodule dictionary can be used
comfortably.

## Main declarations

* `TauCeti.Subcomodule.comap`: inverse image of a subcomodule under a comodule morphism.
* `TauCeti.Subcomodule.mem_comap`, `comap_toSubmodule`: characteristic API.
* `TauCeti.Subcomodule.comap_finite`: inverse images into noetherian modules are finite.
* `TauCeti.Subcomodule.map_le_iff_le_comap`, `gc_map_comap`: the usual image/preimage
  Galois connection.
* `TauCeti.Subcomodule.comap_bot_toSubmodule`: the bottom inverse image as a kernel.
* `TauCeti.Comodule.Hom.ker_finite`: kernels in noetherian modules are finite.

## References

The construction is the standard inverse image of a subcomodule; see Sweedler,
*Hopf Algebras*, Chapter 2. The exactness step reuses Mathlib's
`TensorProduct.rTensor_exact` and `LinearMap.exact_subtype_ker_map`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x y

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommRing R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Subcomodule

private theorem ker_rangeRestrict_mkQ_comp {M₁ : Type w} {N₁ : Type x}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁]
    (B : Submodule R N₁) (f : M₁ →ₗ[R] N₁) :
    LinearMap.ker (B.mkQ.comp f).rangeRestrict = B.comap f := by
  ext m
  simp [LinearMap.mem_ker, Submodule.mem_comap]

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem rTensor_rangeRestrict_eq_zero_of_rTensor_eq_zero {M₁ : Type w} {N₁ : Type x}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁]
    {B : Submodule R N₁} {f : M₁ →ₗ[R] N₁} {t : M₁ ⊗[R] C}
    (h : LinearMap.rTensor C (B.mkQ.comp f) t = 0) :
    LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict t = 0 := by
  letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R (M := C)
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (LinearMap.range (B.mkQ.comp f)).subtype Subtype.val_injective
  calc
    LinearMap.rTensor C (LinearMap.range (B.mkQ.comp f)).subtype
        (LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict t)
      = (LinearMap.rTensor C (LinearMap.range (B.mkQ.comp f)).subtype ∘ₗ
          LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict) t := rfl
    _ = LinearMap.rTensor C
          ((LinearMap.range (B.mkQ.comp f)).subtype.comp (B.mkQ.comp f).rangeRestrict) t := by
          rw [← LinearMap.rTensor_comp]
    _ = LinearMap.rTensor C (B.mkQ.comp f) t := by
          rfl
    _ = 0 := h

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem tensor_mem_range_comap {M₁ : Type w} {N₁ : Type x}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁] [Module R N₁]
    (B : Submodule R N₁) (f : M₁ →ₗ[R] N₁)
    {t : M₁ ⊗[R] C} (h : LinearMap.rTensor C (B.mkQ.comp f) t = 0) :
    t ∈ LinearMap.range
      (TensorProduct.map (B.comap f).subtype (LinearMap.id : C →ₗ[R] C)) := by
  letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R (M := C)
  let g : M₁ →ₗ[R] LinearMap.range (B.mkQ.comp f) := (B.mkQ.comp f).rangeRestrict
  have hker : LinearMap.ker g = B.comap f :=
    ker_rangeRestrict_mkQ_comp (M₁ := M₁) (N₁ := N₁) B f
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    exact LinearMap.range_rangeRestrict (B.mkQ.comp f)
  have hexact : Function.Exact (LinearMap.ker g).subtype g :=
    LinearMap.exact_subtype_ker_map g
  have ht : t ∈ LinearMap.ker (LinearMap.rTensor C g) := by
    rw [LinearMap.mem_ker]
    exact rTensor_rangeRestrict_eq_zero_of_rTensor_eq_zero (R := R) (C := C)
      (M₁ := M₁) (N₁ := N₁) h
  have ht' :
      t ∈ LinearMap.range (LinearMap.rTensor C (LinearMap.ker g).subtype) := by
    simpa [Function.Exact.linearMap_ker_eq (rTensor_exact C hexact hg)] using ht
  rw [← hker]
  rw [LinearMap.rTensor_def] at ht'
  simpa using ht'

private theorem coact_mem_range_comap_toLinearMap (f : Comodule.Hom R C M N) (B : Subcomodule R C N)
    {m : M} (hm : m ∈ B.toSubmodule.comap f.toLinearMap) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range
        (TensorProduct.map (B.toSubmodule.comap f.toLinearMap).subtype
          (LinearMap.id : C →ₗ[R] C)) := by
  letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R (M := C)
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  refine tensor_mem_range_comap (R := R) (C := C) (M₁ := M) (N₁ := N)
    B.toSubmodule f.toLinearMap ?_
  rw [LinearMap.rTensor_comp_apply]
  rw [LinearMap.rTensor_def, LinearMap.rTensor_def]
  rw [Comodule.Hom.map_coact_apply f m]
  -- The preceding rewrites expose the quotient-after-coaction calculation.  The public
  -- `Subcomodule` API is monoid-level, while the tensor exactness proof temporarily uses the
  -- additive-group instances derived from the `R`-module structures; this `change` is only the
  -- resulting `rTensor`/`TensorProduct.map` wrapper conversion.
  change LinearMap.rTensor C B.toSubmodule.mkQ
    (Comodule.coact (R := R) (C := C) (M := N) (f.toLinearMap m)) = 0
  rcases B.coact_mem hm with ⟨t, ht⟩
  rw [← ht]
  change LinearMap.rTensor C B.carrier.mkQ
    (LinearMap.rTensor C B.carrier.subtype t) = 0
  rw [← LinearMap.mem_ker, rTensor_mkQ]
  exact
    (LinearMap.mem_range_self (LinearMap.rTensor C B.carrier.subtype) t)

private theorem comap_coact_mem (f : Comodule.Hom R C M N) (B : Subcomodule R C N)
    {m : M} (hm : m ∈ B.toSubmodule.comap f.toLinearMap) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range
        (TensorProduct.map (B.toSubmodule.comap f.toLinearMap).subtype
          (LinearMap.id : C →ₗ[R] C)) :=
  coact_mem_range_comap_toLinearMap f B hm

/-- The inverse image of a subcomodule under a comodule morphism. -/
@[expose] def comap (B : Subcomodule R C N) (f : Comodule.Hom R C M N) : Subcomodule R C M where
  carrier := B.toSubmodule.comap f.toLinearMap
  coact_mem' := by
    intro m hm
    exact comap_coact_mem f B hm

/-- The underlying submodule of an inverse-image subcomodule is the inverse image of the
underlying submodule. -/
@[simp]
theorem comap_toSubmodule (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    (B.comap f).toSubmodule = B.toSubmodule.comap f.toLinearMap :=
  rfl

/-- The inverse image of a subcomodule into a noetherian module is finitely generated as an
`R`-module. -/
theorem comap_finite (B : Subcomodule R C N) (f : Comodule.Hom R C M N)
    [IsNoetherian R M] : Module.Finite R (B.comap f).toSubmodule := by
  exact (B.comap f).finite

/-- Membership in an inverse-image subcomodule. -/
@[simp]
theorem mem_comap {B : Subcomodule R C N} {f : Comodule.Hom R C M N} {m : M} :
    m ∈ B.comap f ↔ f m ∈ B :=
  Iff.rfl

/-- The inverse-image construction is monotone in the target subcomodule. -/
theorem comap_mono (f : Comodule.Hom R C M N) {B D : Subcomodule R C N} (hBD : B ≤ D) :
    B.comap f ≤ D.comap f := by
  intro m hm
  exact hBD hm

/-- The inverse image of the top subcomodule is top. -/
@[simp]
theorem comap_top (f : Comodule.Hom R C M N) : (⊤ : Subcomodule R C N).comap f = ⊤ := by
  ext m
  simp

/-- The underlying submodule of the inverse image of the bottom subcomodule is the kernel. -/
@[simp]
theorem comap_bot_toSubmodule (f : Comodule.Hom R C M N) :
    ((⊥ : Subcomodule R C N).comap f).toSubmodule = LinearMap.ker f.toLinearMap := by
  ext m
  simp [LinearMap.mem_ker]

/-- Images are left adjoint to inverse images for subcomodules. -/
theorem map_le_iff_le_comap {A : Subcomodule R C M} {B : Subcomodule R C N}
    {f : Comodule.Hom R C M N} :
    A.map f ≤ B ↔ A ≤ B.comap f := by
  rw [map_le_iff]
  rfl

/-- The image construction is left adjoint to inverse image for subcomodules. -/
theorem gc_map_comap (f : Comodule.Hom R C M N) :
    GaloisConnection
      (fun A : Subcomodule R C M => A.map f)
      (fun B : Subcomodule R C N => B.comap f) := fun _ _ =>
  map_le_iff_le_comap

/-- A subcomodule is contained in the inverse image of its image. -/
theorem le_comap_map (A : Subcomodule R C M) (f : Comodule.Hom R C M N) :
    A ≤ (A.map f).comap f :=
  (gc_map_comap f).le_u_l A

/-- A subcomodule is contained in the inverse image of the image of a larger subcomodule. -/
theorem le_comap_map_of_le {A D : Subcomodule R C M} (hAD : A ≤ D) (f : Comodule.Hom R C M N) :
    A ≤ (D.map f).comap f := by
  rw [← map_le_iff_le_comap]
  exact map_mono f hAD

/-- The image of the inverse image of a subcomodule is contained in the subcomodule. -/
theorem map_comap_le (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    (B.comap f).map f ≤ B := by
  exact (gc_map_comap f).l_u_le B

/-- Inverse images compose contravariantly with comodule morphisms. -/
@[simp]
theorem comap_comap {P : Type y} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (B : Subcomodule R C P) (f : Comodule.Hom R C M N) (g : Comodule.Hom R C N P) :
    (B.comap g).comap f = B.comap (g.comp f) := by
  ext m
  rfl

/-- The inverse image along the identity comodule morphism is the original subcomodule. -/
@[simp]
theorem comap_id (B : Subcomodule R C M) :
    B.comap (Comodule.Hom.id R C M) = B := by
  ext m
  rfl

end Subcomodule

namespace Comodule

namespace Hom

/-- The kernel of a comodule morphism as a subcomodule of the domain. -/
def ker (f : Hom R C M N) : Subcomodule R C M :=
  (⊥ : Subcomodule R C N).comap f

/-- The underlying submodule of the kernel subcomodule is the linear-map kernel. -/
@[simp]
theorem ker_toSubmodule (f : Hom R C M N) :
    (ker (R := R) (C := C) f).toSubmodule = LinearMap.ker f.toLinearMap :=
  Subcomodule.comap_bot_toSubmodule f

/-- The kernel of a comodule morphism out of a noetherian module is finitely generated as an
`R`-module. -/
theorem ker_finite (f : Hom R C M N) [IsNoetherian R M] :
    Module.Finite R (ker (R := R) (C := C) f).toSubmodule := by
  exact (ker (R := R) (C := C) f).finite

/-- Membership in the kernel subcomodule is vanishing under the morphism. -/
@[simp]
theorem mem_ker {f : Hom R C M N} {m : M} :
    m ∈ ker (R := R) (C := C) f ↔ f m = 0 := by
  rw [← Subcomodule.mem_toSubmodule, ker_toSubmodule, LinearMap.mem_ker]
  rfl

/-- The kernel subcomodule contains zero. -/
theorem zero_mem_ker (f : Hom R C M N) : (0 : M) ∈ ker (R := R) (C := C) f := by
  rw [mem_ker]
  exact f.toLinearMap.map_zero

/-- A subcomodule is contained in the kernel exactly when the morphism vanishes on it. -/
theorem le_ker_iff {f : Hom R C M N} {A : Subcomodule R C M} :
    A ≤ ker (R := R) (C := C) f ↔ ∀ ⦃m⦄, m ∈ A → f m = 0 := by
  constructor
  · intro h m hm
    exact mem_ker.mp (h hm)
  · intro h m hm
    exact mem_ker.mpr (h hm)

/-- An element whose image under a comodule morphism is zero belongs to its kernel. -/
theorem mem_ker_of_apply_eq_zero {f : Hom R C M N} {m : M} (hm : f m = 0) :
    m ∈ ker (R := R) (C := C) f :=
  mem_ker.mpr hm

end Hom

end Comodule

end TauCeti
