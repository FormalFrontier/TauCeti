/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.Algebra.Module.GradedModule.TensorProduct

/-!
# The graded tensor product of two internally `ℤ`-graded algebras is graded

Mathlib's `GradedTensorProduct R 𝒜 ℬ`, written `𝒜 ᵍ⊗[R] ℬ`, is the tensor product `A ⊗[R] B`
with the Koszul-signed multiplication

`(a ᵍ⊗ₜ b) * (a' ᵍ⊗ₜ b') = (-1) ^ (|b| * |a'|) • (a * a') ᵍ⊗ₜ (b * b')`.

Mathlib stops at the ring and algebra structures.  This file supplies the grading they are
compatible with: the total-degree grading of the underlying tensor product of graded modules turns
`𝒜 ᵍ⊗[R] ℬ` into an internally `ℤ`-graded algebra.

## Main definitions

* `TauCeti.gradedTensorGrading`: the total-degree grading of `𝒜 ᵍ⊗[R] ℬ`, whose degree-`n` piece
  is the sum of the images of `𝒜 p ⊗ ℬ (n - p)`.
* `TauCeti.gradedTensorLift`: the graded universal-property map induced by two graded algebra maps
  whose images satisfy the Koszul commutation rule.
* `TauCeti.gradedTensorIncludeLeft` and `TauCeti.gradedTensorIncludeRight`: the inclusions
  `a ↦ a ᵍ⊗ₜ 1` and `b ↦ 1 ᵍ⊗ₜ b` of the two factors, as homomorphisms of graded algebras.

## Main results

* `TauCeti.tmul_mem_gradedTensorGrading`: degrees add on pure tensors.
* `TauCeti.instGradedAlgebraGradedTensorGrading`: the graded tensor product of two internally
  `ℤ`-graded algebras is an internally `ℤ`-graded algebra.
* `TauCeti.gradedTensorGrading_le`: a submodule containing every homogeneous pure tensor of total
  degree `n` contains the whole degree-`n` piece; `TauCeti.eq_top_of_tmul_mem` and
  `TauCeti.linearMap_ext_of_tmul` are the corresponding statements for the whole graded tensor
  product and for maps out of it.  These three are the tools with which a statement about the
  graded tensor product is reduced to pure tensors of homogeneous elements, which is where the
  Koszul sign is available.

The grading of the underlying module is `TauCeti.InternalGrading.tensorProduct` and the Koszul
multiplication is Mathlib's `GradedTensorProduct`; only their compatibility is proved here.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §4.7, example (2).
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The total-degree grading of the graded tensor product `𝒜 ᵍ⊗[R] ℬ`: the degree-`n` piece is the
sum of the images of `𝒜 p ⊗ ℬ (n - p)`. -/
noncomputable def gradedTensorGrading (n : ℤ) : Submodule R (𝒜 ᵍ⊗[R] ℬ) :=
  (((InternalGrading.ofDecomposition 𝒜).tensorProduct
    (InternalGrading.ofDecomposition ℬ)).map (GradedTensorProduct.of R 𝒜 ℬ)).piece n

/-- The homogeneous pieces of the graded tensor product form an internal direct sum. -/
theorem isInternal_gradedTensorGrading :
    DirectSum.IsInternal (gradedTensorGrading 𝒜 ℬ) :=
  InternalGrading.isInternal _

/-- A pure tensor of homogeneous elements is homogeneous, of the sum of their degrees. -/
theorem tmul_mem_gradedTensorGrading {p q : ℤ} {a : A} {b : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) :
    a ᵍ⊗ₜ[R] b ∈ gradedTensorGrading 𝒜 ℬ (p + q) := by
  rw [gradedTensorGrading, InternalGrading.map_piece,
    InternalGrading.tensorProduct_piece_eq_iSup, InternalGrading.ofDecomposition_piece,
    InternalGrading.ofDecomposition_piece]
  refine Submodule.mem_map_of_mem (Submodule.mem_iSup_of_mem p ?_)
  simpa only [add_sub_cancel_left, TensorProduct.mk_apply] using
    Submodule.apply_mem_map₂ (TensorProduct.mk R A B) ha hb

/-- A submodule containing every homogeneous pure tensor of total degree `n` contains the whole
degree-`n` piece of the graded tensor product. -/
theorem gradedTensorGrading_le {n : ℤ} {C : Submodule R (𝒜 ᵍ⊗[R] ℬ)}
    (h : ∀ p : ℤ, ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ (n - p), a ᵍ⊗ₜ[R] b ∈ C) :
    gradedTensorGrading 𝒜 ℬ n ≤ C := by
  rw [gradedTensorGrading, InternalGrading.map_piece,
    InternalGrading.tensorProduct_piece_eq_iSup, InternalGrading.ofDecomposition_piece,
    InternalGrading.ofDecomposition_piece, Submodule.map_le_iff_le_comap]
  exact iSup_le fun p ↦ Submodule.map₂_le.2 fun a ha b hb ↦ h p a ha b hb

/-- A submodule containing every homogeneous pure tensor is the whole graded tensor product. -/
theorem eq_top_of_tmul_mem {C : Submodule R (𝒜 ᵍ⊗[R] ℬ)}
    (h : ∀ p q : ℤ, ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ q, a ᵍ⊗ₜ[R] b ∈ C) :
    C = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← (isInternal_gradedTensorGrading 𝒜 ℬ).submodule_iSup_eq_top]
  exact iSup_le fun n ↦ gradedTensorGrading_le 𝒜 ℬ fun p a ha b hb ↦ h p (n - p) a ha b hb

/-- Multiplying a homogeneous pure tensor into a homogeneous element adds degrees. -/
private theorem tmul_mul_mem_gradedTensorGrading {p q n : ℤ} {a : A} {b : B} {y : 𝒜 ᵍ⊗[R] ℬ}
    (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) (hy : y ∈ gradedTensorGrading 𝒜 ℬ n) :
    (a ᵍ⊗ₜ[R] b) * y ∈ gradedTensorGrading 𝒜 ℬ (p + q + n) := by
  refine gradedTensorGrading_le 𝒜 ℬ (C := Submodule.comap
    (GradedTensorProduct.mulHom 𝒜 ℬ (a ᵍ⊗ₜ[R] b)) (gradedTensorGrading 𝒜 ℬ (p + q + n)))
    (fun r a' ha' b' hb' ↦ ?_) hy
  rw [Submodule.mem_comap, ← GradedTensorProduct.mul_def,
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨a', ha'⟩ b']
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  convert tmul_mem_gradedTensorGrading 𝒜 ℬ (SetLike.mul_mem_graded ha ha')
    (SetLike.mul_mem_graded hb hb') using 1
  all_goals ring_nf

/-- The Koszul multiplication of the graded tensor product adds degrees. -/
instance instGradedMonoidGradedTensorGrading :
    SetLike.GradedMonoid (gradedTensorGrading 𝒜 ℬ) where
  one_mem := by
    have h : (1 : 𝒜 ᵍ⊗[R] ℬ) = (1 : A) ᵍ⊗ₜ[R] (1 : B) := rfl
    rw [h]
    convert tmul_mem_gradedTensorGrading 𝒜 ℬ (SetLike.one_mem_graded 𝒜)
      (SetLike.one_mem_graded ℬ) using 1
    all_goals ring_nf
  mul_mem := by
    intro m n x y hx hy
    refine gradedTensorGrading_le 𝒜 ℬ (C := Submodule.comap
      ((GradedTensorProduct.mulHom 𝒜 ℬ).flip y) (gradedTensorGrading 𝒜 ℬ (m + n)))
      (fun p a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, LinearMap.flip_apply, ← GradedTensorProduct.mul_def]
    convert tmul_mul_mem_gradedTensorGrading 𝒜 ℬ ha hb hy using 1
    all_goals ring_nf

/-- The graded tensor product of two internally `ℤ`-graded algebras is an internally `ℤ`-graded
algebra for the total-degree grading. -/
noncomputable instance instGradedAlgebraGradedTensorGrading :
    GradedAlgebra (gradedTensorGrading 𝒜 ℬ) :=
  (isInternal_gradedTensorGrading 𝒜 ℬ).gradedAlgebra

section Lift

variable {C : Type uC} [Ring C] [Algebra R C]
  (𝒞 : ℤ → Submodule R C) [GradedAlgebra 𝒞]

private theorem gradedTensorLift_map_mem (F : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C)
    (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞) (hF : ∀ a b, F (a ᵍ⊗ₜ[R] b) = f a * g b)
    {n : ℤ} {x : 𝒜 ᵍ⊗[R] ℬ} (hx : x ∈ gradedTensorGrading 𝒜 ℬ n) : F x ∈ 𝒞 n := by
  refine gradedTensorGrading_le 𝒜 ℬ (C := Submodule.comap
    F.toLinearMap (𝒞 n)) (fun p a ha b hb ↦ ?_) hx
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, hF]
  have hfg := SetLike.mul_mem_graded (f.map_mem ha) (g.map_mem hb)
  -- `mul_mem_graded` uses the stored graded ring maps; expose the definitionally equal
  -- `GradedAlgHom` coercions before normalizing the degree.
  change f a * g b ∈ 𝒞 (p + (n - p)) at hfg
  simpa only [add_sub_cancel] using hfg

/-- The graded algebra map out of a graded tensor product induced by two graded algebra maps whose
images satisfy the Koszul commutation rule. -/
@[expose] noncomputable def gradedTensorLift (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    gradedTensorGrading 𝒜 ℬ →ₐᵍ[R] 𝒞 := by
  have h' : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f.toAlgHom a * g.toAlgHom b = (-1 : ℤˣ) ^ (j * i) •
        (g.toAlgHom b * f.toAlgHom a) := by
    intro i j a b
    -- Mathlib's lift accepts the stored `AlgHom`s, whose applications are definitionally the
    -- applications of the graded maps in the supplied commutation hypothesis.
    change f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)
    exact h a b
  let F : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C :=
    GradedTensorProduct.lift 𝒜 ℬ f.toAlgHom g.toAlgHom h'
  exact { F with
    map_mem := by
      apply gradedTensorLift_map_mem 𝒜 ℬ 𝒞
        (F := F) (f := f) (g := g)
      intro a b
      -- The local `F` is Mathlib's underlying lift; expose its stored factor maps to use its
      -- pure-tensor computation theorem.
      change F (a ᵍ⊗ₜ[R] b) = f.toAlgHom a * g.toAlgHom b
      exact GradedTensorProduct.lift_tmul 𝒜 ℬ f.toAlgHom g.toAlgHom h' a b }

/-- The graded tensor lift sends a pure tensor to the product of the two factor maps. -/
@[simp]
theorem gradedTensorLift_tmul (f : 𝒜 →ₐᵍ[R] 𝒞) (g : ℬ →ₐᵍ[R] 𝒞)
    (h : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j),
      f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) (a : A) (b : B) :
    gradedTensorLift 𝒜 ℬ 𝒞 f g h (a ᵍ⊗ₜ[R] b) = f a * g b :=
  rfl

end Lift

/-- A pure tensor of the graded tensor product is additive in its left factor. -/
@[simp]
theorem gradedTensor_add_tmul (a₁ a₂ : A) (b : B) :
    (a₁ + a₂) ᵍ⊗ₜ[R] b = (a₁ ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) + a₂ ᵍ⊗ₜ[R] b := by
  simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]

/-- A pure tensor of the graded tensor product is additive in its right factor. -/
@[simp]
theorem gradedTensor_tmul_add (a : A) (b₁ b₂ : B) :
    a ᵍ⊗ₜ[R] (b₁ + b₂) = (a ᵍ⊗ₜ[R] b₁ : 𝒜 ᵍ⊗[R] ℬ) + a ᵍ⊗ₜ[R] b₂ := by
  simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]

/-- Scalars pass from the left factor of a pure tensor to the tensor. -/
@[simp]
theorem gradedTensor_smul_tmul (r : R) (a : A) (b : B) :
    (r • a) ᵍ⊗ₜ[R] b = r • (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) := by
  simp only [GradedTensorProduct.tmul, ← map_smul, TensorProduct.smul_tmul']

/-- Scalars pass from the right factor of a pure tensor to the tensor. -/
@[simp]
theorem gradedTensor_tmul_smul (r : R) (a : A) (b : B) :
    a ᵍ⊗ₜ[R] (r • b) = r • (a ᵍ⊗ₜ[R] b : 𝒜 ᵍ⊗[R] ℬ) := by
  simp only [GradedTensorProduct.tmul, ← map_smul, TensorProduct.tmul_smul]

/-- A pure tensor of the graded tensor product vanishes when its left factor does. -/
@[simp]
theorem gradedTensor_zero_tmul (b : B) : (0 : A) ᵍ⊗ₜ[R] b = (0 : 𝒜 ᵍ⊗[R] ℬ) := by
  simp [GradedTensorProduct.tmul]

/-- A pure tensor of the graded tensor product vanishes when its right factor does. -/
@[simp]
theorem gradedTensor_tmul_zero (a : A) : a ᵍ⊗ₜ[R] (0 : B) = (0 : 𝒜 ᵍ⊗[R] ℬ) := by
  simp [GradedTensorProduct.tmul]

/-- Two linear maps out of the graded tensor product agree as soon as they agree on the pure
tensors of homogeneous elements. -/
theorem linearMap_ext_of_tmul {M : Type*} [AddCommGroup M] [Module R M]
    {f g : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] M}
    (h : ∀ p q : ℤ, ∀ a ∈ 𝒜 p, ∀ b ∈ ℬ q, f (a ᵍ⊗ₜ[R] b) = g (a ᵍ⊗ₜ[R] b)) :
    f = g := by
  refine LinearMap.ext fun x ↦ sub_eq_zero.1 ?_
  have hx : x ∈ (⊤ : Submodule R (𝒜 ᵍ⊗[R] ℬ)) := trivial
  rw [← eq_top_of_tmul_mem 𝒜 ℬ (C := LinearMap.ker (f - g))
    fun p q a ha b hb ↦ by simp [h p q a ha b hb]] at hx
  simpa using hx

/-- The inclusion `a ↦ a ᵍ⊗ₜ 1` of the left factor, as a homomorphism of graded algebras. -/
noncomputable def gradedTensorIncludeLeft : 𝒜 →ₐᵍ[R] gradedTensorGrading 𝒜 ℬ :=
  { GradedTensorProduct.includeLeft 𝒜 ℬ with
    map_mem := fun {i x} hx ↦ by
      have h : x ᵍ⊗ₜ[R] (1 : B) ∈ gradedTensorGrading 𝒜 ℬ i := by
        convert tmul_mem_gradedTensorGrading 𝒜 ℬ hx
          (SetLike.one_mem_graded ℬ) using 1
        all_goals ring_nf
      exact h }

@[simp]
theorem gradedTensorIncludeLeft_apply (a : A) :
    gradedTensorIncludeLeft 𝒜 ℬ a = a ᵍ⊗ₜ[R] (1 : B) := (rfl)

/-- The inclusion `b ↦ 1 ᵍ⊗ₜ b` of the right factor, as a homomorphism of graded algebras. -/
noncomputable def gradedTensorIncludeRight : ℬ →ₐᵍ[R] gradedTensorGrading 𝒜 ℬ :=
  { GradedTensorProduct.includeRight 𝒜 ℬ with
    map_mem := fun {i x} hx ↦ by
      have h : (1 : A) ᵍ⊗ₜ[R] x ∈ gradedTensorGrading 𝒜 ℬ i := by
        convert tmul_mem_gradedTensorGrading 𝒜 ℬ
          (SetLike.one_mem_graded 𝒜) hx using 1
        all_goals ring_nf
      exact h }

@[simp]
theorem gradedTensorIncludeRight_apply (b : B) :
    gradedTensorIncludeRight 𝒜 ℬ b = (1 : A) ᵍ⊗ₜ[R] b := (rfl)

end TauCeti
