/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Augmented differential graded algebras

An augmentation of a differential graded algebra `A` over `R` is a morphism of DG algebras from
`A` to the ground ring, placed in degree zero with zero differential.  Its kernel is the reduced
augmentation ideal.  It is homogeneous, stable under the differential and multiplication from
either side, and the unit section splits the underlying module as
`A ≃ R × ker ε`.

This is the input used by the reduced bar construction: tensor words are formed from the
augmentation ideal rather than from the unit-containing algebra.

## Main definitions

* `TauCeti.DGAlgAugmentation`: a DG algebra morphism from `A` to the trivially graded base ring.
* `TauCeti.DGAlgAugmentation.augmentationIdeal`: the homogeneous kernel of an augmentation.
* `TauCeti.DGAlgAugmentation.twoSidedIdeal`: the same kernel as a two-sided ideal of `A`.
* `TauCeti.DGAlgAugmentation.splitLinearEquiv`: the canonical linear splitting
  `A ≃ R × ker ε`.
* `TauCeti.IsDGAlgebra.unitHom`: the canonical unit morphism from the trivially graded base.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- The ground ring with its trivial grading and zero differential is a differential graded
algebra. -/
theorem isDGAlgebra_trivialGrading (R : Type uR) [CommRing R] :
    IsDGAlgebra (trivialGrading R R) (0 : R →ₗ[R] R) :=
  isDGAlgebra_zero _

/-- An augmentation of a differential graded algebra over `R` is a DG algebra morphism to `R`,
where the ground ring is concentrated in degree zero and has zero differential. -/
abbrev DGAlgAugmentation (h : IsDGAlgebra 𝒜 d) :=
  DGAlgHom h (isDGAlgebra_trivialGrading R)

namespace IsDGAlgebra

/-- The canonical unit morphism from the trivially graded ground ring into a differential graded
algebra. -/
noncomputable def unitHom (h : IsDGAlgebra 𝒜 d) :
    DGAlgHom (isDGAlgebra_trivialGrading R) h where
  toGradedAlgHom :=
    { toAlgHom := Algebra.ofId R A
      map_mem := by
        intro p r hr
        rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
        · -- Normalize the `Algebra.ofId` wrapper to the algebra map used by the grading API.
          change algebraMap R A r ∈ 𝒜 0
          rw [Algebra.algebraMap_eq_smul_one]
          exact (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜)
        · simp }
  map_d' r := by simpa using h.map_algebraMap r

@[simp]
theorem unitHom_apply (h : IsDGAlgebra 𝒜 d) (r : R) :
    h.unitHom r = algebraMap R A r := (rfl)

end IsDGAlgebra

namespace DGAlgAugmentation

variable {h : IsDGAlgebra 𝒜 d} (e : DGAlgAugmentation h)

/-- An augmentation restricts to the identity on the image of the ground ring. -/
@[simp]
theorem map_algebraMap (r : R) : e (algebraMap R A r) = r :=
  (e.toGradedAlgHom.commutes r).trans (Algebra.algebraMap_self_apply r)

/-- An augmentation is surjective, since it restricts to the identity on the image of the ground
ring. -/
theorem surjective : Function.Surjective e :=
  fun r => ⟨algebraMap R A r, e.map_algebraMap r⟩

/-- An augmentation annihilates every differential. -/
@[simp]
theorem map_d (a : A) : e (d a) = 0 := by
  simpa using (DGAlgHom.map_d e a).symm

/-- The augmentation ideal, as a homogeneous submodule of the underlying graded module. -/
noncomputable def augmentationIdeal :
    HomogeneousSubmodule (trivialGrading R R) 𝒜 where
  toSubmodule := LinearMap.ker e.toGradedAlgHom.toAlgHom.toLinearMap
  is_homogeneous' := by
    intro p a ha
    rw [LinearMap.mem_ker] at ha ⊢
    -- Unwrap the kernel's linear map so the graded-homomorphism projection lemma applies.
    change e a = 0 at ha
    change e (DirectSum.decompose 𝒜 a p) = 0
    rw [map_directSumDecompose 𝒜 (trivialGrading R R) e, ha,
      DirectSum.decompose_zero]
    rfl

/-- Membership in the augmentation ideal is equivalent to vanishing under the augmentation. -/
@[simp]
theorem mem_augmentationIdeal {a : A} : a ∈ e.augmentationIdeal ↔ e a = 0 :=
  LinearMap.mem_ker

/-- The augmentation ideal, as a two-sided ideal of `A`.  This is the same kernel as
`TauCeti.DGAlgAugmentation.augmentationIdeal`, packaged so that the two-sided ideal lattice,
quotient, and multiplication API applies to it. -/
def twoSidedIdeal : TwoSidedIdeal A :=
  TwoSidedIdeal.ker e

/-- Membership in the two-sided augmentation ideal is equivalent to vanishing under the
augmentation. -/
@[simp]
theorem mem_twoSidedIdeal {a : A} : a ∈ e.twoSidedIdeal ↔ e a = 0 :=
  TwoSidedIdeal.mem_ker e

/-- The two-sided augmentation ideal and its homogeneous submodule view have the same elements. -/
theorem mem_twoSidedIdeal_iff_mem_augmentationIdeal {a : A} :
    a ∈ e.twoSidedIdeal ↔ a ∈ e.augmentationIdeal := by
  rw [mem_twoSidedIdeal, mem_augmentationIdeal]

/-- The augmentation ideal absorbs multiplication on the left. -/
theorem mul_mem_augmentationIdeal_left (a : A) {x : A} (hx : x ∈ e.augmentationIdeal) :
    a * x ∈ e.augmentationIdeal := by
  simpa using e.twoSidedIdeal.mul_mem_left a x (by simpa using hx)

/-- The augmentation ideal absorbs multiplication on the right. -/
theorem mul_mem_augmentationIdeal_right {x : A} (hx : x ∈ e.augmentationIdeal) (a : A) :
    x * a ∈ e.augmentationIdeal := by
  simpa using e.twoSidedIdeal.mul_mem_right x a (by simpa using hx)

/-- The differential of every element lies in the augmentation ideal. -/
theorem map_mem_augmentationIdeal (x : A) :
    d x ∈ e.augmentationIdeal := by
  rw [mem_augmentationIdeal, e.map_d]

/-- The augmentation is a retraction of its canonical unit morphism. -/
@[simp]
theorem comp_unitHom :
    e.comp h.unitHom = DGAlgHom.id (isDGAlgebra_trivialGrading R) := by
  ext r
  simp

/-- Removing the scalar part of an element leaves an element of the augmentation ideal. -/
theorem sub_algebraMap_mem_augmentationIdeal (a : A) :
    a - algebraMap R A (e a) ∈ e.augmentationIdeal := by
  rw [mem_augmentationIdeal, map_sub, e.map_algebraMap, sub_self]

/-- The linear projection from an augmented DG algebra onto its augmentation ideal, subtracting
the scalar part of an element. -/
noncomputable def reducedPart : A →ₗ[R] e.augmentationIdeal.toSubmodule :=
  LinearMap.codRestrict _
    (LinearMap.id - (Algebra.linearMap R A).comp e.toGradedAlgHom.toAlgHom.toLinearMap)
    e.sub_algebraMap_mem_augmentationIdeal

/-- The reduced-part projection subtracts the scalar part of an element. -/
@[simp]
theorem coe_reducedPart (a : A) :
    (e.reducedPart a : A) = a - algebraMap R A (e a) := (rfl)

/-- The reduced-part projection fixes the augmentation ideal pointwise. -/
@[simp]
theorem reducedPart_coe (x : e.augmentationIdeal) :
    e.reducedPart (x : A) = x := by
  apply Subtype.ext
  rw [coe_reducedPart, (mem_augmentationIdeal e).mp x.property, map_zero, sub_zero]

/-- The canonical splitting of an augmented DG algebra into its scalar and reduced parts. -/
noncomputable def splitLinearEquiv : A ≃ₗ[R] R × e.augmentationIdeal :=
  LinearMap.equivProdOfSurjectiveOfIsCompl e.toGradedAlgHom.toAlgHom.toLinearMap e.reducedPart
    (LinearMap.range_eq_top.2 e.surjective) (LinearMap.range_eq_of_proj e.reducedPart_coe)
    (LinearMap.isCompl_of_proj e.reducedPart_coe)

/-- The splitting sends an element to its scalar part and its reduced part. -/
@[simp]
theorem splitLinearEquiv_apply (a : A) :
    e.splitLinearEquiv a = (e a, e.reducedPart a) := (rfl)

/-- The inverse splitting adds the scalar and reduced parts. -/
@[simp]
theorem splitLinearEquiv_symm_apply (x : R × e.augmentationIdeal) :
    e.splitLinearEquiv.symm x = algebraMap R A x.1 + x.2 := by
  have hx : e (x.2 : A) = 0 := (mem_augmentationIdeal e).mp x.2.property
  rw [LinearEquiv.symm_apply_eq, splitLinearEquiv_apply]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [map_add, e.map_algebraMap, hx, add_zero]
  · rw [coe_reducedPart, map_add, e.map_algebraMap, hx, add_zero, add_sub_cancel_left]

end DGAlgAugmentation

end TauCeti
