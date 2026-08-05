/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The augmentation subrepresentation of a permutation representation

A permutation representation `k[X]` of a group `G` on a `G`-set `X` always carries two canonical
subrepresentations, visible before anything is known about `G`: the **invariant line** spanned by
the sum of the standard basis, and the **augmentation subrepresentation** cut out by the vanishing
of the sum of the coefficients.  Neither uses more than the fact that `G` permutes the standard
basis, which leaves the coefficient sum unchanged.

For a finite `X` whose cardinality is invertible in `k` the two are complementary, so `k[X]` splits
as a line carrying the trivial representation plus a representation of dimension `|X| - 1`.  That
is the source of the *deleted* permutation representations, of which the standard representation of
the symmetric group in `TauCeti.RepresentationTheory.Symmetric.Standard` is the first example.

## Main definitions

* `TauCeti.coeffSum`: the augmentation of `k[X]`, the linear map summing all coefficients.
* `TauCeti.permutationSum`: the sum of the standard basis of `k[X]`, for a finite `X`.
* `TauCeti.invariantLine`: the line spanned by `TauCeti.permutationSum`, as a subrepresentation.
* `TauCeti.augmentationSubrepresentation`: the kernel of `TauCeti.coeffSum`, as a
  subrepresentation.

## Main results

* `TauCeti.coeffSum_ofMulAction`: the augmentation is invariant, which is what makes both
  subrepresentations subrepresentations.
* `TauCeti.toRepresentation_invariantLine`: the invariant line carries the trivial representation,
  and `TauCeti.finrank_invariantLine` says it is a line.
* `TauCeti.ker_coeffSum_eq_span`: the augmentation subrepresentation is spanned by the differences
  of the standard basis vectors from a fixed one.
* `TauCeti.isCompl_invariantLine_augmentationSubrepresentation`: when `|X|` is invertible in `k`
  the two subrepresentations are complementary.
* `TauCeti.finrank_augmentationSubrepresentation`: the augmentation subrepresentation has
  dimension `|X| - 1`.

## Implementation notes

The augmentation here is a `k`-linear map on the free module `k[X]` of an arbitrary index type `X`,
because that is what a permutation representation acts on.  It is therefore *not* an instance of
`TauCeti.MonoidAlgebra.augmentation` of `TauCeti.Algebra.MonoidAlgebra.Exactness`, which is the
ring homomorphism `k[M] →+* k` of a monoid algebra: a `G`-set carries no multiplication, so there
is no ring structure on `k[X]` for a ring homomorphism to be defined on.  On the overlap, `X` a
monoid, the two maps agree, both sending `single x a` to `a`.

Invertibility of `|X|` in `k`, rather than an ordered field or an averaging operator, is what the
splitting needs, and it is the sharp hypothesis: if `|X| = 0` in `k` then `permutationSum` itself
lies in the augmentation subrepresentation, and the two are not complementary.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.3, where the permutation
  representation of a group on a finite set is split into the invariant line and its complement.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles", which asks for the standard representation of the
  symmetric group as the complement of the trivial one in a permutation module.
-/

public section

namespace TauCeti

/-! ### The augmentation -/

section Augmentation

variable (k : Type*) [CommSemiring k] (X : Type*)

/-- The **augmentation** of `k[X]`: the linear map sending an element to the sum of its
coefficients.  Equivalently, it is the unique linear map sending every standard basis vector
to `1`. -/
noncomputable def coeffSum : MonoidAlgebra k X →ₗ[k] k :=
  (Finsupp.lsum k fun _ : X => LinearMap.id) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k X}

/-- The augmentation sums the coefficients over the support. -/
theorem coeffSum_apply (v : MonoidAlgebra k X) : coeffSum k X v = v.coeff.sum fun _ a => a := by
  simp [coeffSum, Finsupp.sum]

/-- The augmentation sends a standard basis vector to its coefficient. -/
@[simp]
theorem coeffSum_single (x : X) (a : k) : coeffSum k X (MonoidAlgebra.single x a) = a := by
  rw [coeffSum_apply, MonoidAlgebra.coeff_single, Finsupp.sum_single_index rfl]

/-- Over a finite index type the augmentation is the sum of all the coefficients. -/
theorem coeffSum_eq_sum [Fintype X] (v : MonoidAlgebra k X) :
    coeffSum k X v = ∑ x : X, v.coeff x := by
  rw [coeffSum_apply, Finsupp.sum_fintype _ _ fun _ => rfl]

/-- The augmentation is surjective as soon as there is a standard basis vector to hit `1`. -/
theorem coeffSum_surjective [Nonempty X] : Function.Surjective (coeffSum k X) := fun a =>
  ⟨MonoidAlgebra.single (Classical.arbitrary X) a, coeffSum_single _ _⟩

end Augmentation

/-! ### The augmentation subrepresentation -/

section Subrep

variable (k : Type*) [CommSemiring k] (G X : Type*) [Group G] [MulAction G X]

/-- The augmentation is invariant: a group element permutes the standard basis, so it does not
change the sum of the coefficients. -/
@[simp]
theorem coeffSum_ofMulAction (g : G) (v : MonoidAlgebra k X) :
    coeffSum k X (Representation.ofMulAction k G X g v) = coeffSum k X v := by
  have hcoeff : (Representation.ofMulAction k G X g v).coeff =
      Finsupp.mapDomain (g • ·) v.coeff := by
    simp [Representation.ofMulAction_def]
  rw [coeffSum_apply, coeffSum_apply, hcoeff,
    Finsupp.sum_mapDomain_index_inj (MulAction.injective g)]

/-- The **augmentation subrepresentation** of `k[X]`: the elements whose coefficients sum to
zero. -/
noncomputable def augmentationSubrepresentation :
    Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := LinearMap.ker (coeffSum k X)
  apply_mem_toSubmodule g v hv := by
    simpa only [LinearMap.mem_ker, coeffSum_ofMulAction] using hv

@[simp]
theorem toSubmodule_augmentationSubrepresentation :
    (augmentationSubrepresentation k G X).toSubmodule = LinearMap.ker (coeffSum k X) :=
  -- `(rfl)`, not `rfl`: the body of `augmentationSubrepresentation` is not `@[expose]`d, so this
  -- must not be inferred `@[defeq]`.
  (rfl)

variable {k G X}

@[simp]
theorem mem_augmentationSubrepresentation_iff {v : MonoidAlgebra k X} :
    v ∈ augmentationSubrepresentation k G X ↔ coeffSum k X v = 0 :=
  Iff.rfl

end Subrep

section SubrepRing

variable {k : Type*} [CommRing k] {G X : Type*} [Group G] [MulAction G X]

/-- A difference of two standard basis vectors has vanishing augmentation. -/
theorem single_sub_single_mem_augmentationSubrepresentation (x y : X) :
    (MonoidAlgebra.single x 1 - MonoidAlgebra.single y 1 : MonoidAlgebra k X) ∈
      augmentationSubrepresentation k G X := by
  simp

end SubrepRing

/-! ### The invariant line -/

section PermutationSum

variable (k : Type*) [CommSemiring k] (X : Type*) [Fintype X]

/-- The sum of the standard basis of `k[X]`, for a finite index type. -/
noncomputable def permutationSum : MonoidAlgebra k X := ∑ x : X, MonoidAlgebra.single x (1 : k)

variable {k X}

@[simp]
theorem coeff_permutationSum (x : X) : (permutationSum k X).coeff x = 1 := by
  classical
  simp [permutationSum, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']

/-- The augmentation of the sum of the standard basis is the cardinality of the index type. -/
@[simp]
theorem coeffSum_permutationSum : coeffSum k X (permutationSum k X) = Fintype.card X := by
  rw [coeffSum_eq_sum]
  simp

/-- The sum of the standard basis is nonzero, since each of its coefficients is `1`. -/
theorem permutationSum_ne_zero [Nonempty X] [Nontrivial k] : permutationSum k X ≠ 0 := by
  intro h
  have hone := coeff_permutationSum (k := k) (Classical.arbitrary X)
  rw [h] at hone
  simp at hone

end PermutationSum

section InvariantLine

variable (k : Type*) [CommSemiring k] (G X : Type*) [Group G] [MulAction G X] [Fintype X]

/-- A group element fixes the sum of the standard basis, since it permutes the summands. -/
@[simp]
theorem ofMulAction_permutationSum (g : G) :
    Representation.ofMulAction k G X g (permutationSum k X) = permutationSum k X := by
  rw [permutationSum, map_sum]
  simp only [Representation.ofMulAction_single]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ fun _ => rfl

/-- The **invariant line** of `k[X]`: the line spanned by the sum of the standard basis, as a
subrepresentation. -/
noncomputable def invariantLine : Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := Submodule.span k {permutationSum k X}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, ofMulAction_permutationSum]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

@[simp]
theorem toSubmodule_invariantLine :
    (invariantLine k G X).toSubmodule = Submodule.span k {permutationSum k X} :=
  -- `(rfl)`, not `rfl`: the body of `invariantLine` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

/-- The invariant line carries the trivial representation: the sum of the standard basis, and
hence every multiple of it, is fixed. -/
theorem toRepresentation_invariantLine :
    (invariantLine k G X).toRepresentation = Representation.trivial k G _ := by
  refine DFunLike.ext _ _ fun g => LinearMap.ext fun w => Subtype.ext ?_
  have hw : (w : MonoidAlgebra k X) ∈ Submodule.span k {permutationSum k X} := by
    rw [← toSubmodule_invariantLine k G X]; exact w.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  change Representation.ofMulAction k G X g (w : MonoidAlgebra k X) = (w : MonoidAlgebra k X)
  rw [← hc, map_smul, ofMulAction_permutationSum]

end InvariantLine

/-! ### The splitting -/

section Field

variable (k : Type*) [Field k] (G X : Type*) [Group G] [MulAction G X]

/-- The augmentation subrepresentation is spanned by the differences of the standard basis vectors
from a fixed one. -/
theorem ker_coeffSum_eq_span (x₀ : X) :
    LinearMap.ker (coeffSum k X) =
      Submodule.span k (Set.range fun x : X =>
        (MonoidAlgebra.single x 1 - MonoidAlgebra.single x₀ 1 : MonoidAlgebra k X)) := by
  classical
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · rw [LinearMap.mem_ker, coeffSum_apply, Finsupp.sum] at hv
    have hbasis : ∑ x ∈ v.coeff.support, MonoidAlgebra.single x (v.coeff x) = v :=
      MonoidAlgebra.sum_coeff_single v
    have key : ∑ x ∈ v.coeff.support, v.coeff x •
        (MonoidAlgebra.single x 1 - MonoidAlgebra.single x₀ 1 : MonoidAlgebra k X) = v := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hv, zero_smul, sub_zero]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans hbasis
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [← key]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    simp

variable [Fintype X]

/-- The invariant line is a line. -/
@[simp]
theorem finrank_invariantLine [Nonempty X] :
    Module.finrank k (invariantLine k G X).toSubmodule = 1 := by
  rw [toSubmodule_invariantLine]
  exact finrank_span_singleton permutationSum_ne_zero

variable {k G X}

/-- **The permutation representation splits.**  When the cardinality of `X` is invertible in `k`,
the invariant line and the augmentation subrepresentation are complementary, so `k[X]` is the
direct sum of a trivial representation and a representation of dimension `|X| - 1`. -/
theorem isCompl_invariantLine_augmentationSubrepresentation (h : (Fintype.card X : k) ≠ 0) :
    IsCompl (invariantLine k G X) (augmentationSubrepresentation k G X) := by
  have hsub : IsCompl (Submodule.span k {permutationSum k X}) (LinearMap.ker (coeffSum k X)) := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro v hv hv'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [LinearMap.mem_ker, map_smul, coeffSum_permutationSum, smul_eq_mul] at hv'
      rw [(mul_eq_zero.mp hv').resolve_right h, zero_smul]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      refine Submodule.mem_sup.mpr ⟨(coeffSum k X v / Fintype.card X) • permutationSum k X,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        v - (coeffSum k X v / Fintype.card X) • permutationSum k X, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, coeffSum_permutationSum, smul_eq_mul,
        div_mul_cancel₀ _ h, sub_self]
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hsub.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hsub.sup_eq_top

/-- The augmentation subrepresentation has dimension one less than the cardinality of `X`. -/
theorem finrank_augmentationSubrepresentation [Nonempty X] :
    Module.finrank k (augmentationSubrepresentation k G X).toSubmodule = Fintype.card X - 1 := by
  have hcard : Module.finrank k (MonoidAlgebra k X) = Fintype.card X :=
    (Module.finrank_eq_card_basis (MonoidAlgebra.basis X k)).trans (by simp)
  have : Module.Finite k (MonoidAlgebra k X) := Module.Finite.of_basis (MonoidAlgebra.basis X k)
  have hrange : Module.finrank k (LinearMap.range (coeffSum k X)) = 1 := by
    rw [LinearMap.range_eq_top.mpr coeffSum_surjective]
    simp
  have hsum := LinearMap.finrank_range_add_finrank_ker (coeffSum k X)
  rw [hrange, hcard] at hsum
  rw [toSubmodule_augmentationSubrepresentation]
  omega

end Field

end TauCeti
