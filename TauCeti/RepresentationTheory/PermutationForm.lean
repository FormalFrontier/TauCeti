/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The invariant form on a permutation representation

A permutation representation `k[X]` of a group `G` on a `G`-set `X` carries a canonical bilinear
form, the one for which the standard basis `single x 1` is orthonormal: the pairing of `v` and `w`
is the sum of `v x * w x` over the (finite) support of `v`.  Because the action of a group element
permutes the standard basis, this **permutation form** is invariant, and the orthogonal complement
of an invariant submodule is again invariant.

Over an ordered ring the form is positive definite, so its restriction to *any* submodule is
nondegenerate, and over an ordered field the orthogonal complement of a subrepresentation is a
genuine complement.  This exhibits a canonical invariant complement of a subrepresentation of a
permutation representation: one that needs no averaging operator and no hypothesis on `G`, and
whose orthogonality relation is a tool in its own right.  An ordered field has characteristic zero,
so the complementation statements say nothing about positive characteristic; what they drop
relative to Maschke's theorem is finiteness of `G` and invertibility of `|G|`.

## Main definitions

* `TauCeti.permutationForm`: the bilinear form on `k[X]` making the standard basis orthonormal.
* `TauCeti.orthogonalSubrepresentation`: the orthogonal complement of a subrepresentation of a
  permutation representation, as a subrepresentation.

## Main results

* `TauCeti.permutationForm_single_single`: the standard basis is orthonormal.
* `TauCeti.permutationForm_isSymm` and `TauCeti.permutationForm_nondegenerate`: the form is
  symmetric and nondegenerate over any commutative ring.
* `TauCeti.permutationForm_ofMulAction_invariant`: the action of a group element preserves the
  form, and `TauCeti.permutationForm_ofMulAction_left` moves that action across the form by
  inverting it.
* `TauCeti.orthogonal_mem_invtSubmodule`: the orthogonal complement of an invariant submodule of a
  permutation representation is invariant.
* `TauCeti.permutationForm_self_pos` and `TauCeti.permutationForm_restrict_nondegenerate`: over an
  ordered ring the form is positive definite, hence nondegenerate on every submodule.
* `TauCeti.isCompl_orthogonalSubrepresentation`: over an ordered field, and for a finite `G`-set,
  a subrepresentation is complemented by its orthogonal complement.

## Implementation notes

The form is defined on `MonoidAlgebra k X` rather than on `X →₀ k` because that is the module
Mathlib's `Representation.ofMulAction` acts on.  Here `X` carries no multiplication and the
monoid-algebra product plays no role; only the free module on `X` and its standard basis do.  For a
finite `X` the form is the one with identity Gram matrix, which under the identification of `k[X]`
with `X → k` is Mathlib's `Matrix.toBilin' 1`; the definition below is stated with `Finsupp.sum` so
that it needs no finiteness and no `DecidableEq X`.

Positive definiteness, not invertibility of `|G|`, is what drives the complementation statements,
which is why they ask for an ordered field rather than for a finite group. In particular nothing
below reproves Maschke's theorem: the content is that the complement can be taken orthogonal, so
that a submodule and its complement are separated by an explicit pairing.

The orthogonal-complement half of this file is the bilinear-form transcription of an existing
TauCeti development: `ofMulAction_mem_orthogonal`, `orthogonal_mem_invtSubmodule`,
`orthogonalSubrepresentation`, `toSubmodule_orthogonalSubrepresentation` and
`isCompl_orthogonalSubrepresentation` follow, statement for statement and proof for proof, their
namesakes in `TauCeti.RepresentationTheory.Continuous.InvariantComplement`, with
`IsUnitary.inner_map_right` replaced by `permutationForm_ofMulAction_left` and
`Submodule.isCompl_orthogonal` by
`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`.  The two cannot be unified:
that file works over an inner-product space, which is unavailable over `ℚ`.

## References

* `TauCeti.RepresentationTheory.Continuous.InvariantComplement`, the unitary orthogonal-complement
  API this file adapts to a bilinear form, as described in the implementation notes above.
* G. D. James, *The Representation Theory of the Symmetric Groups*, Chapter 1, where this form is
  introduced on the permutation module of a Young subgroup and used for the submodule theorem.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, which asks for the tabloid bilinear form and its orthogonality API.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

/-! ### The permutation form -/

section Ring

variable (k : Type*) [CommSemiring k] (X : Type*)

/-- The **permutation form** on `k[X]`: the bilinear form for which the standard basis of `k[X]`
is orthonormal.  On a pair of elements it is the sum of the products of matching coefficients. -/
noncomputable def permutationForm : BilinForm k (MonoidAlgebra k X) :=
  Finsupp.lsum k (fun x : X => LinearMap.toSpanSingleton k (MonoidAlgebra k X →ₗ[k] k)
      (Finsupp.lapply x ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

variable {k X}

/-- The permutation form pairs two elements by summing the products of matching coefficients over
the support of the left argument. -/
theorem permutationForm_apply (v w : MonoidAlgebra k X) :
    permutationForm k X v w = v.coeff.sum fun x a => a * w.coeff x := by
  simp [permutationForm, Finsupp.sum, LinearMap.toSpanSingleton_apply]

/-- Pairing with a standard basis vector reads off a coefficient. -/
@[simp]
theorem permutationForm_single_left (x : X) (a : k) (w : MonoidAlgebra k X) :
    permutationForm k X (MonoidAlgebra.single x a) w = a * w.coeff x := by
  rw [permutationForm_apply, MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

/-- The permutation form is symmetric: both sides are the sum of `v x * w x` over the union of the
two supports. -/
theorem permutationForm_comm (v w : MonoidAlgebra k X) :
    permutationForm k X v w = permutationForm k X w v := by
  classical
  have h₁ : (v.coeff.sum fun x a => a * w.coeff x) =
      ∑ x ∈ v.coeff.support ∪ w.coeff.support, v.coeff x * w.coeff x :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (by simp)
  have h₂ : (w.coeff.sum fun x a => a * v.coeff x) =
      ∑ x ∈ v.coeff.support ∪ w.coeff.support, w.coeff x * v.coeff x :=
    Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (by simp)
  rw [permutationForm_apply, permutationForm_apply, h₁, h₂]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The permutation form is symmetric. -/
theorem permutationForm_isSymm : (permutationForm k X).IsSymm :=
  ⟨fun v w => permutationForm_comm v w⟩

/-- The permutation form is reflexive, so its orthogonal complement has no chirality. -/
theorem permutationForm_isRefl : (permutationForm k X).IsRefl :=
  permutationForm_isSymm.isRefl

/-- Pairing with a standard basis vector on the right reads off a coefficient. -/
@[simp]
theorem permutationForm_single_right (v : MonoidAlgebra k X) (x : X) (a : k) :
    permutationForm k X v (MonoidAlgebra.single x a) = v.coeff x * a := by
  rw [permutationForm_comm, permutationForm_single_left, mul_comm]

/-- The standard basis of `k[X]` is orthonormal for the permutation form. -/
theorem permutationForm_single_single (x y : X) [Decidable (x = y)] (a b : k) :
    permutationForm k X (MonoidAlgebra.single x a) (MonoidAlgebra.single y b) =
      if x = y then a * b else 0 := by
  classical
  rw [permutationForm_single_left, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h, Ne.symm h]

/-- An element pairing to zero with everything on the right is zero: it is enough to pair it with
the standard basis vectors. -/
theorem permutationForm_separatingLeft : (permutationForm k X).SeparatingLeft := by
  intro v hv
  rw [← MonoidAlgebra.coeff_eq_zero]
  ext x
  simpa using hv (MonoidAlgebra.single x 1)

/-- The permutation form is nondegenerate: an element pairing to zero with every standard basis
vector has all coefficients zero. -/
theorem permutationForm_nondegenerate : (permutationForm k X).Nondegenerate :=
  ⟨permutationForm_separatingLeft, fun v hv =>
    permutationForm_separatingLeft v fun w => by rw [permutationForm_comm]; exact hv w⟩

end Ring

/-! ### Positive definiteness over an ordered ring -/

section Ordered

variable {k : Type*} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k] {X : Type*}

/-- Over an ordered ring the permutation form is positive definite. -/
theorem permutationForm_self_pos {v : MonoidAlgebra k X} (hv : v ≠ 0) :
    0 < permutationForm k X v v := by
  rw [permutationForm_apply, Finsupp.sum]
  refine Finset.sum_pos (fun x hx => mul_self_pos.mpr (Finsupp.mem_support_iff.mp hx)) ?_
  exact Finsupp.support_nonempty_iff.mpr (by simpa using hv)

/-- Over an ordered ring an element is isotropic for the permutation form only if it is zero. -/
@[simp]
theorem permutationForm_self_eq_zero_iff {v : MonoidAlgebra k X} :
    permutationForm k X v v = 0 ↔ v = 0 := by
  refine ⟨fun h => by_contra fun hv => ?_, fun h => by simp [h]⟩
  exact (permutationForm_self_pos hv).ne' h

/-- A positive definite form stays nondegenerate on every submodule, which is what makes the
orthogonal complement below a genuine complement. -/
theorem permutationForm_restrict_nondegenerate (W : Submodule k (MonoidAlgebra k X)) :
    ((permutationForm k X).restrict W).Nondegenerate := by
  have key : ∀ v : W, permutationForm k X v v = 0 → v = 0 := fun v h =>
    Submodule.coe_eq_zero.mp (permutationForm_self_eq_zero_iff.mp h)
  exact ⟨fun v hv => key v (by simpa using hv v), fun v hv => key v (by simpa using hv v)⟩

end Ordered

/-! ### Invariance under a permutation action -/

section MulAction

variable {k : Type*} [CommSemiring k] {G X : Type*} [Group G] [MulAction G X]

/-- The action of a group element permutes the standard basis of `k[X]`, so it preserves the
permutation form. -/
@[simp]
theorem permutationForm_ofMulAction_invariant (g : G) (v w : MonoidAlgebra k X) :
    permutationForm k X (Representation.ofMulAction k G X g v)
        (Representation.ofMulAction k G X g w) = permutationForm k X v w := by
  have hcoeff : (Representation.ofMulAction k G X g v).coeff =
      Finsupp.mapDomain (g • ·) v.coeff := by
    simp [Representation.ofMulAction_def]
  rw [permutationForm_apply, permutationForm_apply, hcoeff,
    Finsupp.sum_mapDomain_index_inj (MulAction.injective g)]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Representation.coeff_ofMulAction, inv_smul_smul]

/-- Moving the action of a group element across the permutation form replaces it by its inverse.
This is the shape in which invariance is used to compare a submodule with an orthogonal
complement. -/
theorem permutationForm_ofMulAction_left (g : G) (v w : MonoidAlgebra k X) :
    permutationForm k X (Representation.ofMulAction k G X g v) w =
      permutationForm k X v (Representation.ofMulAction k G X g⁻¹ w) := by
  conv_lhs => rw [← Representation.self_inv_apply (Representation.ofMulAction k G X) g w]
  exact permutationForm_ofMulAction_invariant g v _

/-- The action carries the orthogonal complement of an invariant submodule into itself. -/
theorem ofMulAction_mem_orthogonal {W : Submodule k (MonoidAlgebra k X)}
    (hW : ∀ g : G, ∀ v ∈ W, Representation.ofMulAction k G X g v ∈ W) (g : G)
    {v : MonoidAlgebra k X} (hv : v ∈ (permutationForm k X).orthogonal W) :
    Representation.ofMulAction k G X g v ∈ (permutationForm k X).orthogonal W := by
  intro u hu
  rw [permutationForm_comm, permutationForm_ofMulAction_left, permutationForm_comm]
  exact hv _ (hW g⁻¹ u hu)

/-- **Invariant orthogonal complements.**  The orthogonal complement of an invariant submodule of
a permutation representation is again invariant. -/
theorem orthogonal_mem_invtSubmodule {W : Submodule k (MonoidAlgebra k X)}
    (hW : W ∈ (Representation.ofMulAction k G X).invtSubmodule) :
    (permutationForm k X).orthogonal W ∈ (Representation.ofMulAction k G X).invtSubmodule := by
  rw [Representation.mem_invtSubmodule] at hW ⊢
  exact fun g _ hv => ofMulAction_mem_orthogonal (fun g' _ hu => hW g' hu) g hv

/-- The orthogonal complement of a subrepresentation of a permutation representation, as a
subrepresentation. -/
noncomputable def orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := (permutationForm k X).orthogonal σ.toSubmodule
  apply_mem_toSubmodule g _ hv :=
    ofMulAction_mem_orthogonal (fun g' _ hu => σ.apply_mem_toSubmodule g' hu) g hv

/-- The underlying submodule of the orthogonal complement of a subrepresentation. -/
@[simp]
theorem toSubmodule_orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    (orthogonalSubrepresentation σ).toSubmodule =
      (permutationForm k X).orthogonal σ.toSubmodule :=
  -- `(rfl)`, not `rfl`: the body of `orthogonalSubrepresentation` is not `@[expose]`d, so this
  -- must not be inferred `@[defeq]`.
  (rfl)

end MulAction

/-! ### Complementation over an ordered field -/

section OrderedField

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  {G X : Type*} [Group G] [MulAction G X] [Finite X]

/-- **Invariant complements without averaging.**  Over an ordered field a subrepresentation of the
permutation representation on a finite `G`-set is complemented by its orthogonal complement.  No
hypothesis on `G` is needed: neither finiteness nor invertibility of `|G|`.  The ordered field is
of characteristic zero, so this is not a statement about positive characteristic. -/
theorem isCompl_orthogonalSubrepresentation
    (σ : Subrepresentation (Representation.ofMulAction k G X)) :
    IsCompl σ (orthogonalSubrepresentation σ) := by
  haveI : Module.Finite k (MonoidAlgebra k X) := Module.Finite.of_basis (MonoidAlgebra.basis X k)
  have h : IsCompl σ.toSubmodule ((permutationForm k X).orthogonal σ.toSubmodule) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate permutationForm_isRefl
      (permutationForm_restrict_nondegenerate σ.toSubmodule)
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top

end OrderedField

end TauCeti
