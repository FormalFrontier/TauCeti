/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Homogeneous multilinear maps

This file records the degree of a multilinear map between modules equipped with families of
graded subobjects. A multilinear map has degree `q` when it maps inputs lying in `𝒜 i (d i)`
into `ℬ ((∑ i, d i) + q)`; as in the linear case
(`TauCeti.LinearAlgebra.Graded.LinearMap`) this is a containment condition, so no direct-sum
hypothesis is imposed and a map can have several degrees at once.

The main results show that degrees add under composition, both for precomposition by a family of
linear maps and for simultaneous substitution of multilinear maps. The composition operations are
Mathlib's `MultilinearMap.compLinearMap` and `MultilinearMap.compMultilinearMap`; this file supplies
their unsigned degree calculations, which underlie signed substitution for DG and `A∞` structures.

## Main definitions

* `MultilinearMap.IsHomogeneous`: a multilinear map shifts the sum of its input degrees.
* `MultilinearMap.homogeneousSubmodule`: the submodule of multilinear maps of a fixed degree.

## Main results

* `MultilinearMap.IsHomogeneous.compLinearMap`: precomposing the inputs by homogeneous linear
  maps adds their degrees to the degree of the multilinear map.
* `MultilinearMap.IsHomogeneous.compMultilinearMap`: simultaneously substituting homogeneous
  multilinear maps adds their degrees to the degree of the outer map; the composite is indexed by
  the sigma type `Σ i, β i`.
* `MultilinearMap.IsHomogeneous.domDomCongrLinearEquiv'`: reindexing the inputs along an
  equivalence preserves the degree, which turns a sigma-indexed composite into one of any
  equivalent arity.
* `LinearMap.IsHomogeneous.compMultilinearMap`: postcomposing by a homogeneous linear map adds
  its degree.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

open scoped BigOperators

universe uR uι uκ uβ uM uN uP

namespace MultilinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN} {σM : κ → Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
  [∀ i, Module R (M i)] [Module R N]
  [∀ i, SetLike (σM i) (M i)] [SetLike σN N]

/-- A multilinear map is homogeneous of degree `q` if it maps inputs lying in `𝒜 i (d i)` into
`ℬ ((∑ i, d i) + q)`. No direct-sum hypothesis on the families is needed. -/
def IsHomogeneous (f : MultilinearMap R M N)
    (𝒜 : (i : κ) → ι → σM i) (ℬ : ι → σN) (q : ι) : Prop :=
  ∀ (d : κ → ι) (x : ∀ i, M i),
    (∀ i, x i ∈ 𝒜 i (d i)) → f x ∈ ℬ ((∑ i, d i) + q)

/-- Homogeneity of degree `q` is exactly the mapping condition on homogeneous inputs. This is a
convenient introduction rule, and `IsHomogeneous.map_mem` is the corresponding elimination rule. -/
theorem isHomogeneous_def {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι} :
    IsHomogeneous f 𝒜 ℬ q ↔
      ∀ (d : κ → ι) (x : ∀ i, M i), (∀ i, x i ∈ 𝒜 i (d i)) → f x ∈ ℬ ((∑ i, d i) + q) :=
  Iff.rfl

/-- Apply a homogeneous multilinear map to homogeneous inputs. -/
theorem IsHomogeneous.map_mem {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (d : κ → ι) (x : ∀ i, M i)
    (hx : ∀ i, x i ∈ 𝒜 i (d i)) :
    f x ∈ ℬ ((∑ i, d i) + q) :=
  hf d x hx

/-- The zero multilinear map is homogeneous of every degree. -/
@[simp]
theorem isHomogeneous_zero [ZeroMemClass σN N] (𝒜 : (i : κ) → ι → σM i)
    (ℬ : ι → σN) (q : ι) :
    IsHomogeneous (0 : MultilinearMap R M N) 𝒜 ℬ q := by
  intro d x _
  simp

/-- A sum of multilinear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.add [AddMemClass σN N] {f g : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f + g) 𝒜 ℬ q := by
  intro d x hx
  simpa using add_mem (hf d x hx) (hg d x hx)

/-- Precomposing each input by a homogeneous linear map adds all of their degrees to the degree
of the multilinear map. -/
@[grind .]
theorem IsHomogeneous.compLinearMap
    {M' : κ → Type uP} {σM' : κ → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    [∀ i, SetLike (σM' i) (M' i)]
    {f : MultilinearMap R M N} {g : ∀ i, M' i →ₗ[R] M i}
    {𝒜 : (i : κ) → ι → σM' i}
    {ℬ : (i : κ) → ι → σM i} {𝒞 : ι → σN}
    {q : ι} {r : κ → ι} (hf : IsHomogeneous f ℬ 𝒞 q)
    (hg : ∀ i, LinearMap.IsHomogeneous (g i) (𝒜 i) (ℬ i) (r i)) :
    IsHomogeneous (f.compLinearMap g) 𝒜 𝒞 ((∑ i, r i) + q) := by
  intro d x hx
  -- the input `g i (x i)` of `f` has degree `d i + r i`, and these degrees add up correctly
  have hdeg : (∑ i, (d i + r i)) + q = (∑ i, d i) + ((∑ i, r i) + q) := by
    rw [Finset.sum_add_distrib, add_assoc]
  have h := hf.map_mem (fun i ↦ d i + r i) (fun i ↦ g i (x i)) fun i ↦ (hg i).map_mem (hx i)
  rw [hdeg] at h
  simpa only [_root_.MultilinearMap.compLinearMap_apply] using h

/-- Simultaneous substitution of homogeneous multilinear maps adds the degrees of all substituted
maps to the degree of the outer map. -/
theorem IsHomogeneous.compMultilinearMap
    {β : κ → Type uβ} [∀ i, Fintype (β i)]
    {P : (i : κ) → β i → Type uP} {σP : (i : κ) → β i → Type*}
    [∀ i j, AddCommMonoid (P i j)] [∀ i j, Module R (P i j)]
    [∀ i j, SetLike (σP i j) (P i j)]
    {f : MultilinearMap R M N} {g : (i : κ) → MultilinearMap R (P i) (M i)}
    {𝒜 : (i : κ) → (j : β i) → ι → σP i j}
    {ℬ : (i : κ) → ι → σM i} {𝒞 : ι → σN}
    {q : ι} {r : κ → ι} (hf : IsHomogeneous f ℬ 𝒞 q)
    (hg : ∀ i, IsHomogeneous (g i) (𝒜 i) (ℬ i) (r i)) :
    IsHomogeneous (f.compMultilinearMap g)
      (fun ij ↦ 𝒜 ij.1 ij.2) 𝒞 ((∑ i, r i) + q) := by
  intro d x hx
  -- the `i`-th input `g i (Sigma.curry x i)` of `f` has degree `(∑ j, d ⟨i, j⟩) + r i`; summing
  -- these over `i` reassembles the total input degree `∑ ij, d ij` of the composite
  have hdeg : (∑ i, ((∑ j, d ⟨i, j⟩) + r i)) + q = (∑ ij, d ij) + ((∑ i, r i) + q) := by
    rw [Finset.sum_add_distrib, Fintype.sum_sigma, add_assoc]
  -- `Sigma.curry x i j` is definitionally `x ⟨i, j⟩`
  have hcurry : ∀ (i : κ) (j : β i), Sigma.curry x i j = x ⟨i, j⟩ := fun _ _ ↦ rfl
  have h := hf.map_mem (fun i ↦ (∑ j, d ⟨i, j⟩) + r i) (fun i ↦ g i (Sigma.curry x i))
    fun i ↦ (hg i).map_mem (fun j ↦ d ⟨i, j⟩) (Sigma.curry x i) fun j ↦ by
      rw [hcurry i j]; exact hx ⟨i, j⟩
  rw [hdeg] at h
  simpa only [_root_.MultilinearMap.compMultilinearMap_apply] using h

/-- Reindexing the inputs of a homogeneous multilinear map along an equivalence of index types
preserves its degree. -/
@[grind .]
theorem IsHomogeneous.domDomCongrLinearEquiv' {κ' : Type*} [Fintype κ']
    (σ : κ ≃ κ')
    {f : MultilinearMap R M N} {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (_root_.MultilinearMap.domDomCongrLinearEquiv' R ℕ M N σ f)
      (fun i ↦ 𝒜 (σ.symm i)) ℬ q := by
  intro d x hx
  -- reindexing does not change the total input degree
  have hdeg : ∑ i, d (σ i) = ∑ i, d i := Fintype.sum_equiv σ _ _ fun _ ↦ rfl
  have h := hf.map_mem (fun i ↦ d (σ i)) ((σ.piCongrLeft' M).symm x) fun i ↦ by
    obtain ⟨j, rfl⟩ : ∃ j, i = σ.symm j := ⟨σ i, (σ.symm_apply_apply i).symm⟩
    simpa using hx j
  rw [hdeg] at h
  simpa only [_root_.MultilinearMap.domDomCongrLinearEquiv'_apply,
    _root_.MultilinearMap.coe_mk, Function.comp_apply] using h

end Semiring

section Neg

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN} {σM : κ → Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommGroup N]
  [∀ i, Module R (M i)] [Module R N]
  [∀ i, SetLike (σM i) (M i)] [SetLike σN N]

/-- The negative of a homogeneous multilinear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.neg [NegMemClass σN N] {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) :
    IsHomogeneous (-f) 𝒜 ℬ q := by
  intro d x hx
  simpa using neg_mem (hf d x hx)

/-- A difference of multilinear maps of the same degree has that degree. -/
@[grind ←]
theorem IsHomogeneous.sub [AddMemClass σN N] [NegMemClass σN N] {f g : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (hg : IsHomogeneous g 𝒜 ℬ q) :
    IsHomogeneous (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Neg

section Scalars

variable {R : Type uR} {S : Type*} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN} {σM : κ → Type*} {σN : Type*}
  [Semiring R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
  [∀ i, Module R (M i)] [Module R N]
  [∀ i, SetLike (σM i) (M i)] [SetLike σN N]

/-- A scalar multiple of a homogeneous multilinear map has the same degree. -/
@[grind ←]
theorem IsHomogeneous.smul [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    [SMulMemClass σN S N] {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι}
    (hf : IsHomogeneous f 𝒜 ℬ q) (s : S) :
    IsHomogeneous (s • f) 𝒜 ℬ q := by
  intro d x hx
  simpa using SMulMemClass.smul_mem s (hf d x hx)

/-- Multilinear maps of a fixed degree form a submodule over any scalar ring acting on the
target. -/
def homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N]
    (𝒜 : (i : κ) → ι → σM i) (ℬ : ι → σN) (q : ι) :
    Submodule S (MultilinearMap R M N) where
  carrier := {f | IsHomogeneous f 𝒜 ℬ q}
  zero_mem' := isHomogeneous_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' s _ hf := hf.smul s

@[simp, grind =]
theorem mem_homogeneousSubmodule [Semiring S] [Module S N] [SMulCommClass R S N]
    [AddSubmonoidClass σN N] [SMulMemClass σN S N]
    {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {q : ι} :
    f ∈ homogeneousSubmodule (S := S) 𝒜 ℬ q ↔ IsHomogeneous f 𝒜 ℬ q :=
  Iff.rfl

end Scalars

end MultilinearMap

namespace LinearMap

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN} {P : Type uP} {σM : κ → Type*} {σN σP : Type*}
  [Semiring R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid N] [AddCommMonoid P]
  [∀ i, Module R (M i)] [Module R N] [Module R P]
  [∀ i, SetLike (σM i) (M i)] [SetLike σN N] [SetLike σP P]

/-- Postcomposing a homogeneous multilinear map by a homogeneous linear map adds their degrees. -/
@[grind →]
theorem IsHomogeneous.compMultilinearMap {f : MultilinearMap R M N} {g : N →ₗ[R] P}
    {𝒜 : (i : κ) → ι → σM i} {ℬ : ι → σN} {𝒞 : ι → σP} {q r : ι}
    (hg : IsHomogeneous g ℬ 𝒞 r) (hf : MultilinearMap.IsHomogeneous f 𝒜 ℬ q) :
    MultilinearMap.IsHomogeneous (g.compMultilinearMap f) 𝒜 𝒞 (q + r) := by
  intro d x hx
  simpa only [_root_.LinearMap.compMultilinearMap_apply, add_assoc] using
    hg.map_mem (hf d x hx)

end LinearMap

end TauCeti
