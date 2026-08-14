/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Homogeneous linear and multilinear maps

This file records the degree of a linear or multilinear map between modules equipped with
families of graded submodules. A multilinear map has degree `q` when it sends inputs of degrees
`d i` to an output of degree `(∑ i, d i) + q`.

The main results show that degrees add under composition, both for precomposition by a family of
linear maps and for simultaneous substitution of multilinear maps. The composition operations are
Mathlib's `MultilinearMap.compLinearMap` and `MultilinearMap.compMultilinearMap`; this file supplies
their unsigned degree calculations, which underlie signed substitution for DG and `A∞` structures.

## Main definitions

* `LinearMap.IsHomogeneousOfDegree`: a linear map shifts homogeneous degree by a fixed amount.
* `MultilinearMap.IsHomogeneousOfDegree`: a multilinear map shifts the sum of its input degrees.
* `LinearMap.homogeneousSubmodule`: the submodule of linear maps of a fixed degree.
* `MultilinearMap.homogeneousSubmodule`: the submodule of multilinear maps of a fixed degree.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

open scoped BigOperators

universe uR uι uκ uβ uM uN uP

namespace LinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN}
  [CommSemiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- A linear map is homogeneous of degree `q` if it maps the degree-`p` submodule into the
degree-`p + q` submodule. No direct-sum hypothesis on the families of submodules is needed. -/
def IsHomogeneousOfDegree (f : M →ₗ[R] N) (𝒜 : ι → Submodule R M)
    (ℬ : ι → Submodule R N) (q : ι) : Prop :=
  ∀ ⦃p : ι⦄ ⦃x : M⦄, x ∈ 𝒜 p → f x ∈ ℬ (p + q)

/-- Apply a homogeneous linear map to a homogeneous element. -/
theorem IsHomogeneousOfDegree.map_mem {f : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q p : ι} (hf : IsHomogeneousOfDegree f 𝒜 ℬ q)
    {x : M} (hx : x ∈ 𝒜 p) :
    f x ∈ ℬ (p + q) :=
  hf hx

/-- The zero linear map is homogeneous of every degree. -/
theorem isHomogeneousOfDegree_zero (𝒜 : ι → Submodule R M) (ℬ : ι → Submodule R N) (q : ι) :
    IsHomogeneousOfDegree (0 : M →ₗ[R] N) 𝒜 ℬ q := by
  intro p x hx
  simp

/-- A sum of linear maps of the same degree has that degree. -/
theorem IsHomogeneousOfDegree.add {f g : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q : ι} (hf : IsHomogeneousOfDegree f 𝒜 ℬ q)
    (hg : IsHomogeneousOfDegree g 𝒜 ℬ q) :
    IsHomogeneousOfDegree (f + g) 𝒜 ℬ q := by
  intro p x hx
  exact Submodule.add_mem _ (hf hx) (hg hx)

/-- A scalar multiple of a homogeneous linear map has the same degree. -/
theorem IsHomogeneousOfDegree.smul {f : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q : ι} (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) (r : R) :
    IsHomogeneousOfDegree (r • f) 𝒜 ℬ q := by
  intro p x hx
  exact Submodule.smul_mem _ r (hf hx)

/-- Linear maps of a fixed degree form a submodule. -/
def homogeneousSubmodule (𝒜 : ι → Submodule R M) (ℬ : ι → Submodule R N) (q : ι) :
    Submodule R (M →ₗ[R] N) where
  carrier := {f | IsHomogeneousOfDegree f 𝒜 ℬ q}
  zero_mem' := isHomogeneousOfDegree_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' r _ hf := hf.smul r

@[simp]
theorem mem_homogeneousSubmodule {f : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q : ι} :
    f ∈ homogeneousSubmodule 𝒜 ℬ q ↔ IsHomogeneousOfDegree f 𝒜 ℬ q :=
  Iff.rfl

/-- The identity linear map is homogeneous of degree zero. -/
theorem isHomogeneousOfDegree_id (𝒜 : ι → Submodule R M) :
    IsHomogeneousOfDegree (LinearMap.id : M →ₗ[R] M) 𝒜 𝒜 0 := by
  intro p x hx
  simpa using hx

/-- Degrees add under composition of linear maps. -/
theorem IsHomogeneousOfDegree.comp {P : Type uP} [AddCommMonoid P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {𝒞 : ι → Submodule R P} {q r : ι}
    (hg : IsHomogeneousOfDegree g ℬ 𝒞 r) (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) :
    IsHomogeneousOfDegree (g.comp f) 𝒜 𝒞 (q + r) := by
  intro p x hx
  simpa only [_root_.LinearMap.comp_apply, add_assoc] using hg (hf hx)

end Semiring

section Ring

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN}
  [CommRing R] [AddMonoid ι] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- The negative of a homogeneous linear map has the same degree. -/
theorem IsHomogeneousOfDegree.neg {f : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q : ι} (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) :
    IsHomogeneousOfDegree (-f) 𝒜 ℬ q := by
  intro p x hx
  exact Submodule.neg_mem _ (hf hx)

/-- A difference of linear maps of the same degree has that degree. -/
theorem IsHomogeneousOfDegree.sub {f g : M →ₗ[R] N} {𝒜 : ι → Submodule R M}
    {ℬ : ι → Submodule R N} {q : ι} (hf : IsHomogeneousOfDegree f 𝒜 ℬ q)
    (hg : IsHomogeneousOfDegree g 𝒜 ℬ q) :
    IsHomogeneousOfDegree (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Ring

end LinearMap

namespace MultilinearMap

section Semiring

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN}
  [CommSemiring R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
  [∀ i, Module R (M i)] [Module R N]

/-- A multilinear map is homogeneous of degree `q` if it sends homogeneous inputs of degrees
`d i` to an output of degree `(∑ i, d i) + q`. No direct-sum hypothesis on the families of
submodules is needed. -/
def IsHomogeneousOfDegree (f : MultilinearMap R M N)
    (𝒜 : (i : κ) → ι → Submodule R (M i)) (ℬ : ι → Submodule R N) (q : ι) : Prop :=
  ∀ (d : κ → ι) (x : ∀ i, M i),
    (∀ i, x i ∈ 𝒜 i (d i)) → f x ∈ ℬ ((∑ i, d i) + q)

/-- Apply a homogeneous multilinear map to homogeneous inputs. -/
theorem IsHomogeneousOfDegree.map_mem {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι}
    (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) (d : κ → ι) (x : ∀ i, M i)
    (hx : ∀ i, x i ∈ 𝒜 i (d i)) :
    f x ∈ ℬ ((∑ i, d i) + q) :=
  hf d x hx

/-- The zero multilinear map is homogeneous of every degree. -/
theorem isHomogeneousOfDegree_zero (𝒜 : (i : κ) → ι → Submodule R (M i))
    (ℬ : ι → Submodule R N) (q : ι) :
    IsHomogeneousOfDegree (0 : MultilinearMap R M N) 𝒜 ℬ q := by
  intro d x hx
  simp

/-- A sum of multilinear maps of the same degree has that degree. -/
theorem IsHomogeneousOfDegree.add {f g : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι}
    (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) (hg : IsHomogeneousOfDegree g 𝒜 ℬ q) :
    IsHomogeneousOfDegree (f + g) 𝒜 ℬ q := by
  intro d x hx
  exact Submodule.add_mem _ (hf d x hx) (hg d x hx)

/-- A scalar multiple of a homogeneous multilinear map has the same degree. -/
theorem IsHomogeneousOfDegree.smul {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι}
    (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) (r : R) :
    IsHomogeneousOfDegree (r • f) 𝒜 ℬ q := by
  intro d x hx
  exact Submodule.smul_mem _ r (hf d x hx)

/-- Multilinear maps of a fixed degree form a submodule. -/
def homogeneousSubmodule (𝒜 : (i : κ) → ι → Submodule R (M i))
    (ℬ : ι → Submodule R N) (q : ι) : Submodule R (MultilinearMap R M N) where
  carrier := {f | IsHomogeneousOfDegree f 𝒜 ℬ q}
  zero_mem' := isHomogeneousOfDegree_zero 𝒜 ℬ q
  add_mem' hf hg := hf.add hg
  smul_mem' r _ hf := hf.smul r

@[simp]
theorem mem_homogeneousSubmodule {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι} :
    f ∈ homogeneousSubmodule 𝒜 ℬ q ↔ IsHomogeneousOfDegree f 𝒜 ℬ q :=
  Iff.rfl

/-- Precomposing each input by a homogeneous linear map adds all of their degrees to the degree
of the multilinear map. -/
theorem IsHomogeneousOfDegree.compLinearMap
    {M' : κ → Type uP} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    {f : MultilinearMap R M N} {g : ∀ i, M' i →ₗ[R] M i}
    {𝒜 : (i : κ) → ι → Submodule R (M' i)}
    {ℬ : (i : κ) → ι → Submodule R (M i)} {𝒞 : ι → Submodule R N}
    {q : ι} {r : κ → ι} (hf : IsHomogeneousOfDegree f ℬ 𝒞 q)
    (hg : ∀ i, LinearMap.IsHomogeneousOfDegree (g i) (𝒜 i) (ℬ i) (r i)) :
    IsHomogeneousOfDegree (f.compLinearMap g) 𝒜 𝒞 ((∑ i, r i) + q) := by
  intro d x hx
  simpa only [_root_.MultilinearMap.compLinearMap_apply, Finset.sum_add_distrib, add_assoc] using
    hf (fun i ↦ d i + r i) (fun i ↦ g i (x i)) (fun i ↦ hg i (hx i))

/-- Simultaneous substitution of homogeneous multilinear maps adds the degrees of all substituted
maps to the degree of the outer map. -/
theorem IsHomogeneousOfDegree.compMultilinearMap
    {β : κ → Type uβ} [∀ i, Fintype (β i)]
    {P : (i : κ) → β i → Type uP}
    [∀ i j, AddCommMonoid (P i j)] [∀ i j, Module R (P i j)]
    {f : MultilinearMap R M N} {g : (i : κ) → MultilinearMap R (P i) (M i)}
    {𝒜 : (i : κ) → (j : β i) → ι → Submodule R (P i j)}
    {ℬ : (i : κ) → ι → Submodule R (M i)} {𝒞 : ι → Submodule R N}
    {q : ι} {r : κ → ι} (hf : IsHomogeneousOfDegree f ℬ 𝒞 q)
    (hg : ∀ i, IsHomogeneousOfDegree (g i) (𝒜 i) (ℬ i) (r i)) :
    IsHomogeneousOfDegree (f.compMultilinearMap g)
      (fun ij ↦ 𝒜 ij.1 ij.2) 𝒞 ((∑ i, r i) + q) := by
  intro d x hx
  simpa only [_root_.MultilinearMap.compMultilinearMap_apply, Fintype.sum_sigma,
    Finset.sum_add_distrib, add_assoc] using
    hf (fun i ↦ (∑ j, d ⟨i, j⟩) + r i) (fun i ↦ g i (Sigma.curry x i))
      (fun i ↦ hg i (fun j ↦ d ⟨i, j⟩) (Sigma.curry x i) (fun j ↦ hx ⟨i, j⟩))

end Semiring

section Ring

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN}
  [CommRing R] [AddCommMonoid ι] [Fintype κ]
  [∀ i, AddCommGroup (M i)] [AddCommGroup N]
  [∀ i, Module R (M i)] [Module R N]

/-- The negative of a homogeneous multilinear map has the same degree. -/
theorem IsHomogeneousOfDegree.neg {f : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι}
    (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) :
    IsHomogeneousOfDegree (-f) 𝒜 ℬ q := by
  intro d x hx
  exact Submodule.neg_mem _ (hf d x hx)

/-- A difference of multilinear maps of the same degree has that degree. -/
theorem IsHomogeneousOfDegree.sub {f g : MultilinearMap R M N}
    {𝒜 : (i : κ) → ι → Submodule R (M i)} {ℬ : ι → Submodule R N} {q : ι}
    (hf : IsHomogeneousOfDegree f 𝒜 ℬ q) (hg : IsHomogeneousOfDegree g 𝒜 ℬ q) :
    IsHomogeneousOfDegree (f - g) 𝒜 ℬ q := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end Ring

end MultilinearMap

end TauCeti
