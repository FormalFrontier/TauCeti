/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.Regular
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Multiplication of regular subcomodules

For a bialgebra `H`, multiplication is a morphism from the tensor square of the regular
right comodule to the regular right comodule. Consequently, if `N` and `P` are
subcomodules of the regular comodule and a third subcomodule `Q` contains all products
`n * p`, multiplication corestricts to a comodule morphism `N ⊗ P ⟶ Q`.

When `H` is free over the base semiring and `N` and `P` are finite submodules, the products
of their elements lie in some finite regular subcomodule. This packages the multiplication
map needed to compare tensor-compatible natural transformations on finite regular
subcomodules.

## Main declarations

* `TauCeti.Subcomodule.mulHom`: multiplication corestricted to a containing regular
  subcomodule.
* `TauCeti.Subcomodule.exists_finite_mul_le_of_exists_mem`: pairwise products lie in a
  finite regular subcomodule whenever every element does.
* `TauCeti.Subcomodule.exists_finite_mul_le`: two finite submodules have all
  their pairwise products in a third finite regular subcomodule.

## References

The regular-comodule multiplication is the coalgebra-homomorphism part of the bialgebra
axioms; see Sweedler, *Hopf Algebras*, Chapter 2. The finite containment argument uses the
finite-subcomodule theorem from the same chapter.

This advances the Layer 1 Tannakian reconstruction milestone of the reductive-groups
roadmap, `ReductiveGroups/README.md` in TauCetiRoadmap: tensor naturality applied to these
multiplication morphisms supplies the multiplicativity law for the reconstructed point.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

namespace Subcomodule

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]

attribute [local instance] Comodule.tensor

/-- Multiplication from `N ⊗ P`, corestricted to a regular subcomodule `Q` containing
every product `n * p`. -/
noncomputable def mulHom (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) :
    Comodule.Hom R H (N ⊗[R] P) Q :=
  let ambient : Comodule.Hom R H (N ⊗[R] P) H :=
    Comodule.Hom.comp (Comodule.Hom.regularMul (R := R) (H := H))
      (Comodule.Hom.tensorMap (Subcomodule.subtype N) (Subcomodule.subtype P))
  have hmem : ∀ x, ambient x ∈ Q := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [← Comodule.Hom.coe_toLinearMap ambient, map_zero]
      exact Q.toSubmodule.zero_mem
    | add x y hx hy =>
      rw [← Comodule.Hom.coe_toLinearMap ambient, map_add]
      exact Q.toSubmodule.add_mem hx hy
    | tmul n p =>
      simpa only [ambient, Comodule.Hom.comp_apply, Comodule.Hom.tensorMap_tmul,
        Subcomodule.subtype_apply, Comodule.Hom.regularMul_tmul] using h n p
  Comodule.Hom.codRestrict ambient Q hmem

private theorem mulHom_tmul_def (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) (n : N) (p : P) :
    ((mulHom N P Q h) (n ⊗ₜ[R] p) : H) = (n : H) * (p : H) := by
  simp only [mulHom, Comodule.Hom.codRestrict_apply, Comodule.Hom.comp_apply,
    Comodule.Hom.tensorMap_tmul, Subcomodule.subtype_apply, Comodule.Hom.regularMul_tmul]

/-- Corestricted regular multiplication sends a pure tensor to the product of its
factors. -/
@[simp]
theorem mulHom_tmul (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) (n : N) (p : P) :
    ((mulHom N P Q h) (n ⊗ₜ[R] p) : H) = (n : H) * (p : H) := by
  exact mulHom_tmul_def N P Q h n p

/-- The underlying linear map of corestricted regular multiplication is Mathlib's
`Submodule.mulMap`, with codomain restricted to `Q`. -/
@[simp]
theorem mulHom_toLinearMap (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) :
    (mulHom N P Q h).toLinearMap =
      (Submodule.mulMap N.toSubmodule P.toSubmodule).codRestrict Q.toSubmodule (by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => exact Q.toSubmodule.zero_mem
        | add x y hx hy =>
          rw [map_add]
          exact Q.toSubmodule.add_mem hx hy
        | tmul n p => exact h n p) := by
  apply TensorProduct.ext'
  intro n p
  exact Subtype.ext (mulHom_tmul N P Q h n p)

/-- If every element of `H` belongs to a finite regular subcomodule, then pairwise products
from two finite submodules lie in a finite regular subcomodule. -/
theorem exists_finite_mul_le_of_exists_mem
    (hH : ∀ h : H, ∃ Q : Subcomodule R H H, Module.Finite R Q.toSubmodule ∧ h ∈ Q)
    (N P : Submodule R H)
    [Module.Finite R N] [Module.Finite R P] :
    ∃ Q : Subcomodule R H H, Module.Finite R Q.toSubmodule ∧
      ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q := by
  let f := Submodule.mulMap N P
  obtain ⟨Q, hQfinite, hQ⟩ :=
    exists_finite_subcomodule_of_fg_of_exists_mem hH
      f.range (Submodule.fg_range f)
  refine ⟨Q, hQfinite, fun n p ↦ hQ ?_⟩
  exact ⟨n ⊗ₜ[R] p, rfl⟩

/-- If `H` is free over `R`, pairwise products from two finite submodules lie in a finite
regular subcomodule. -/
theorem exists_finite_mul_le [Module.Free R H] (N P : Submodule R H)
    [Module.Finite R N] [Module.Finite R P] :
    ∃ Q : Subcomodule R H H, Module.Finite R Q.toSubmodule ∧
      ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q :=
  exists_finite_mul_le_of_exists_mem
    (exists_finite_subcomodule_mem (R := R) (C := H) (M := H)) N P

end Subcomodule

end TauCeti
