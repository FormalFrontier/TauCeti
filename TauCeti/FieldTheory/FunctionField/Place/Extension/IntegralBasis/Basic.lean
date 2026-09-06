/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Local integral bases of extensions of algebraic function fields

Let `F' / F` be a finite separable extension and let `P` be a place of `F / k`.  Its local
integral closure

`𝒪'_P = integralClosure 𝒪_P F'`

is a finite free module over the discrete valuation ring `𝒪_P`, of rank `[F' : F]`.  Choosing a
basis of that module and extending scalars from `𝒪_P` to its fraction field `F` gives a basis of
`F' / F` consisting of elements integral over `𝒪_P`.  This is the local integral basis of
Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Corollary 3.3.5.

The local model `𝒪_P ⊆ 𝒪'_P` and its fraction-field, localization, Dedekind, finiteness, and
separability infrastructure are supplied by
`TauCeti/FieldTheory/FunctionField/Place/Extension/Basic.lean`.

The freeness and rank calculation are specializations of Mathlib's generic integral-closure
theorems `IsIntegralClosure.module_free` and `IsIntegralClosure.rank`.  The point of this file is
the function-field interface: the basis is indexed by `Fin [F' : F]`, its vectors are visibly
integral, and their `𝒪_P`-span inside `F'` is exactly `𝒪'_P`.  These are the forms used by the
subsequent constructions of the complementary module and different.

The basis material is the place-local analogue of Mathlib's `NumberField.integralBasis` API in
`Mathlib.NumberTheory.NumberField.Basic`, and is built the same way:
`TauCeti.Place.finrank_integralClosure` matches `NumberField.RingOfIntegers.rank`,
`TauCeti.Place.localIntegralBasis` matches `NumberField.integralBasis`,
`TauCeti.Place.localIntegralBasis_apply` and
`TauCeti.Place.localIntegralBasis_repr_algebraMap` match `NumberField.integralBasis_apply` and
`NumberField.integralBasis_repr_apply`, and
`TauCeti.Place.isIntegralBasis_localizationLocalization` plays the role of
`NumberField.mem_span_integralBasis`.

## Main definitions

* `TauCeti.Place.IsIntegralBasis`: the property that an `F`-basis of `F'` is an integral basis
  at `P`.
* `TauCeti.Place.integralClosureFinBasis`: an `𝒪_P`-basis of `𝒪'_P`, indexed by
  `Fin [F' : F]`.
* `TauCeti.Place.localIntegralBasis`: the resulting `F`-basis of `F'`.

## Main results

* `TauCeti.Place.IsIntegralBasis.isIntegral` and
  `TauCeti.Place.IsIntegralBasis.mem_span_iff_isIntegral`: what an integral basis at `P` gives —
  integral vectors, and an integral span that detects integrality.
* `TauCeti.Place.isIntegralBasis_iff_isIntegral_iff_repr_mem`: an arbitrary basis is integral
  exactly when integrality is detected coordinatewise over `𝒪_P`.
* `TauCeti.Place.IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual`: a basis and its trace
  dual being integral at a place is sufficient for the basis to be an integral basis there.
* `TauCeti.Place.finrank_integralClosure`: `rank_{𝒪_P} 𝒪'_P = [F' : F]`.
* `TauCeti.Place.isIntegralBasis_localizationLocalization`: extending any `𝒪_P`-basis of `𝒪'_P`
  to the fraction fields gives an integral basis at `P`.
* `TauCeti.Place.isIntegralBasis_localIntegralBasis`: the chosen basis
  `TauCeti.Place.localIntegralBasis` is one; this is the existence statement of Stichtenoth,
  Corollary 3.3.5.
* `TauCeti.Place.localIntegralBasis_repr_algebraMap`: the coordinates of an integral element in
  the local integral basis are the images of its coordinates in the `𝒪_P`-basis of `𝒪'_P`.
* `TauCeti.Place.isIntegral_iff_repr_mem`: an element of `F'` is integral over `𝒪_P` exactly when
  all its coordinates in the local integral basis lie in `𝒪_P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.3.5.
-/

public section

open IsDedekindDomain
open Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-! ### Integral bases at a place -/

variable (F') (P : Place k F)

/-- An `F`-basis of `F'` is an **integral basis at `P`** when its `𝒪_P`-span is exactly the
integral closure `𝒪'_P` inside `F'` (Stichtenoth, Section III.3). -/
def IsIntegralBasis {ι : Type*} (b : Basis ι F F') : Prop :=
  Submodule.span (P.integers) (Set.range b) = (integralClosure (P.integers) F').toSubmodule

/-- A basis is an integral basis at `P` exactly when integrality over `𝒪_P` is equivalent to all
of its coordinates lying in `𝒪_P`. -/
theorem isIntegralBasis_iff_isIntegral_iff_repr_mem {ι : Type*} (b : Basis ι F F') :
    P.IsIntegralBasis F' b ↔
      ∀ x, IsIntegral (P.integers) x ↔ ∀ i, b.repr x i ∈ P.integers := by
  rw [IsIntegralBasis, Submodule.ext_iff]
  apply forall_congr'
  intro x
  rw [Basis.mem_span_iff_repr_mem, Subalgebra.mem_toSubmodule,
    mem_integralClosure_iff]
  have hmem (y : F) :
      y ∈ Set.range (algebraMap (P.integers) F) ↔ y ∈ P.integers :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.2, fun hy ↦ ⟨⟨y, hy⟩, rfl⟩⟩
  simp only [hmem, iff_comm]

/-- Every vector of an integral basis at `P` is integral over `𝒪_P`. -/
theorem IsIntegralBasis.isIntegral {ι : Type*} {b : Basis ι F F'} (hb : P.IsIntegralBasis F' b)
    (i : ι) : IsIntegral (P.integers) (b i) := by
  rw [← mem_integralClosure_iff, ← Subalgebra.mem_toSubmodule, ← hb]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- Membership in the integral span of an integral basis at `P` is the same as integrality over
`𝒪_P`. -/
theorem IsIntegralBasis.mem_span_iff_isIntegral {ι : Type*} {b : Basis ι F F'}
    (hb : P.IsIntegralBasis F' b) {x : F'} :
    x ∈ Submodule.span (P.integers) (Set.range b) ↔ IsIntegral (P.integers) x := by
  rw [hb, Subalgebra.mem_toSubmodule]
  exact mem_integralClosure_iff (P.integers) F'

/-- Integrality over `𝒪_P`, expressed in the coordinate normal form supplied by an integral
basis at `P`. -/
theorem IsIntegralBasis.isIntegral_iff_repr_mem {ι : Type*} {b : Basis ι F F'}
    (hb : P.IsIntegralBasis F' b) {x : F'} :
    IsIntegral (P.integers) x ↔ ∀ i, b.repr x i ∈ P.integers :=
  (isIntegralBasis_iff_isIntegral_iff_repr_mem F' P b).mp hb x

/-- If an `F`-basis of `F'` and its trace-dual basis are integral over `𝒪_P`, then the basis is
an integral basis at `P`. -/
theorem IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual {ι : Type*} [Finite ι]
    [DecidableEq ι] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P : Place k F)
    (b : Basis ι F F')
    (hb : ∀ i, IsIntegral P.integers (b i))
    (hbdual : ∀ i, IsIntegral P.integers (b.traceDual i)) :
    P.IsIntegralBasis F' b := by
  rw [IsIntegralBasis]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_integralClosure_iff (P.integers) F').mpr (hb i)
  · simpa only [← Basis.traceDual_def, Basis.traceDual_traceDual] using
      (integralClosure_le_span_dualBasis (A := P.integers) b.traceDual hbdual)

/-! ### The local integral closure -/

section Localization

variable [IsLocalization
  (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F']

/-- Extending any `𝒪_P`-basis of the local integral closure `𝒪'_P` to the fraction fields gives
an integral basis at `P`.  This is Stichtenoth, Corollary 3.3.5. -/
theorem isIntegralBasis_localizationLocalization {ι : Type*}
    (c : Basis ι (P.integers) (integralClosure (P.integers) F')) :
    P.IsIntegralBasis F' (c.localizationLocalization F (P.integers)⁰ F') := by
  rw [IsIntegralBasis, Basis.localizationLocalization_span F (P.integers)⁰ F']
  ext x
  simp

end Localization

variable [FiniteDimensional F F']

attribute [local instance] isLocalization_integralClosure

variable [Algebra.IsSeparable F F']

/-- The rank of the local integral closure is the degree of the field extension:
`rank_{𝒪_P} 𝒪'_P = [F' : F]`. -/
theorem finrank_integralClosure :
    Module.finrank (P.integers) (integralClosure (P.integers) F') = Module.finrank F F' :=
  IsIntegralClosure.rank (P.integers) F F' _

/-! ### A local integral basis -/

/-- An `𝒪_P`-basis of the local integral closure `𝒪'_P`, indexed by the degree `[F' : F]`. -/
noncomputable def integralClosureFinBasis :
    Basis (Fin (Module.finrank F F')) (P.integers) (integralClosure (P.integers) F') :=
  Module.finBasisOfFinrankEq (P.integers) (integralClosure (P.integers) F')
    (finrank_integralClosure F' P)

/-- **A local integral basis at `P`** (Stichtenoth, Corollary 3.3.5): extend an `𝒪_P`-basis of
the local integral closure `𝒪'_P` to the fraction fields. The resulting `F`-basis of `F'` is
indexed by `Fin [F' : F]`, and its `𝒪_P`-span is exactly `𝒪'_P`. -/
noncomputable def localIntegralBasis : Basis (Fin (Module.finrank F F')) F F' :=
  (integralClosureFinBasis F' P).localizationLocalization F (P.integers)⁰ F'

/-- A vector of the local integral basis is the image in `F'` of the corresponding vector of
the `𝒪_P`-basis of `𝒪'_P`. -/
@[simp]
theorem localIntegralBasis_apply (i : Fin (Module.finrank F F')) :
    localIntegralBasis F' P i =
      algebraMap (integralClosure (P.integers) F') F' (integralClosureFinBasis F' P i) :=
  Basis.localizationLocalization_apply F (P.integers)⁰ F' (integralClosureFinBasis F' P) i

/-- The coordinates of an integral element in the local integral basis are the images in `F` of
its coordinates in the `𝒪_P`-basis of `𝒪'_P`. -/
@[simp]
theorem localIntegralBasis_repr_algebraMap (x : integralClosure (P.integers) F')
    (i : Fin (Module.finrank F F')) :
    (localIntegralBasis F' P).repr (x : F') i =
      algebraMap (P.integers) F ((integralClosureFinBasis F' P).repr x i) := by
  simpa only [localIntegralBasis, Subalgebra.algebraMap_apply] using
    Basis.localizationLocalization_repr_algebraMap F (P.integers)⁰ F'
      (integralClosureFinBasis F' P) x i

/-- **The chosen `localIntegralBasis` is an integral basis at `P`**: its `𝒪_P`-span is exactly
the local integral closure `𝒪'_P`.  This is the existence statement of Stichtenoth,
Corollary 3.3.5. -/
theorem isIntegralBasis_localIntegralBasis :
    P.IsIntegralBasis F' (localIntegralBasis F' P) :=
  isIntegralBasis_localizationLocalization F' P (integralClosureFinBasis F' P)

/-- **An element of `F'` is integral over `𝒪_P` exactly when all of its coordinates in the local
integral basis lie in `𝒪_P`** (Stichtenoth, Corollary 3.3.5). -/
@[simp]
theorem isIntegral_iff_repr_mem {x : F'} :
    IsIntegral (P.integers) x ↔
      ∀ i, (localIntegralBasis F' P).repr x i ∈ P.integers := by
  exact (isIntegralBasis_localIntegralBasis F' P).isIntegral_iff_repr_mem

end Place

end TauCeti

end
