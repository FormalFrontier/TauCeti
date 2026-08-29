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

This file also owns the local model `𝒪_P ⊆ 𝒪'_P` that the later layers work with: on top of the
action of `𝒪_P` on `F'` supplied by
`TauCeti/FieldTheory/FunctionField/Place/Extension/Basic.lean` it records that `F'` is the
fraction field — indeed the localization at `(𝒪_P)⁰` — of `𝒪'_P`, that `𝒪'_P` is a Dedekind domain
and module-finite over `𝒪_P`, and it transports separability to the canonical fraction fields over
which Mathlib states the different.

The freeness and rank calculation are specializations of Mathlib's generic integral-closure
theorems `IsIntegralClosure.module_free` and `IsIntegralClosure.rank`.  The point of this file is
the function-field interface: the basis is indexed by `Fin [F' : F]`, its vectors are visibly
integral, and their `𝒪_P`-span inside `F'` is exactly `𝒪'_P`.  These are the forms used by the
complementary module and different of the next layer.

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
* `TauCeti.Place.isLocalization_integralClosure`: `F'` is the localization of `𝒪'_P` at the
  nonzero divisors of `𝒪_P`.
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

/-- An `F`-basis of `F'` is an integral basis at `P` exactly when its `𝒪_P`-span is the local
integral closure `𝒪'_P`. -/
theorem isIntegralBasis_iff {ι : Type*} (b : Basis ι F F') :
    P.IsIntegralBasis F' b ↔
      Submodule.span (P.integers) (Set.range b) =
        (integralClosure (P.integers) F').toSubmodule := Iff.rfl

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

/-! ### The local integral closure -/

variable [FiniteDimensional F F']

/-- The local model `𝒪'_P` — the integral closure of `𝒪_P` in `F'` — has fraction field `F'`. -/
instance isFractionRing_integralClosure :
    IsFractionRing (integralClosure (P.integers) F') F' :=
  IsIntegralClosure.isFractionRing_of_finite_extension (P.integers) F F' _

/-- More precisely, `F'` is the localization of the local model `𝒪'_P` at the nonzero divisors
of `𝒪_P`.  This is the form in which the `Basis.localizationLocalization` API consumes it. -/
theorem isLocalization_integralClosure :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F' :=
  IsIntegralClosure.isLocalization (P.integers) F F' _

attribute [local instance] isLocalization_integralClosure

/-- Extending any `𝒪_P`-basis of the local integral closure `𝒪'_P` to the fraction fields gives
an integral basis at `P`.  This is Stichtenoth, Corollary 3.3.5. -/
theorem isIntegralBasis_localizationLocalization {ι : Type*}
    (c : Basis ι (P.integers) (integralClosure (P.integers) F')) :
    P.IsIntegralBasis F' (c.localizationLocalization F (P.integers)⁰ F') := by
  rw [isIntegralBasis_iff, Basis.localizationLocalization_span F (P.integers)⁰ F']
  ext x
  simp

variable [Algebra.IsSeparable F F']

/-- The local model `𝒪'_P` is a Dedekind domain. -/
instance isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure (P.integers) F') :=
  integralClosure.isDedekindDomain (A := P.integers) (K := F) (L := F')

/-- The local model `𝒪'_P` is module-finite over `𝒪_P`. -/
instance moduleFinite_integralClosure :
    Module.Finite (P.integers) (integralClosure (P.integers) F') :=
  IsIntegralClosure.finite (A := P.integers) (K := F) (L := F') _

/-- Separability of `F' / F`, transported to the canonical fraction fields used by the
integral-closure API. -/
instance isSeparable_fractionRing_integralClosure :
    Algebra.IsSeparable (FractionRing (P.integers))
      (FractionRing (integralClosure (P.integers) F')) := by
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (P.integers) F).symm.toRingEquiv
    (FractionRing.algEquiv (integralClosure (P.integers) F') F').symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext (P.integers)⁰
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply (P.integers) (integralClosure (P.integers) F') F',
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

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
theorem isIntegral_iff_repr_mem {x : F'} :
    IsIntegral (P.integers) x ↔
      ∀ i, (localIntegralBasis F' P).repr x i ∈ P.integers := by
  rw [← (isIntegralBasis_localIntegralBasis F' P).mem_span_iff_isIntegral,
    Basis.mem_span_iff_repr_mem (P.integers) (localIntegralBasis F' P) x]
  exact forall_congr' fun _ ↦
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.2, fun hy ↦ ⟨⟨_, hy⟩, rfl⟩⟩

end Place

end TauCeti

end
