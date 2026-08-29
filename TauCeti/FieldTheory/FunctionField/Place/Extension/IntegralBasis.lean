/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension

/-!
# Local integral bases of extensions of algebraic function fields

Let `F' / F` be a finite separable extension and let `P` be a place of `F / k`.  Its local
integral closure

`𝒪'_P = integralClosure 𝒪_P F'`

is a finite free module over the discrete valuation ring `𝒪_P`, of rank `[F' : F]`.  Choosing a
basis of that module and extending scalars from `𝒪_P` to its fraction field `F` gives a basis of
`F' / F` consisting of elements integral over `𝒪_P`.  This is the local integral basis of
Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Corollary 3.3.5.

The freeness and rank calculation are specializations of Mathlib's generic integral-closure
theorems `IsIntegralClosure.module_free` and `IsIntegralClosure.rank`.  The point of this file is
the function-field interface: the basis is indexed by `Fin [F' : F]`, its vectors are visibly
integral, and their `𝒪_P`-span inside `F'` is exactly `𝒪'_P`.  These are the forms used by the
complementary module and different of the next layer.

## Main definitions

* `TauCeti.Place.IsIntegralBasis`: the property that an `F`-basis of `F'` is an integral basis
  at `P`.
* `TauCeti.Place.integralClosureFinBasis`: an `𝒪_P`-basis of `𝒪'_P`, indexed by
  `Fin [F' : F]`.
* `TauCeti.Place.localIntegralBasis`: the resulting `F`-basis of `F'`.

## Main results

* `TauCeti.Place.localIntegralBasis_isIntegral`: every basis vector is integral over `𝒪_P`.
* `TauCeti.Place.span_localIntegralBasis`: the `𝒪_P`-span of the basis vectors is exactly the
  integral closure `𝒪'_P` inside `F'`.
* `TauCeti.Place.mem_span_localIntegralBasis_iff`: an element of `F'` has integral coordinates
  in the local basis exactly when it is integral over `𝒪_P`.

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

/-! ### The local integral closure -/

variable (F') (P : Place k F)

/-- **The valuation ring of a place of `F / k` acts on an extension field `F'`**, through `F`.

This is not a global instance: for `F' = F` it would compete with the action of a valuation
subring on its own field. Install it, together with
`TauCeti.Place.isScalarTowerIntegersExtension`, with `attribute [local instance 10]` in any file
that works with the local model of the extension at `P`. -/
@[instance_reducible]
noncomputable def algebraIntegersExtension : Algebra (P.integers) F' :=
  ((algebraMap F F').comp (algebraMap (P.integers) F)).toAlgebra

attribute [local instance 10] algebraIntegersExtension

/-- The action of `TauCeti.Place.algebraIntegersExtension` on `F'` factors through `F`. -/
theorem isScalarTowerIntegersExtension : IsScalarTower (P.integers) F F' :=
  .of_algebraMap_eq fun _ ↦ rfl

attribute [local instance 10] isScalarTowerIntegersExtension

theorem algebraMap_integersExtension_injective :
    Function.Injective (algebraMap (P.integers) F') := by
  rw [IsScalarTower.algebraMap_eq (P.integers) F F', RingHom.coe_comp]
  exact (algebraMap F F').injective.comp (FaithfulSMul.algebraMap_injective (P.integers) F)

instance isTorsionFree_integersExtension : Module.IsTorsionFree (P.integers) F' :=
  Module.IsTorsionFree.comap (M := F') (algebraMap (P.integers) F')
    (fun _ hr ↦ isRegular_iff_ne_zero'.mpr fun h ↦ isRegular_iff_ne_zero'.mp hr
      (algebraMap_integersExtension_injective F' P (by simpa using h)))
    (fun r m ↦ (Algebra.smul_def r m).symm)

/-- An `F`-basis of `F'` is an **integral basis at `P`** when its `𝒪_P`-span is exactly the
integral closure `𝒪'_P` inside `F'` (Stichtenoth, Section III.3). -/
def IsIntegralBasis {ι : Type*} (b : Basis ι F F') : Prop :=
  Submodule.span (P.integers) (Set.range b) = (integralClosure (P.integers) F').toSubmodule

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

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- The local model `𝒪'_P` — the integral closure of `𝒪_P` in `F'` — has fraction field `F'`. -/
instance isFractionRing_integralClosure :
    IsFractionRing (integralClosure (P.integers) F') F' :=
  IsIntegralClosure.isFractionRing_of_finite_extension (P.integers) F F' _

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
noncomputable def localIntegralBasis : Basis (Fin (Module.finrank F F')) F F' := by
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F' :=
    IsIntegralClosure.isLocalization (P.integers) F F' (integralClosure (P.integers) F')
  exact (integralClosureFinBasis F' P).localizationLocalization F (P.integers)⁰ F'

/-- A vector of the local integral basis is the image in `F'` of the corresponding vector of
the `𝒪_P`-basis of `𝒪'_P`. -/
@[simp]
theorem localIntegralBasis_apply (i : Fin (Module.finrank F F')) :
    localIntegralBasis F' P i =
      algebraMap (integralClosure (P.integers) F') F' (integralClosureFinBasis F' P i) := by
  let _ : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F' :=
    IsIntegralClosure.isLocalization (P.integers) F F' (integralClosure (P.integers) F')
  exact Basis.localizationLocalization_apply F (P.integers)⁰ F'
    (integralClosureFinBasis F' P) i

/-- The coordinates of an integral element in the local integral basis are the images in `F` of
its coordinates in the `𝒪_P`-basis of `𝒪'_P`. -/
@[simp]
theorem localIntegralBasis_repr_coe (x : integralClosure (P.integers) F')
    (i : Fin (Module.finrank F F')) :
    (localIntegralBasis F' P).repr (x : F') i =
      algebraMap (P.integers) F ((integralClosureFinBasis F' P).repr x i) := by
  let _ : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F' :=
    IsIntegralClosure.isLocalization (P.integers) F F' (integralClosure (P.integers) F')
  rw [localIntegralBasis]
  simpa only [Subalgebra.algebraMap_apply] using
    Basis.localizationLocalization_repr_algebraMap F (P.integers)⁰ F'
      (integralClosureFinBasis F' P) x i

/-- **The integral span of a local integral basis is the local integral closure `𝒪'_P`.** -/
theorem span_localIntegralBasis :
    Submodule.span (P.integers) (Set.range (localIntegralBasis F' P)) =
      (integralClosure (P.integers) F').toSubmodule := by
  let _ : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure (P.integers) F') (P.integers)⁰) F' :=
    IsIntegralClosure.isLocalization (P.integers) F F' (integralClosure (P.integers) F')
  rw [localIntegralBasis]
  rw [Basis.localizationLocalization_span F (P.integers)⁰ F']
  ext x
  simp

/-- The chosen `localIntegralBasis` is an integral basis at `P`. This is the existence statement
of Stichtenoth, Corollary 3.3.5. -/
theorem isIntegralBasis_localIntegralBasis :
    P.IsIntegralBasis F' (localIntegralBasis F' P) :=
  span_localIntegralBasis F' P

/-- Every vector of the chosen local integral basis is integral over `𝒪_P`. -/
theorem localIntegralBasis_isIntegral (i : Fin (Module.finrank F F')) :
    IsIntegral (P.integers) (localIntegralBasis F' P i) :=
  IsIntegralBasis.isIntegral (F' := F') (P := P) (isIntegralBasis_localIntegralBasis F' P) i

/-- An element of `F'` has integral coordinates in the local integral basis exactly when it is
integral over `𝒪_P`. -/
theorem mem_span_localIntegralBasis_iff {x : F'} :
    x ∈ Submodule.span (P.integers) (Set.range (localIntegralBasis F' P)) ↔
      IsIntegral (P.integers) x := by
  exact (isIntegralBasis_localIntegralBasis F' P).mem_span_iff_isIntegral

end Place

end TauCeti

end
