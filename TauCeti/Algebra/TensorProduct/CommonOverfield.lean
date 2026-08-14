/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: consumers combine the common-overfield construction with the generic base-change
-- equivalence and injectivity lemma.
public import TauCeti.Algebra.TensorProduct.BaseChange
-- Non-public: these imports supply the residue-field construction and tensor-product
-- nontriviality used only in the definition body below.
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# A common overfield of two field extensions

Two extensions `K / k` and `L / k` embed into a common overfield: take a residue field of a
maximal ideal of `K ⊗[k] L`. This file records that field-theoretic construction; consumers use
the generic tensor-product base-change API to compare scalar extensions and obtain the injective
map induced by the embedding of `L`.

## Main declarations

* `TauCeti.Field.commonOverfield`: constructs a common overfield of two field extensions.

This is base-change descent infrastructure for geometric connectedness and reducedness in the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Field

universe u v w

/-- A common overfield of two extensions `K / k` and `L / k`.

The `K`-algebra structure on `Ω` is compatible with its `k`-algebra structure, while
`includeRight` embeds `L` into `Ω` as a `k`-algebra. -/
structure CommonOverfield (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] where
  /-- The common overfield. -/
  Ω : Type (max v w)
  /-- The field structure on the common overfield. -/
  [fieldΩ : Field Ω]
  /-- The common overfield as a `k`-algebra. -/
  [algebraBase : Algebra k Ω]
  /-- The common overfield as a `K`-algebra. -/
  [algebraLeft : Algebra K Ω]
  /-- Compatibility of the `k`- and `K`-algebra structures on the common overfield. -/
  [isScalarTower : IsScalarTower k K Ω]
  /-- The embedding of the second field extension into the common overfield. -/
  includeRight : L →ₐ[k] Ω

attribute [instance] CommonOverfield.fieldΩ CommonOverfield.algebraBase
  CommonOverfield.algebraLeft CommonOverfield.isScalarTower

/-- Construct a common overfield of two extensions of a field. -/
noncomputable def commonOverfield (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] :
    CommonOverfield k K L := by
  let R := K ⊗[k] L
  letI : Nontrivial R :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K L
      (algebraMap k K).injective (algebraMap k L).injective
  let P := Classical.choose (Ideal.exists_maximal R)
  have hP : P.IsMaximal := Classical.choose_spec (Ideal.exists_maximal R)
  letI : P.IsMaximal := hP
  let Ω := P.ResidueField
  let iK : K →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeLeft
  let iL : L →ₐ[k] Ω := (IsScalarTower.toAlgHom k R Ω).comp Algebra.TensorProduct.includeRight
  letI : Algebra K Ω := iK.toRingHom.toAlgebra
  letI : IsScalarTower k K Ω := IsScalarTower.of_algHom iK
  exact
    { Ω := Ω
      fieldΩ := inferInstance
      algebraBase := inferInstance
      algebraLeft := inferInstance
      isScalarTower := inferInstance
      includeRight := iL }

end Field

end TauCeti
