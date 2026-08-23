/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the common-overfield comparison exposes the coordinate-ring-order tower equivalence.
public import TauCeti.Algebra.TensorProduct.BaseChange
-- Non-public: these imports supply the residue-field construction, tensor-product
-- nontriviality, and flatness proof used only in definition bodies and proofs below.
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# A common overfield of two field extensions

Two extensions `K / k` and `L / k` embed into a common overfield: take a residue field of a
maximal ideal of `K ⊗[k] L`. This file records that construction together with the comparison
between successive and direct scalar extension, and the injective map induced by either field
embedding.

## Main declarations

* `TauCeti.Algebra.TensorProduct.commonOverfield`: constructs a common overfield of two field
  extensions.
* `TauCeti.Algebra.TensorProduct.CommonOverfield.comparison`: compares scalar extension through
  the first field with direct scalar extension to the common overfield.
* `TauCeti.Algebra.TensorProduct.CommonOverfield.map`: extends scalars along the embedding of the
  second field.

This is base-change descent infrastructure for geometric connectedness and reducedness in the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u v w x

/-- A common overfield of two extensions `K / k` and `L / k`.

The `K`-algebra structure on `Ω` is compatible with its `k`-algebra structure, while `right`
embeds `L` into `Ω` as a `k`-algebra. -/
structure CommonOverfield (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] where
  /-- The common overfield. -/
  Ω : Type (max v w)
  /-- The field structure on the common overfield. -/
  [fieldΩ : Field Ω]
  /-- The common overfield as a `k`-algebra. -/
  [algebraOmega : Algebra k Ω]
  /-- The common overfield as a `K`-algebra. -/
  [algebraKΩ : Algebra K Ω]
  /-- Compatibility of the `k`- and `K`-algebra structures on the common overfield. -/
  [isScalarTower : IsScalarTower k K Ω]
  /-- The embedding of the second field extension into the common overfield. -/
  right : L →ₐ[k] Ω

attribute [instance] CommonOverfield.fieldΩ CommonOverfield.algebraOmega
  CommonOverfield.algebraKΩ CommonOverfield.isScalarTower

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
      algebraOmega := inferInstance
      algebraKΩ := inferInstance
      isScalarTower := inferInstance
      right := iL }

namespace CommonOverfield

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

/-- Successive scalar extension through `K` agrees with direct scalar extension to a common
overfield. -/
noncomputable def comparison (d : CommonOverfield k K L) (A : Type x)
    [CommSemiring A] [Algebra k A] :
    ((K ⊗[k] A) ⊗[K] d.Ω) ≃+* (A ⊗[k] d.Ω) :=
  baseChangeTowerRingEquiv k K A d.Ω

/-- The common-overfield comparison sends nested pure tensors to pure tensors. -/
@[simp]
theorem comparison_tmul_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommSemiring A] [Algebra k A] (x : K) (a : A) (ω : d.Ω) :
    d.comparison A ((x ⊗ₜ[k] a) ⊗ₜ[K] ω) = a ⊗ₜ[k] (x • ω) :=
  baseChangeTowerRingEquiv_tmul_tmul k K A d.Ω x a ω

/-- The inverse common-overfield comparison sends pure tensors to nested pure tensors. -/
@[simp]
theorem comparison_symm_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommSemiring A] [Algebra k A] (a : A) (ω : d.Ω) :
    (d.comparison A).symm (a ⊗ₜ[k] ω) = (1 ⊗ₜ[k] a) ⊗ₜ[K] ω :=
  baseChangeTowerRingEquiv_symm_tmul k K A d.Ω a ω

/-- Scalar extension along the embedding of `L` into a common overfield. -/
noncomputable def map (d : CommonOverfield k K L) (A : Type x)
    [CommSemiring A] [Algebra k A] :
    A ⊗[k] L →ₐ[k] A ⊗[k] d.Ω :=
  Algebra.TensorProduct.map (AlgHom.id k A) d.right

/-- Scalar extension to a common overfield maps each pure tensor componentwise. -/
@[simp]
theorem map_tmul (d : CommonOverfield k K L) (A : Type x)
    [CommSemiring A] [Algebra k A] (a : A) (l : L) :
    d.map A (a ⊗ₜ[k] l) = a ⊗ₜ[k] d.right l := by
  simp [map]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
/-- Scalar extension from `L` to a common overfield is injective. -/
theorem map_injective (d : CommonOverfield k K L) (A : Type x)
    [CommRing A] [Algebra k A] : Function.Injective (d.map A) :=
  Module.Flat.lTensor_preserves_injective_linearMap d.right.toLinearMap
    (RingHom.injective d.right.toRingHom)

end CommonOverfield

end Algebra.TensorProduct

end TauCeti
