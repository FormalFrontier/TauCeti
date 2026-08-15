/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Lattices and base change

This file develops properties of full lattice submodules over a principal ideal domain. In
particular, the inclusion of a full lattice submodule `S ≤ V` into an ambient vector space `V`
over the fraction field `K` exhibits `V` as the base change `K ⊗[R] S`.

## Main declarations

* `TauCeti.Submodule.IsLattice.isBaseChange_subtype`: the inclusion of a full lattice submodule
  over a principal ideal domain into its ambient vector space over the fraction field is a base
  change.

## References

* See N. Bourbaki, *Commutative Algebra*, Chapter VII, §4 for lattice theory over Dedekind domains.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u v w

namespace Submodule

namespace IsLattice

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The inclusion of a full lattice submodule over a principal ideal domain into its ambient vector
space over the fraction field exhibits that space as base change from `R` to `K`. -/
theorem isBaseChange_subtype (S : Submodule R V) [S.IsLattice K] :
    IsBaseChange K S.subtype := by
  have : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (IsFractionRing.injective R K)
  let b := Module.Free.chooseBasis R S
  let e : K ⊗[R] S ≃ₗ[K] V :=
    (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
  have hmap : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R K S 1) =
      S.subtype := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [← Module.Basis.baseChange_apply K b i, Basis.equiv_apply,
      Basis.extendOfIsLattice_apply, Equiv.refl_apply]
  exact IsBaseChange.of_equiv e fun x ↦ DFunLike.congr_fun hmap x

end IsLattice

end Submodule

end TauCeti
