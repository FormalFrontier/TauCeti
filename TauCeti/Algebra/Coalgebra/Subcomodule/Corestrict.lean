/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Corestriction of subcomodules

Corestriction of a comodule along a coalgebra morphism preserves every subcomodule and its
underlying submodule. When the coalgebra morphism is an equivalence, this gives an order
isomorphism between the subcomodule lattices before and after corestriction.

This is Layer 1 infrastructure for the reductive-groups roadmap: changing coordinate
coalgebras must preserve the invariant subspaces of their comodules.

## Main declarations

* `TauCeti.Subcomodule.corestrict`: corestrict a subcomodule along a coalgebra morphism.
* `TauCeti.Subcomodule.corestrictOrderIso`: the carrier-preserving order isomorphism induced
  by a coalgebra equivalence.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Subcomodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Corestriction along a coalgebra morphism preserves a subcomodule and its carrier. -/
@[expose] def corestrict (f : C →ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict f
    Subcomodule R D M :=
  letI : Comodule R D M := Comodule.Corestrict f
  Subcomodule.ofSubmodule W.carrier fun m hm ↦ by
    obtain ⟨t, ht⟩ := W.coact_mem hm
    refine ⟨TensorProduct.map LinearMap.id f.toLinearMap t, ?_⟩
    rw [Comodule.corestrict_coact_apply]
    calc
      _ = TensorProduct.map LinearMap.id f.toLinearMap
          (TensorProduct.map W.carrier.subtype LinearMap.id t) := by
            simp [TensorProduct.map_map]
      _ = _ := congrArg (TensorProduct.map LinearMap.id f.toLinearMap) ht

/-- Corestriction of a subcomodule does not change its underlying submodule. -/
@[simp]
theorem corestrict_toSubmodule (f : C →ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict f
    (W.corestrict f).toSubmodule = W.toSubmodule :=
  rfl

/-- A coalgebra equivalence identifies the subcomodules of a comodule with those of its
corestriction, without changing their underlying submodules. -/
@[expose] def corestrictOrderIso (e : C ≃ₗc[R] D) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    Subcomodule R C M ≃o Subcomodule R D M :=
  letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  { toFun := fun W ↦ W.corestrict e.toCoalgHom
    invFun := fun W ↦
      Subcomodule.ofSubmodule W.carrier fun m hm ↦ by
        obtain ⟨t, ht⟩ := W.coact_mem hm
        rw [Comodule.corestrict_coact_apply] at ht
        refine ⟨TensorProduct.map LinearMap.id e.symm.toLinearMap t, ?_⟩
        calc
          _ = TensorProduct.map LinearMap.id e.symm.toLinearMap
              (TensorProduct.map W.carrier.subtype LinearMap.id t) := by
                simp [TensorProduct.map_map]
          _ = TensorProduct.map LinearMap.id e.symm.toLinearMap
              (TensorProduct.map LinearMap.id e.toLinearMap
                (Comodule.coact (R := R) (C := C) (M := M) m)) :=
            congrArg (TensorProduct.map LinearMap.id e.symm.toLinearMap) ht
          _ = _ := by
            rw [TensorProduct.map_map]
            rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by
              ext c
              simp]
            simp
    left_inv := by
      intro W
      ext m
      rfl
    right_inv := by
      intro W
      ext m
      rfl
    map_rel_iff' := by
      rfl }

/-- The forward subcomodule correspondence preserves the underlying submodule. -/
@[simp]
theorem corestrictOrderIso_apply_toSubmodule (e : C ≃ₗc[R] D)
    (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    (corestrictOrderIso e W).toSubmodule = W.toSubmodule :=
  rfl

/-- The inverse subcomodule correspondence preserves the underlying submodule. -/
@[simp]
theorem corestrictOrderIso_symm_apply_toSubmodule (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    ((corestrictOrderIso e).symm W).toSubmodule = W.toSubmodule :=
  rfl

end Subcomodule

end TauCeti
