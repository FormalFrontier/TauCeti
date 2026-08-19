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
* `TauCeti.Subcomodule.corestrictSymm`: recover a subcomodule before corestriction along a
  coalgebra equivalence.
* `TauCeti.Subcomodule.corestrictOrderIso`: the carrier-preserving order isomorphism induced
  by a coalgebra equivalence.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
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
def corestrict (f : C →ₗc[R] D) (W : Subcomodule R C M) :
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
  (rfl)

/-- Membership is unchanged by corestriction of a subcomodule. -/
@[simp]
theorem mem_corestrict (f : C →ₗc[R] D) (W : Subcomodule R C M) (m : M) :
    letI : Comodule R D M := Comodule.Corestrict f
    m ∈ W.corestrict f ↔ m ∈ W :=
  Iff.rfl

private theorem corestrict_symm_instance_eq (e : C ≃ₗc[R] D) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    Comodule.Corestrict e.symm.toCoalgHom = (inferInstance : Comodule R C M) := by
  let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  apply Comodule.ext
  -- `Comodule.ext` presents the goal through the inferred instance projection. Unfolding that
  -- projection is necessary to expose the named corestriction coaction lemmas used below.
  change Comodule.corestrictCoact e.symm.toCoalgHom = Comodule.coact
  rw [← Comodule.corestrictCoact_comp e.toCoalgHom e.symm.toCoalgHom]
  have hcomp : e.symm.toCoalgHom.comp e.toCoalgHom = CoalgHom.id R C := by
    ext c
    simp
  rw [hcomp, Comodule.corestrictCoact_id]

/-- Pull a subcomodule of a corestricted comodule back along a coalgebra equivalence. -/
def corestrictSymm (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) : Subcomodule R C M :=
  let instOriginal : Comodule R C M := inferInstance
  letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  let instDouble : Comodule R C M := Comodule.Corestrict e.symm.toCoalgHom
  let W' : @Subcomodule R C M _ _ _ _ _ _ instDouble := by
    letI : Comodule R C M := instDouble
    exact W.corestrict e.symm.toCoalgHom
  have h : instDouble = instOriginal := by
    let _ : Comodule R C M := instOriginal
    exact corestrict_symm_instance_eq e
  letI : Comodule R C M := instOriginal
  Subcomodule.ofSubmodule W.carrier fun m hm => by
    have hmem : instDouble.coact m ∈ LinearMap.range
        (TensorProduct.map W.carrier.subtype (LinearMap.id : C →ₗ[R] C)) := by
      let _ : Comodule R C M := instDouble
      have hmem' := W'.coact_mem hm
      -- The source of `hmem'` contains `W'.carrier`, while the target contains `W.carrier`.
      -- These subcomodules have different dependent comodule-instance indices, so expose the
      -- carrier equality explicitly before rewriting it with the corestriction API.
      rw [show W'.carrier = W.carrier by
        exact corestrict_toSubmodule e.symm.toCoalgHom W] at hmem'
      exact hmem'
    rw [congrArg (fun rho : Comodule R C M => rho.coact) h] at hmem
    exact hmem

/-- Pulling a subcomodule back from a corestriction preserves its underlying submodule. -/
@[simp]
theorem corestrictSymm_toSubmodule (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    (corestrictSymm e W).toSubmodule = W.toSubmodule :=
  by
    ext m
    rfl

/-- Membership is unchanged when pulling a subcomodule back from a corestriction. -/
@[simp]
theorem mem_corestrictSymm (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) (m : M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    m ∈ corestrictSymm e W ↔ m ∈ W :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    -- Membership notation hides the underlying submodules behind subcomodules indexed by
    -- dependent comodule instances; expose those carriers so the preservation lemma can rewrite.
    change m ∈ (corestrictSymm e W).toSubmodule ↔ m ∈ W.toSubmodule
    rw [corestrictSymm_toSubmodule]

/-- A coalgebra equivalence identifies the subcomodules of a comodule with those of its
corestriction, without changing their underlying submodules. -/
def corestrictOrderIso (e : C ≃ₗc[R] D) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    Subcomodule R C M ≃o Subcomodule R D M :=
  letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
  { toFun := fun W ↦ W.corestrict e.toCoalgHom
    invFun := corestrictSymm e
    -- Both directions are built with `ofSubmodule W.carrier`, so carrier equality and order
    -- reflection hold definitionally.
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

/-- The forward order correspondence is corestriction. -/
@[simp]
theorem corestrictOrderIso_apply (e : C ≃ₗc[R] D) (W : Subcomodule R C M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    corestrictOrderIso e W = W.corestrict e.toCoalgHom :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    ext m
    rfl

/-- The inverse order correspondence is pullback from the corestriction. -/
@[simp]
theorem corestrictOrderIso_symm_apply (e : C ≃ₗc[R] D)
    (W : letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
      Subcomodule R D M) :
    letI : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    (corestrictOrderIso e).symm W = corestrictSymm e W :=
  by
    let _ : Comodule R D M := Comodule.Corestrict e.toCoalgHom
    ext m
    rfl

end Subcomodule

end TauCeti
