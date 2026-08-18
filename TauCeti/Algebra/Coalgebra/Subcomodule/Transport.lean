/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Transport of subcomodules

Mutually inverse comodule morphisms identify the corresponding subcomodule lattices by taking
images. In particular, transporting a comodule structure along a linear equivalence preserves
its subcomodules and their underlying submodules.

This is Layer 1 infrastructure for the reductive-groups roadmap: changing the carrier of a
comodule must preserve its invariant subspaces.

## Main declarations

* `TauCeti.Subcomodule.mapOrderIso`: the order isomorphism induced by mutually inverse comodule
  morphisms.
* `TauCeti.Subcomodule.transportOrderIso`: the carrier-compatible order isomorphism induced by
  transport along a linear equivalence.
-/

public section

namespace TauCeti

universe u v w x

namespace Subcomodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N]

/-- Mutually inverse comodule morphisms identify the lattices of subcomodules by taking images. -/
@[expose] def mapOrderIso [Comodule R C N]
    (f : Comodule.Hom R C M N) (g : Comodule.Hom R C N M)
    (hgf : g.comp f = Comodule.Hom.id R C M)
    (hfg : f.comp g = Comodule.Hom.id R C N) :
    Subcomodule R C M ≃o Subcomodule R C N where
  toFun A := A.map f
  invFun A := A.map g
  left_inv A := by
    change (A.map f).map g = A
    rw [map_map, hgf, map_id]
  right_inv A := by
    change (A.map g).map f = A
    rw [map_map, hfg, map_id]
  map_rel_iff' := by
    intro A B
    constructor
    · intro h
      change A.map f ≤ B.map f at h
      have hg := map_mono g h
      change (A.map f).map g ≤ (B.map f).map g at hg
      rwa [map_map, hgf, map_id, map_map, hgf, map_id] at hg
    · intro h
      change A.map f ≤ B.map f
      exact map_mono f h

/-- Transporting a comodule along a linear equivalence identifies its subcomodule lattice with
the original one. -/
@[expose] def transportOrderIso (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Comodule.Transport e
    Subcomodule R C M ≃o Subcomodule R C N := by
  letI : Comodule R C N := Comodule.Transport e
  exact mapOrderIso (Comodule.transportToHom e) (Comodule.transportInvHom e)
    (Comodule.Hom.ext fun m => e.symm_apply_apply m)
    (Comodule.Hom.ext fun n => e.apply_symm_apply n)

/-- The forward transport correspondence is image under the transport equivalence. -/
@[simp]
theorem transportOrderIso_apply (e : M ≃ₗ[R] N) (A : Subcomodule R C M) :
    letI : Comodule R C N := Comodule.Transport e
    transportOrderIso e A = A.map (Comodule.transportToHom e) :=
  rfl

/-- The inverse transport correspondence is image under the inverse transport equivalence. -/
@[simp]
theorem transportOrderIso_symm_apply (e : M ≃ₗ[R] N)
    (A : letI : Comodule R C N := Comodule.Transport e; Subcomodule R C N) :
    letI : Comodule R C N := Comodule.Transport e
    (transportOrderIso e).symm A = A.map (Comodule.transportInvHom e) :=
  rfl

/-- The forward transport correspondence maps the underlying submodule along the linear
equivalence. -/
theorem transportOrderIso_apply_toSubmodule (e : M ≃ₗ[R] N) (A : Subcomodule R C M) :
    letI : Comodule R C N := Comodule.Transport e
    (transportOrderIso e A).toSubmodule = Submodule.orderIsoMapComap e A.toSubmodule := by
  let _ : Comodule R C N := Comodule.Transport e
  rw [transportOrderIso_apply, map_toSubmodule, Comodule.transportToHom_toLinearMap,
    Submodule.orderIsoMapComap_apply]

/-- The inverse transport correspondence maps the underlying submodule along the inverse linear
equivalence. -/
theorem transportOrderIso_symm_apply_toSubmodule (e : M ≃ₗ[R] N)
    (A : letI : Comodule R C N := Comodule.Transport e; Subcomodule R C N) :
    letI : Comodule R C N := Comodule.Transport e
    ((transportOrderIso e).symm A).toSubmodule =
      (Submodule.orderIsoMapComap e).symm A.toSubmodule := by
  let _ : Comodule R C N := Comodule.Transport e
  rw [transportOrderIso_symm_apply, map_toSubmodule,
    Comodule.transportInvHom_toLinearMap]
  exact (Submodule.orderIsoMapComap_symm_apply' e A.toSubmodule).symm

end Subcomodule

end TauCeti
