/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodule intervals and quotients

This file records the generic order correspondence between a submodule interval and submodules of
the associated quotient, and the identifications of *subquotients* `↥B ⧸ A` that a linear map
induces when it is injective or surjective.

## Main declarations

* `TauCeti.mapIic_symm_apply`: the inverse of `Submodule.mapIic` takes inverse images
  along the inclusion.
* `TauCeti.iccOrderIsoQuotientOfMapEq`: the interval/quotient correspondence for a
  specified copy of the lower endpoint inside the upper endpoint.
* `TauCeti.mapSubquotientEquivOfInjective`: an injective linear map identifies the subquotient of
  the images of two submodules with the subquotient of the two submodules themselves.
* `TauCeti.comapSubquotientEquivOfSurjective`: a surjective linear map identifies the subquotient
  of the preimages of two submodules with the subquotient of the two submodules themselves.
-/

public section

namespace TauCeti

section QuotientInterval

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The inverse of `Submodule.mapIic` takes the inverse image along the inclusion.  This is the
`symm`-side counterpart of Mathlib's `Submodule.coe_mapIic_apply`. -/
theorem mapIic_symm_apply (p : Submodule R M) (N : Set.Iic p) :
    p.mapIic.symm N = (N : Submodule R M).comap p.subtype :=
  rfl

/-- Submodules of `q` containing a submodule whose ambient image is `p` are the same as ambient
submodules in the interval from `p` to `q`. -/
private def iciSubmoduleOrderIsoIcc {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Ici r ≃o Set.Icc p q where
  toFun N := ⟨(q.mapIic N.1 : Submodule R M), by
    refine ⟨?_, (q.mapIic N.1).2⟩
    rw [Submodule.coe_mapIic_apply, ← hr]
    exact Submodule.map_mono N.2⟩
  invFun N := ⟨q.mapIic.symm ⟨N.1, N.2.2⟩, by
    rw [mapIic_symm_apply]
    exact (Submodule.le_comap_map q.subtype r).trans
      (Submodule.comap_mono (hr.le.trans N.2.1))⟩
  left_inv N := Subtype.ext (q.mapIic.symm_apply_apply N.1)
  right_inv N := by
    apply Subtype.ext
    exact congrArg (fun P : Set.Iic q => (P : Submodule R M))
      (q.mapIic.apply_symm_apply ⟨N.1, N.2.2⟩)
  map_rel_iff' := by
    intro N₁ N₂
    exact Subtype.coe_le_coe.trans q.mapIic.le_iff_le

private theorem coe_iciSubmoduleOrderIsoIcc_symm_apply {p q : Submodule R M}
    (r : Submodule R q) (hr : r.map q.subtype = p) (N : Set.Icc p q) :
    (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) =
      N.1.comap q.subtype :=
  mapIic_symm_apply q ⟨N.1, N.2.2⟩

/-- The interval correspondence for a specified copy `r` of the lower endpoint inside `q`. -/
def iccOrderIsoQuotientOfMapEq {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Icc p q ≃o Submodule R (q ⧸ r) :=
  (iciSubmoduleOrderIsoIcc r hr).symm.trans (Submodule.comapMkQRelIso r).symm

/-- A representative belongs to the quotient submodule in the interval correspondence exactly
when its underlying ambient element belongs to the corresponding interval submodule. -/
@[simp]
theorem mk_mem_iccOrderIsoQuotientOfMapEq_iff {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) (N : Set.Icc p q) (x : q) :
    Submodule.Quotient.mk x ∈ iccOrderIsoQuotientOfMapEq r hr N ↔
      (x : M) ∈ N.1 := by
  have happly : iccOrderIsoQuotientOfMapEq r hr N =
      (Submodule.comapMkQRelIso r).symm ((iciSubmoduleOrderIsoIcc r hr).symm N) :=
    OrderIso.trans_apply _ _ N
  have hcomap : ((Submodule.comapMkQRelIso r).symm
      ((iciSubmoduleOrderIsoIcc r hr).symm N)).comap r.mkQ =
      (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) :=
    congrArg Subtype.val
      ((Submodule.comapMkQRelIso r).apply_symm_apply ((iciSubmoduleOrderIsoIcc r hr).symm N))
  rw [happly, ← r.mkQ_apply, ← Submodule.mem_comap, hcomap,
    coe_iciSubmoduleOrderIsoIcc_symm_apply, Submodule.mem_comap, Submodule.subtype_apply]

/-- An ambient representative belongs to the interval submodule corresponding to `Q` exactly
when its quotient class belongs to `Q`. -/
@[simp]
theorem mem_iccOrderIsoQuotientOfMapEq_symm_apply_iff {p q : Submodule R M}
    (r : Submodule R q)
    (hr : r.map q.subtype = p) (Q : Submodule R (q ⧸ r)) (x : q) :
    (x : M) ∈ ((iccOrderIsoQuotientOfMapEq r hr).symm Q).1 ↔
      Submodule.Quotient.mk x ∈ Q := by
  simpa only [OrderIso.apply_symm_apply] using
    (mk_mem_iccOrderIsoQuotientOfMapEq_iff r hr
      ((iccOrderIsoQuotientOfMapEq r hr).symm Q) x).symm

end QuotientInterval

section Subquotient

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An injective linear map carries the trace of `A` in `B` onto the trace of `A.map f` in
`B.map f`, so it descends to the subquotients. -/
theorem map_equivMapOfInjective_comap_subtype (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) :
    Submodule.map ((Submodule.equivMapOfInjective f hf B : ↥B ≃ₗ[R] ↥(B.map f)) :
        ↥B →ₗ[R] ↥(B.map f)) (Submodule.comap B.subtype A)
      = Submodule.comap (B.map f).subtype (A.map f) := by
  refine Submodule.map_injective_of_injective (B.map f).injective_subtype ?_
  have hcomp : (B.map f).subtype ∘ₗ
      ((Submodule.equivMapOfInjective f hf B : ↥B ≃ₗ[R] ↥(B.map f)) : ↥B →ₗ[R] ↥(B.map f))
        = f ∘ₗ B.subtype :=
    LinearMap.ext fun x => Submodule.coe_equivMapOfInjective_apply f hf B x
  rw [← Submodule.map_comp, hcomp, Submodule.map_comp, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, Submodule.map_inf f hf]

/-- **An injective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `M`
the subquotient cut out by the images `A.map f`, `B.map f` is the subquotient cut out by `A` and
`B` themselves; for `A ≤ B` this reads `B.map f ⧸ A.map f ≃ₗ[R] B ⧸ A`. -/
noncomputable def mapSubquotientEquivOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) :
    (↥(B.map f) ⧸ Submodule.comap (B.map f).subtype (A.map f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf B)
    (map_equivMapOfInjective_comap_subtype f hf A B)).symm

/-- `TauCeti.mapSubquotientEquivOfInjective` read on representatives: its inverse is induced by
the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    (mapSubquotientEquivOfInjective f hf A B).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x) := by
  rw [mapSubquotientEquivOfInjective, LinearEquiv.symm_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- `TauCeti.mapSubquotientEquivOfInjective` read on representatives, in the forward direction:
it undoes the restriction `Submodule.equivMapOfInjective` of `f` to `B`. -/
@[simp]
theorem mapSubquotientEquivOfInjective_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (A B : Submodule R M) (x : ↥B) :
    mapSubquotientEquivOfInjective f hf A B
        (Submodule.Quotient.mk (Submodule.equivMapOfInjective f hf B x)) =
      Submodule.Quotient.mk x := by
  rw [← mapSubquotientEquivOfInjective_symm_apply f hf A B x,
    LinearEquiv.apply_symm_apply]

/-- The kernel of `x ↦ f x mod A`, on the preimage of `B`, is the trace of the preimage of `A`. -/
theorem ker_mkQ_comp_submoduleComap (f : M →ₗ[R] N) (A B : Submodule R N) :
    LinearMap.ker ((Submodule.comap B.subtype A).mkQ ∘ₗ f.submoduleComap B)
      = Submodule.comap (B.comap f).subtype (A.comap f) := by
  ext x
  simp

/-- **A surjective linear map identifies subquotients.**  For arbitrary submodules `A`, `B` of `N`
the subquotient cut out by the preimages `A.comap f`, `B.comap f` is the subquotient cut out by `A`
and `B` themselves; for `A ≤ B` this reads `B.comap f ⧸ A.comap f ≃ₗ[R] B ⧸ A`. -/
noncomputable def comapSubquotientEquivOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) :
    (↥(B.comap f) ⧸ Submodule.comap (B.comap f).subtype (A.comap f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_submoduleComap f A B).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp
        (LinearMap.submoduleComap_surjective_of_surjective f B hf)))

/-- `TauCeti.comapSubquotientEquivOfSurjective` read on representatives: it is induced by the
restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    comapSubquotientEquivOfSurjective f hf A B (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.submoduleComap B x) := by
  rw [comapSubquotientEquivOfSurjective, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- `TauCeti.comapSubquotientEquivOfSurjective` read on representatives, in the inverse direction:
it undoes the restriction `LinearMap.submoduleComap` of `f` to the preimage of `B`. -/
@[simp]
theorem comapSubquotientEquivOfSurjective_symm_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A B : Submodule R N) (x : ↥(B.comap f)) :
    (comapSubquotientEquivOfSurjective f hf A B).symm
        (Submodule.Quotient.mk (f.submoduleComap B x)) = Submodule.Quotient.mk x := by
  rw [← comapSubquotientEquivOfSurjective_apply f hf A B x,
    LinearEquiv.symm_apply_apply]

end Subquotient

end TauCeti
