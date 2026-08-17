/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodule intervals and quotients

This file records the generic order correspondence between a submodule interval and submodules of
the associated quotient.

## Main declarations

* `TauCeti.mapIic_symm_apply`: the inverse of `Submodule.mapIic` takes inverse images
  along the inclusion.
* `TauCeti.iccOrderIsoQuotientOfMapEq`: the interval/quotient correspondence for a
  specified copy of the lower endpoint inside the upper endpoint.
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
    refine Subtype.ext ?_
    change (↑(q.mapIic (q.mapIic.symm ⟨N.1, N.2.2⟩)) : Submodule R M) = ↑N
    rw [OrderIso.apply_symm_apply]
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

end TauCeti
