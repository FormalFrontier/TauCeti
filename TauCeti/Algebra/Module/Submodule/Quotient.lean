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

* `TauCeti.Submodule.iccOrderIsoQuotientOfMapEq`: the interval/quotient correspondence for a
  specified copy of the lower endpoint inside the upper endpoint.
-/

public section

namespace TauCeti

namespace Submodule

section QuotientInterval

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Submodules of `q` containing a submodule whose ambient image is `p` are the same as ambient
submodules in the interval from `p` to `q`. -/
private def iciSubmoduleOrderIsoIcc {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Ici r ≃o Set.Icc p q := by
  let e := q.mapIic
  have he : (e r : Submodule R M) = p := by
    rw [Submodule.coe_mapIic_apply]
    exact hr
  refine (e.Ici r).trans
    { toFun := fun N ↦ by
        have hbase : (e r : Submodule R M) ≤ N.1.1 := N.2
        refine ⟨N.1.1, ?_, N.1.2⟩
        exact he.symm.le.trans hbase
      invFun := fun N ↦ by
        have hN : p ≤ N.1 ∧ N.1 ≤ q := N.2
        refine ⟨⟨N.1, hN.2⟩, ?_⟩
        exact he.le.trans hN.1
      left_inv := fun N ↦ by rfl
      right_inv := fun N ↦ by rfl
      map_rel_iff' := Iff.rfl }

@[simp]
private theorem coe_iciSubmoduleOrderIsoIcc_symm_apply {p q : Submodule R M}
    (r : Submodule R q) (hr : r.map q.subtype = p) (N : Set.Icc p q) :
    (((iciSubmoduleOrderIsoIcc r hr).symm N).1 : Submodule R q) =
      N.1.comap q.subtype := by
  ext x
  rfl

/-- The interval correspondence for a specified copy `r` of the lower endpoint inside `q`. -/
def iccOrderIsoQuotientOfMapEq {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) : Set.Icc p q ≃o Submodule R (q ⧸ r) :=
  (iciSubmoduleOrderIsoIcc r hr).symm.trans (Submodule.comapMkQRelIso r).symm

/-- A representative belongs to the quotient submodule in the interval correspondence exactly
when its underlying ambient element belongs to the corresponding interval submodule. -/
@[simp]
theorem mk_mem_iccOrderIsoQuotientOfMapEq_iff {p q : Submodule R M} (r : Submodule R q)
    (hr : r.map q.subtype = p) (N : Set.Icc p q) (x : q) :
    Submodule.Quotient.mk x ∈ Submodule.iccOrderIsoQuotientOfMapEq r hr N ↔
      (x : M) ∈ N.1 := by
  let N' : Set.Ici r := (iciSubmoduleOrderIsoIcc r hr).symm N
  let Q : Submodule R (q ⧸ r) := (Submodule.comapMkQRelIso r).symm N'
  have hcomap : Q.comap r.mkQ = N'.1 := congrArg Subtype.val
    ((Submodule.comapMkQRelIso r).apply_symm_apply N')
  have hQ : Submodule.iccOrderIsoQuotientOfMapEq r hr N = Q := rfl
  rw [hQ, ← r.mkQ_apply, ← Submodule.mem_comap, hcomap]
  have hN' : N'.1 = ((iciSubmoduleOrderIsoIcc r hr).symm N).1 := rfl
  rw [hN', coe_iciSubmoduleOrderIsoIcc_symm_apply]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]

/-- An ambient representative belongs to the interval submodule corresponding to `Q` exactly
when its quotient class belongs to `Q`. -/
@[simp]
theorem mem_iccOrderIsoQuotientOfMapEq_symm_apply_iff {p q : Submodule R M}
    (r : Submodule R q)
    (hr : r.map q.subtype = p) (Q : Submodule R (q ⧸ r)) (x : q) :
    (x : M) ∈ ((Submodule.iccOrderIsoQuotientOfMapEq r hr).symm Q).1 ↔
      Submodule.Quotient.mk x ∈ Q := by
  simpa only [OrderIso.apply_symm_apply] using
    (Submodule.mk_mem_iccOrderIsoQuotientOfMapEq_iff r hr
      ((Submodule.iccOrderIsoQuotientOfMapEq r hr).symm Q) x).symm

/-- The correspondence theorem restricted to an interval: submodules between `p` and `q` are
order-isomorphic to submodules of the quotient of `q` by the copy of `p` in `q`. -/
def iccOrderIsoQuotient {p q : Submodule R M} (h : p ≤ q) :
    Set.Icc p q ≃o Submodule R (q ⧸ p.submoduleOf q) := by
  have hmap : (p.submoduleOf q).map q.subtype = p := by
    rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_of_le_right h]
  exact Submodule.iccOrderIsoQuotientOfMapEq (p.submoduleOf q) hmap

/-- A representative belongs to the quotient submodule corresponding to `N` exactly when its
underlying ambient element belongs to `N`. -/
@[simp]
theorem mk_mem_iccOrderIsoQuotient_iff {p q : Submodule R M} (h : p ≤ q)
    (N : Set.Icc p q) (x : q) :
    Submodule.Quotient.mk x ∈ Submodule.iccOrderIsoQuotient h N ↔ (x : M) ∈ N.1 := by
  have hmap : (p.submoduleOf q).map q.subtype = p := by
    rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_of_le_right h]
  have hiso : Submodule.iccOrderIsoQuotient h =
      Submodule.iccOrderIsoQuotientOfMapEq (p.submoduleOf q) hmap := rfl
  rw [hiso]
  exact Submodule.mk_mem_iccOrderIsoQuotientOfMapEq_iff (p.submoduleOf q) hmap N x

/-- An ambient representative belongs to the interval submodule corresponding to `Q` exactly
when its quotient class belongs to `Q`. -/
@[simp]
theorem mem_iccOrderIsoQuotient_symm_apply_iff {p q : Submodule R M} (h : p ≤ q)
    (Q : Submodule R (q ⧸ p.submoduleOf q)) (x : q) :
    (x : M) ∈ ((Submodule.iccOrderIsoQuotient h).symm Q).1 ↔
      Submodule.Quotient.mk x ∈ Q := by
  simpa only [OrderIso.apply_symm_apply] using
    (Submodule.mk_mem_iccOrderIsoQuotient_iff h
      ((Submodule.iccOrderIsoQuotient h).symm Q) x).symm

end QuotientInterval

end Submodule

end TauCeti
