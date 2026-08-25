/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNSmul

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The index of `n • G` in a finitely generated commutative group

Mathlib's `Mathlib/GroupTheory/IndexNSmul.lean` computes the index of the image of the
multiplication-by-`n` map `nsmulAddMonoidHom n` on a group that is **free** and finitely generated
as a `ℤ`-module: `AddSubgroup.index_range_nsmul` gives `n ^ finrank ℤ M`. This file drops freeness.

## Main results

* `AddSubgroup.index_range_nsmul_of_fg`: **the index of `n • G` in a finitely generated commutative
  group** `G` is `n ^ finrank ℤ G * Nat.card G[n]`, where `G[n]` is the `n`-torsion subgroup. Over a
  free group the torsion factor is `1` and this is Mathlib's `AddSubgroup.index_range_nsmul`; the
  extra factor is exactly what torsion contributes. The proof runs the structure theorem
  `AddCommGroup.equiv_free_prod_directSum_zmod` and reduces to the free case on the free part and
  to a counting argument on the finite part.
* `AddSubgroup.index_range_nsmul_mul_card_ker`: for a subgroup `U ≤ G` of finite index,
  `(G : nG) * #U[n] = #G[n] * (U : nU)`. This is the cross-multiplied form of "`(G : nG) / #G[n]`
  is unchanged on passing to a finite-index subgroup", and only the cross-multiplied form is
  asserted: nothing here forces `G[n]` finite or the indices nonzero, and `Nat.card` and
  `AddSubgroup.index` are both `0` on infinite arguments, so neither ratio need be defined.
* `AddEquiv.map_ker_nsmulAddMonoidHom` and `AddEquiv.index_range_nsmulAddMonoidHom`: an additive
  equivalence carries `G[n]` to `H[n]` and preserves the index of `n • G`. These are the kernel
  counterparts of Mathlib's `AddEquiv.map_range_nsmulAddMonoidHom`.

What the descent needs here is the exact count, not merely finiteness of the index.
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 makes explicit `2`-descent a target in its own
right, naming "the theorem converting its cardinality into a Mordell–Weil rank bound" and taking an
explicit rank computation as its acceptance test. That conversion is this formula solved for the
rank: from `(G : nG) = n ^ finrank ℤ G * Nat.card G[n]`, a bound on the Selmer cardinality gives a
bound on `finrank ℤ G`. Finiteness of the index alone carries no rank information — Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, recorded below as already available, supplies
exactly that and no more — so the free-case theorem this file generalises cannot be substituted for
it either. The same formula is in turn the group-theoretic input to the finiteness of the Selmer
group `K(S,n)` that the layer's weak Mordell–Weil bullet names, for the finitely generated — not
free — group of `S`-units.

Everything here is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header,
and each declaration carries its source name.

**Not ported from that file**, because Mathlib or this repository already has them: its
`Module.finite_int_additive` and `Group.fg_of_module_finite_int` (Mathlib's
`AddMonoid.FG.to_moduleFinite_int` and `Module.Finite.iff_addGroup_fg` composed with
`AddGroup.fg_iff_mul_fg`), `finite_of_fg_of_pow_eq_one` (`CommGroup.finite_of_fg_isMulTorsion`),
`finite_modPow` (`Subgroup.finiteIndex_range_powMonoidHom_of_fg`), `card_ker_mul_card_range` and
`index_range_eq_card_ker` (`AddSubgroup.index_range`, which needs only `FiniteIndex` on the kernel
rather than a finite ambient group, so the counting lemma that derived it is unnecessary),
`ker_nsmulAddMonoidHom` (`AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree` through
`AddMonoidHom.ker_eq_bot_iff`), its `nsmulAddMonoidHom_range_prod` and `nsmulAddMonoidHom_ker_prod`
(`AddMonoidHom.range_prodMap` and `AddMonoidHom.ker_prodMap`, which apply once multiplication by
`n` on a product is identified with the componentwise `AddMonoidHom.prodMap`, a step the proof
below takes directly), and its `Subgroup.fg_of_commGroup_fg` and
`Group.fg_of_fg_ker_of_fg_range` (both in `TauCeti/GroupTheory/Finiteness.lean`). Its
`Module.rank_eq_zero_of_finite` has no Mathlib counterpart but is a three-line consequence of
`rank_eq_zero_iff` used exactly once, so it is inlined at that use site rather than given a name.
The source predates those additions, several of which its own author upstreamed, so check Mathlib
again before porting anything further from it.

Its `AddMonoidHom.range_nsmulAddMonoidHom`, which identifies the range of multiplication by `n` on
a commutative ring with the ideal generated by `n`, is a statement about rings rather than a step
in this index computation, which nowhere uses it. It belongs with the ring-theoretic development
that first needs it, not here.
-/

public section

open Module

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- The relative index of `nU` in `nG` equals the index of `G[n] ⊔ U`.
A step of `index_range_nsmul_mul_card_ker`. -/
-- Statement adapted from the private `relIndex_range_comp_subtype` in Michael Stoll's
-- `EllipticCurves` (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`); the proof
-- here is Mathlib's `AddSubgroup.relIndex_map_map` rather than the source's own surjection
-- `G → nG ⧸ nU` and quotient-isomorphism argument.
private lemma relIndex_range_comp_subtype (U : AddSubgroup G) (n : ℕ) :
    (((nsmulAddMonoidHom (α := G) n).comp U.subtype).range).relIndex
        (nsmulAddMonoidHom (α := G) n).range =
      ((nsmulAddMonoidHom (α := G) n).ker ⊔ U).index := by
  set φG := nsmulAddMonoidHom (α := G) n
  -- `nU` is `φG(U)` and `nG` is `φG(⊤)`, so `relIndex_map_map` applies; `⊤ ⊔ ker = ⊤`
  -- turns the resulting relative index into a plain index.
  have hU : (φG.comp U.subtype).range = U.map φG := by ext x; simp
  rw [hU, AddMonoidHom.range_eq_map φG, AddSubgroup.relIndex_map_map, top_sup_eq,
    AddSubgroup.relIndex_top_right, sup_comm]

/-- The second isomorphism theorem applied to `G[n]` and `U`: `(U : G[n] ⊔ U) * #U[n] = #G[n]`.
A step of `index_range_nsmul_mul_card_ker`. -/
-- Adapted from the private `relIndex_sup_ker_mul_card_ker` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
private lemma relIndex_sup_ker_mul_card_ker (U : AddSubgroup G) (n : ℕ) :
    U.relIndex ((nsmulAddMonoidHom (α := G) n).ker ⊔ U) *
        Nat.card (nsmulAddMonoidHom (α := U) n).ker =
      Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  have h2 : Nat.card (φG.ker ⧸ U.addSubgroupOf φG.ker) = U.relIndex (φG.ker ⊔ U) :=
    Nat.card_congr (QuotientAddGroup.quotientInfEquivSumNormalQuotient φG.ker U).toEquiv
  have h3 : Nat.card (U.addSubgroupOf φG.ker) = Nat.card φU.ker :=
    Nat.card_congr
      ⟨fun x ↦ ⟨⟨(x : G), x.2⟩, Subtype.ext (x : φG.ker).2⟩,
        fun y ↦ ⟨⟨(y : U), congrArg Subtype.val y.2⟩, (y : U).2⟩,
        fun x ↦ rfl, fun y ↦ rfl⟩
  rw [← h2, ← h3]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

/-- **For a subgroup `U` of finite index in a commutative group `G` and any `n`,
`(G : nG) * #U[n] = #G[n] * (U : nU)`.** This is the cross-multiplied form of "`(G : nG) / #G[n]`
is unchanged on passing to a finite-index subgroup"; it is the product, not the quotient
statement, that holds at this generality, since with `G[n]` not assumed finite `Nat.card` and
`AddSubgroup.index` may both be `0` and neither ratio need be defined. -/
-- Adapted from `AddSubgroup.index_range_nsmul_mul_card_ker` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
theorem index_range_nsmul_mul_card_ker (U : AddSubgroup G) [U.FiniteIndex] (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).range.index *
        Nat.card ((nsmulAddMonoidHom (α := U) n)).ker =
      Nat.card ((nsmulAddMonoidHom (α := G) n)).ker *
        (nsmulAddMonoidHom (α := U) n).range.index := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  set B : AddSubgroup G := (φG.comp U.subtype).range
  set C : AddSubgroup G := φG.ker ⊔ U
  -- the small subgroup `B = nU` sits in both `nG` and `U`
  have hBA : B ≤ φG.range := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hBU : B ≤ U := by
    rintro _ ⟨u, rfl⟩
    exact U.nsmul_mem u.2 n
  have hUC : U ≤ C := le_sup_right
  -- `B.relIndex U` is the index of `nU` in `U`
  have hrBU : B.relIndex U = φU.range.index := by
    have h : B.addSubgroupOf U = φU.range := by
      ext u
      exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, Subtype.ext hw⟩, fun ⟨w, hw⟩ ↦ ⟨w, congrArg Subtype.val hw⟩⟩
    rw [relIndex, h]
  have hrBA : B.relIndex φG.range = C.index := relIndex_range_comp_subtype U n
  have hUK : U.relIndex C * Nat.card φU.ker = Nat.card φG.ker :=
    relIndex_sup_ker_mul_card_ker U n
  -- assemble
  have h24 : C.index * φG.range.index = φU.range.index * U.index := by
    rw [← hrBA, ← hrBU, relIndex_mul_index hBA, relIndex_mul_index hBU]
  have hCne : C.index ≠ 0 := by
    intro h
    exact FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.index_dvd_of_le hUC))
  have hA : φG.range.index = φU.range.index * U.relIndex C := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hCne) ?_
    rw [h24, ← relIndex_mul_index hUC]
    ring
  calc φG.range.index * Nat.card φU.ker
      = φU.range.index * (U.relIndex C * Nat.card φU.ker) := by rw [hA]; ring
    _ = φU.range.index * Nat.card φG.ker := by rw [hUK]
    _ = Nat.card φG.ker * φU.range.index := mul_comm _ _

end AddSubgroup

namespace AddEquiv

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An additive equivalence maps `M[n]` to `N[n]`. This is the kernel counterpart of Mathlib's
`AddEquiv.map_range_nsmulAddMonoidHom`. -/
-- Adapted from `AddEquiv.map_ker_nsmulAddMonoidHom` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
lemma map_ker_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- The index of `n • M` is invariant under additive equivalence. -/
-- Adapted from `AddEquiv.index_range_nsmulAddMonoidHom` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
lemma index_range_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = (nsmulAddMonoidHom (α := N) n).range.index := by
  simpa [AddEquiv.map_range_nsmulAddMonoidHom]
    using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := M) n).range e).symm

end AddEquiv

namespace AddSubgroup

open scoped DirectSum in
/-- **The index of `n • G` in a finitely generated commutative group** `G` is
`n ^ finrank ℤ G * #G[n]`, where `G[n]` is the `n`-torsion subgroup.

This extends Mathlib's `AddSubgroup.index_range_nsmul`, which is the free case: there the torsion
subgroup is trivial and the second factor is `1`. -/
-- Adapted from `AddSubgroup.index_range_nsmul_of_fg` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`). Two steps are discharged from
-- Mathlib rather than from the source's own helpers: `AddSubgroup.index_range` replaces its
-- `AddMonoidHom.index_range_eq_card_ker`, and the rank-zero step is inlined in place of its
-- `Module.rank_eq_zero_of_finite`.
theorem index_range_nsmul_of_fg (G : Type*) [AddCommGroup G] [AddGroup.FG G] {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx : (nsmulAddMonoidHom (α := G) n).range.index
      = (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index :=
    AddEquiv.index_range_nsmulAddMonoidHom eqv n
  have hker : Nat.card (nsmulAddMonoidHom (α := G) n).ker
      = Nat.card (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact Nat.card_congr
      (AddSubgroup.equivMapOfInjective _ eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 : Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π := LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i)) with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 : LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun x := x.1.2
            map_add' _ _ := rfl
            map_smul' _ _ := rfl
            invFun t := ⟨(0, t), rfl⟩
            left_inv x := Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv t := rfl }
        rw [e2.rank_eq]
        -- a finite module over a ring of characteristic zero has rank `0`
        exact rank_eq_zero_iff.mpr fun x ↦ ⟨addOrderOf x,
          Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
          by rw [Nat.cast_smul_eq_nsmul]; exact addOrderOf_nsmul_eq_zero x⟩
      rw [← π.rank_range_add_rank_ker, LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 : finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  -- multiplication by `n` on a product is componentwise, so it is `AddMonoidHom.prodMap`
  have hprod : nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n =
      (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).prodMap
        (nsmulAddMonoidHom (α := ⨁ i, ZMod (p i ^ e i)) n) := by
    ext x <;> simp
  rw [hidx, hker, hrk, hprod, AddMonoidHom.range_prodMap, AddSubgroup.index_prod,
    AddSubgroup.index_range_nsmul, AddSubgroup.index_range,
    AddMonoidHom.ker_prodMap, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end AddSubgroup

end
