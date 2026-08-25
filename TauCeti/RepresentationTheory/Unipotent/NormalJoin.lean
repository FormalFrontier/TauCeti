/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.Unipotent.Solvable
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Joins of normal unipotent linear groups

Let `U` and `W` be subgroups of a group acting on a finite-dimensional vector space, with `W`
normalizing `U`. If every element of each subgroup acts unipotently, then every element of `U ⊔ W`
acts unipotently. The key point is that the common fixed space of `U` is invariant under `W`.
Kolchin's common fixed-vector theorem applied to `W` on that space therefore produces a line fixed
by both subgroups. Repeating the argument on the quotient gives a simultaneous upper-unitriangular
basis for their join. In particular, the result applies when `U` is normal in the ambient group.

This is the linear-algebraic core of closure of connected normal unipotent affine subgroups under
binary products. The scheme-theoretic argument additionally has to identify the geometric points
of the multiplication image with products of points of the two source subgroups.

## Main declarations

* `Representation.exists_common_fixed_vector_of_le_normalizer_isUnipotent`: two subgroups, one
  normalized by the other, acting unipotently have a common nonzero fixed vector.
* `Representation.exists_basis_isUpperUnitriangular_of_le_normalizer_isUnipotent`: if they generate
  the ambient group, it is simultaneously upper unitriangular.
* `Representation.isNilpotent_sub_one_of_mem_sup_of_le_normalizer_isUnipotent`: the corresponding
  result for an arbitrary join inside a larger group.

## References

* A. Borel, *Linear Algebraic Groups*, Theorem 4.8 and Proposition 14.4.
* T. A. Springer, *Linear Algebraic Groups*, Proposition 2.4.12.

This supplies the representation-theoretic product step in Layer 5, "The unipotent radical", of
the ReductiveGroups roadmap.
-/

public section

open Matrix Module

namespace TauCeti

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Common fixed vector when a normal subgroup and a second subgroup act unipotently. -/
private theorem _root_.Representation.exists_common_fixed_vector_of_normal_isUnipotent_aux
    [FiniteDimensional K V] [Nontrivial V]
    (rho : Representation K G V) (U W : Subgroup G) [U.Normal]
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ x : V, x ≠ 0 ∧ (∀ u : U, rho u x = x) ∧ ∀ w : W, rho w x = x := by
  obtain ⟨x, hx, hxU⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent (rho.comp U.subtype) hU
  let S := Representation.invariants (rho.comp U.subtype)
  have hxS : x ∈ S := hxU
  let xS : S := ⟨x, hxS⟩
  have : Nontrivial S := ⟨xS, 0, fun h ↦ hx (congrArg Subtype.val h)⟩
  let rhoW : Representation K W S := (rho.toInvariants U).comp W.subtype
  have hW' (w : W) : IsNilpotent (rhoW w - 1) := by
    have hinvariant : Set.MapsTo (rho (w : G) - (1 : Module.End K V)) S S := by
      intro y hy
      exact S.sub_mem (Representation.le_comap_invariants rho U (w : G) hy) hy
    have hrestrict := Module.End.isNilpotent.restrict hinvariant (hW w)
    have heq : rhoW w - 1 =
        (rho (w : G) - (1 : Module.End K V)).restrict hinvariant := by
      ext y
      have hrestrict_apply :=
        congrArg Subtype.val (LinearMap.restrict_apply hinvariant y)
      have hrhoW_apply : (rhoW w y : V) = rho (w : G) y := by
        -- `toInvariants` and representation composition are abbreviations, so their application
        -- rule is definitional rather than a separately named theorem.
        rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, hrhoW_apply]
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using hrestrict_apply.symm
    rwa [heq]
  obtain ⟨y, hy, hyW⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent rhoW hW'
  refine ⟨y, fun h ↦ hy (Subtype.ext h), y.2, fun w ↦ ?_⟩
  exact congrArg Subtype.val (hyW w)

/-- **Common fixed vector for two unipotent subgroups, one normalized by the other.**
If `W` normalizes `U` and both subgroups act unipotently in a nonzero finite-dimensional
representation, they fix a common nonzero vector. -/
theorem _root_.Representation.exists_common_fixed_vector_of_le_normalizer_isUnipotent
    [FiniteDimensional K V] [Nontrivial V]
    (rho : Representation K G V) (U W : Subgroup G)
    (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ x : V, x ≠ 0 ∧ (∀ u : U, rho u x = x) ∧ ∀ w : W, rho w x = x := by
  let U' : Subgroup (W ⊔ U : Subgroup G) := U.subgroupOf (W ⊔ U)
  let W' : Subgroup (W ⊔ U : Subgroup G) := W.subgroupOf (W ⊔ U)
  let rhoJ : Representation K (W ⊔ U : Subgroup G) V := rho.comp (W ⊔ U).subtype
  let _ : U'.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hWU
  have hU' (u : U') : IsNilpotent (rhoJ u - 1) := by
    exact hU ⟨u, u.2⟩
  have hW' (w : W') : IsNilpotent (rhoJ w - 1) := by
    exact hW ⟨w, w.2⟩
  obtain ⟨x, hx, hxU, hxW⟩ :=
    rhoJ.exists_common_fixed_vector_of_normal_isUnipotent_aux U' W' hU' hW'
  refine ⟨x, hx, fun u ↦ ?_, fun w ↦ ?_⟩
  · exact hxU (⟨⟨u, (le_sup_right : U ≤ W ⊔ U) u.2⟩, u.2⟩ : U')
  · exact hxW (⟨⟨w, (le_sup_left : W ≤ W ⊔ U) w.2⟩, w.2⟩ : W')

/-- If one subgroup is normalized by a second subgroup, they generate the ambient group, and each
acts unipotently, then the whole group acts unipotently. -/
private theorem _root_.Representation.isNilpotent_sub_one_of_normal_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G)
    (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ⊔ W = ⊤)
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) (g : G) :
    IsNilpotent (rho g - 1) := by
  generalize hdim : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      by_cases hV : Nontrivial V
      · let _ : Nontrivial V := hV
        obtain ⟨x, hx, hxU, hxW⟩ :=
          rho.exists_common_fixed_vector_of_le_normalizer_isUnipotent U W hWU hU hW
        have hfixed (z : G) : rho z x = x := by
          have hz : z ∈ U ⊔ W := by rw [hUW]; exact Subgroup.mem_top z
          obtain ⟨u, hu, w, hw, rfl⟩ :=
            (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
              (H := U) (K := W) hWU).mp hz
          rw [map_mul, Module.End.mul_apply, hxW ⟨w, hw⟩, hxU ⟨u, hu⟩]
        let p : Submodule K V := K ∙ x
        have hpdim : finrank K p = 1 := finrank_span_singleton hx
        have hp_fixed (z : G) (y : p) : rho z (y : V) = y := by
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
          rw [← ha, map_smul, hfixed]
        have hp (z : G) : p ≤ p.comap (rho z) := by
          intro y hy
          rw [Submodule.mem_comap]
          rw [hp_fixed z ⟨y, hy⟩]
          exact hy
        let q : Representation K G (V ⧸ p) := rho.quotient p hp
        have quotient_sub_one_eq_mapQ (z : G)
            (hsub : p ≤ p.comap (rho z - 1)) :
            q z - 1 = p.mapQ p (rho z - 1) hsub := by
          ext y
          simp only [Representation.quotient_apply, LinearMap.coe_comp, Function.comp_apply,
            Submodule.mkQ_apply, LinearMap.sub_apply, Submodule.mapQ_apply, End.one_apply,
            Submodule.Quotient.mk_sub, q]
        have hq (z : G) (hz : IsNilpotent (rho z - 1)) : IsNilpotent (q z - 1) := by
          have hsub : p ≤ p.comap (rho z - 1) := by
            intro y hy
            rw [Submodule.mem_comap]
            simpa only [LinearMap.sub_apply, Module.End.one_apply] using p.sub_mem (hp z hy) hy
          rw [quotient_sub_one_eq_mapQ z hsub]
          exact Module.End.IsNilpotent.mapQ hsub hz
        have hqdim : finrank K (V ⧸ p) < d := by
          have hsum := Module.finrank_quotient_add_finrank_le p
          rw [hpdim, hdim] at hsum
          omega
        obtain ⟨n, hn⟩ := ih (finrank K (V ⧸ p)) hqdim q
          (fun u ↦ hq u (hU u)) (fun w ↦ hq w (hW w)) rfl
        have hsub : p ≤ p.comap (rho g - 1) := by
          intro y hy
          rw [Submodule.mem_comap]
          simpa only [LinearMap.sub_apply, Module.End.one_apply] using p.sub_mem (hp g hy) hy
        rw [quotient_sub_one_eq_mapQ g hsub] at hn
        let f : Module.End K V := rho g - 1
        refine ⟨n + 1, ?_⟩
        ext y
        rw [pow_succ', Module.End.mul_apply]
        have hymem : (f ^ n) y ∈ p := by
          apply (Submodule.Quotient.mk_eq_zero p).mp
          have hz := LinearMap.congr_fun hn (p.mkQ y)
          rw [← p.mapQ_pow hsub n] at hz
          simpa only [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_apply] using hz
        rw [LinearMap.sub_apply, Module.End.one_apply, hp_fixed g ⟨(f ^ n) y, hymem⟩, sub_self,
          LinearMap.zero_apply]
      · let _ : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
        exact ⟨1, Subsingleton.elim _ _⟩

/-- Two unipotent subgroups, one normalized by the other, which generate the ambient group are
simultaneously upper unitriangular.

The generation hypothesis is the natural form used for a product subgroup: after restricting an
ambient representation to `U ⊔ W`, the images of `U` and `W` generate the whole restricted group.
-/
theorem _root_.Representation.exists_basis_isUpperUnitriangular_of_le_normalizer_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G)
    (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ⊔ W = ⊤)
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n) K V),
      ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular :=
  rho.exists_basis_isUpperUnitriangular_of_isUnipotent
    (rho.isNilpotent_sub_one_of_normal_isUnipotent U W hWU hUW hU hW)

/-- Every element of the join of two unipotent subgroups, one normalized by the other, acts
unipotently.

This is the form used for products of subgroup schemes: normalization makes the setwise product a
subgroup, and that product is the join. -/
theorem _root_.Representation.isNilpotent_sub_one_of_mem_sup_of_le_normalizer_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G)
    (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) {g : G} (hg : g ∈ U ⊔ W) :
    IsNilpotent (rho g - 1) := by
  let J : Subgroup G := W ⊔ U
  let U' : Subgroup J := U.comap J.subtype
  let W' : Subgroup J := W.comap J.subtype
  let rhoJ : Representation K J V := rho.comp J.subtype
  let _ : U'.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hWU
  have hU_le : U ≤ J := le_sup_right
  have hW_le : W ≤ J := le_sup_left
  have hU_range : U ≤ J.subtype.range := by simpa only [Subgroup.range_subtype] using hU_le
  have hW_range : W ≤ J.subtype.range := by simpa only [Subgroup.range_subtype] using hW_le
  have hsup : U' ⊔ W' = ⊤ := by
    rw [Subgroup.comap_sup_eq_of_le_range J.subtype hU_range hW_range]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_top, iff_true]
    rw [sup_comm]
    exact x.2
  have hU' (u : U') : IsNilpotent (rhoJ u - 1) := by
    exact hU ⟨u, u.2⟩
  have hW' (w : W') : IsNilpotent (rhoJ w - 1) := by
    exact hW ⟨w, w.2⟩
  have hgJ : g ∈ J := by
    have hJ : J = U ⊔ W := sup_comm W U
    rw [hJ]
    exact hg
  let gJ : J := ⟨g, hgJ⟩
  exact rhoJ.isNilpotent_sub_one_of_normal_isUnipotent U' W'
    Subgroup.le_normalizer_of_normal hsup hU' hW' gJ

end

end TauCeti
