/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.GroupTheory.SemidirectProduct
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
import TauCeti.LinearAlgebra.ExtensionBasis
import TauCeti.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.Group

/-!
# Joins of normal unipotent linear groups

Let `U` be a normal subgroup and `W` a subgroup of a group acting on a finite-dimensional vector
space. If every element of each subgroup acts unipotently, then every element of `U ⊔ W` acts
unipotently. The key point is that the common fixed space of `U` is invariant under the ambient
group. Kolchin's common fixed-vector theorem applied to `W` on that space therefore produces a
line fixed by both subgroups. Repeating the argument on the quotient gives a simultaneous
upper-unitriangular basis for their join. Only `U` needs to be normal; this is stronger than the
binary-product application, where both subgroups are normal.

This is the linear-algebraic core of closure of connected normal unipotent affine subgroups under
binary products. The scheme-theoretic argument additionally has to identify the geometric points
of the multiplication image with products of points of the two source subgroups.

## Main declarations

* `Representation.exists_common_fixed_vector_of_normal_isUnipotent`: a normal subgroup and a
  second subgroup acting unipotently have a common nonzero fixed vector.
* `Representation.exists_basis_isUpperUnitriangular_of_normal_isUnipotent`: if they generate the
  ambient group, it is simultaneously upper unitriangular.
* `Representation.isNilpotent_sub_one_of_normal_isUnipotent`: every element of that ambient group
  acts unipotently.
* `Representation.isNilpotent_sub_one_of_mem_sup_of_normal_isUnipotent`: the corresponding result
  for an arbitrary join inside a larger group.

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

/-- The common fixed space of a subgroup in a representation. -/
private def fixedSubmodule (rho : Representation K G V) (U : Subgroup G) : Submodule K V where
  carrier := {x | ∀ u : U, rho u x = x}
  zero_mem' := by simp
  add_mem' hx hy u := by simp only [map_add, hx u, hy u]
  smul_mem' r x hx u := by simp only [map_smul, hx u]

/-- Membership in the common fixed space means being fixed by every subgroup element. -/
private theorem mem_fixedSubmodule_iff (rho : Representation K G V) (U : Subgroup G) (x : V) :
    x ∈ fixedSubmodule rho U ↔ ∀ u : U, rho u x = x :=
  Iff.rfl

/-- The common fixed space of a normal subgroup is an ambient subrepresentation. -/
private def fixedSubrepresentation (rho : Representation K G V) (U : Subgroup G) [U.Normal] :
    Subrepresentation rho where
  toSubmodule := fixedSubmodule rho U
  apply_mem_toSubmodule g x hx := by
    rw [mem_fixedSubmodule_iff] at hx ⊢
    intro u
    let ugu : U := ⟨g⁻¹ * (u : G) * g,
      (show U.Normal from inferInstance).conj_mem' (u : G) u.2 g⟩
    calc
      rho u (rho g x) = rho (u * g) x := by rw [map_mul, Module.End.mul_apply]
      _ = rho (g * (g⁻¹ * u * g)) x := by congr 2; group
      _ = rho g (rho ugu x) := by rw [map_mul, Module.End.mul_apply]
      _ = rho g x := by rw [hx ugu]

/-- **Common fixed vector for a normal unipotent subgroup and a second unipotent subgroup.**
If both subgroups act unipotently in a nonzero finite-dimensional representation, they fix a
common nonzero vector. -/
theorem _root_.Representation.exists_common_fixed_vector_of_normal_isUnipotent
    [FiniteDimensional K V] [Nontrivial V]
    (rho : Representation K G V) (U W : Subgroup G) [U.Normal]
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ x : V, x ≠ 0 ∧ (∀ u : U, rho u x = x) ∧ ∀ w : W, rho w x = x := by
  obtain ⟨x, hx, hxU⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent (rho.comp U.subtype) hU
  let S := fixedSubrepresentation rho U
  have hxS : x ∈ S.toSubmodule := hxU
  let xS : S.toSubmodule := ⟨x, hxS⟩
  have : Nontrivial S.toSubmodule := ⟨xS, 0, fun h ↦ hx (congrArg Subtype.val h)⟩
  let rhoW : Representation K W S.toSubmodule := S.toRepresentation.comp W.subtype
  have hW' (w : W) : IsNilpotent (rhoW w - 1) := by
    have hinvariant : Set.MapsTo (rho (w : G) - (1 : Module.End K V))
        S.toSubmodule S.toSubmodule := by
      intro y hy
      exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule w hy) hy
    have hrestrict := Module.End.isNilpotent.restrict hinvariant (hW w)
    have heq : rhoW w - 1 =
        (rho (w : G) - (1 : Module.End K V)).restrict hinvariant := by
      ext y
      rfl
    rwa [heq]
  obtain ⟨y, hy, hyW⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent rhoW hW'
  refine ⟨y, fun h ↦ hy (Subtype.ext h), y.2, fun w ↦ ?_⟩
  exact congrArg Subtype.val (hyW w)

/-- A normal subgroup and a second subgroup which generate the ambient group and act unipotently
are simultaneously upper unitriangular.

The generation hypothesis is the natural form used for a product subgroup: after restricting an
ambient representation to `U ⊔ W`, the images of `U` and `W` generate the whole restricted group.
-/
theorem _root_.Representation.exists_basis_isUpperUnitriangular_of_normal_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G) [U.Normal]
    (hUW : U ⊔ W = ⊤)
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n) K V),
      ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular := by
  generalize hdim : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      by_cases hV : Nontrivial V
      · let _ : Nontrivial V := hV
        -- First find a line fixed by both generators, hence by the group they generate.
        obtain ⟨x, hx, hxU, hxW⟩ :=
          rho.exists_common_fixed_vector_of_normal_isUnipotent U W hU hW
        have hfixed (g : G) : rho g x = x := by
          have hg : g ∈ U ⊔ W := by rw [hUW]; exact Subgroup.mem_top g
          obtain ⟨u, hu, w, hw, rfl⟩ :=
            (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
              (H := U) (K := W) (by rw [U.normalizer_eq_top]; exact le_top)).mp hg
          rw [map_mul, Module.End.mul_apply, hxW ⟨w, hw⟩, hxU ⟨u, hu⟩]
        let p : Submodule K V := K ∙ x
        have hpdim : finrank K p = 1 := finrank_span_singleton hx
        have hp_fixed (g : G) (y : p) : rho g (y : V) = y := by
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
          rw [← ha, map_smul, hfixed]
        have hp (g : G) : p ≤ p.comap (rho g) := by
          intro y hy
          change rho g y ∈ p
          rw [hp_fixed g ⟨y, hy⟩]
          exact hy
        let q : Representation K G (V ⧸ p) := rho.quotient p hp
        have q_apply (g : G) (y : V) : q g (p.mkQ y) = p.mkQ (rho g y) := by
          simp [q, Representation.quotient_apply, Submodule.mapQ_apply]
        have hqU (u : U) : IsNilpotent (q u - 1) := by
          have hsub : p ≤ p.comap (rho u - 1) := by
            intro y hy
            change rho u y - y ∈ p
            exact p.sub_mem (hp u hy) hy
          have hnil := Module.End.IsNilpotent.mapQ hsub (hU u)
          have heq : q u - 1 = p.mapQ p (rho u - 1) hsub := by
            ext y
            simp [q, Representation.quotient_apply, Submodule.mapQ_apply]
          rwa [heq]
        have hqW (w : W) : IsNilpotent (q w - 1) := by
          have hsub : p ≤ p.comap (rho w - 1) := by
            intro y hy
            change rho w y - y ∈ p
            exact p.sub_mem (hp w hy) hy
          have hnil := Module.End.IsNilpotent.mapQ hsub (hW w)
          have heq : q w - 1 = p.mapQ p (rho w - 1) hsub := by
            ext y
            simp [q, Representation.quotient_apply, Submodule.mapQ_apply]
          rwa [heq]
        have hqdim : finrank K (V ⧸ p) < d := by
          have hsum := Module.finrank_quotient_add_finrank_le p
          rw [hpdim, hdim] at hsum
          omega
        obtain ⟨n, bq, hbq⟩ := ih (finrank K (V ⧸ p)) hqdim q hqU hqW rfl
        -- Put the common fixed line before an upper-unitriangular basis of the quotient.
        let bp : Basis (Fin 1) K p := finBasisOfFinrankEq K p hpdim
        let b := extensionBasis p bp bq
        refine ⟨1 + n, b, fun g ↦ ?_⟩
        rw [Matrix.isUpperUnitriangular_def]
        constructor
        -- The extension basis gives four matrix blocks. The lower-left block vanishes because
        -- `p` is invariant; the lower-right block is the quotient matrix.
        · intro i j hji
          obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
          obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
          cases i with
          | inl i =>
              cases j with
              | inl j =>
                  simp only [finSumFinEquiv_apply_left] at hji
                  have := (Fin.strictMono_castAdd n).lt_iff_lt.mp hji
                  omega
              | inr j =>
                  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hji
                  change 1 + j.val < i.val at hji
                  omega
          | inr i =>
              cases j with
              | inl j =>
                  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
                    LinearMap.toMatrixAlgEquiv_apply]
                  have hmem : rho g (bp j : V) ∈ p := hp g (bp j).2
                  rw [extensionBasis_castAdd,
                    extensionBasis_repr_natAdd p bp bq (rho g (bp j : V)) i]
                  simp only [Submodule.mkQ_apply,
                    (Submodule.Quotient.mk_eq_zero p).mpr hmem, map_zero,
                    Finsupp.zero_apply]
              | inr j =>
                  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
                    LinearMap.toMatrixAlgEquiv_apply, extensionBasis_repr_natAdd]
                  rw [← q_apply]
                  rw [Submodule.mkQ_apply, extensionBasis_natAdd_mkQ]
                  simpa only [LinearMap.toMatrixAlgEquiv_apply] using
                    (hbq g |>.isUpperTriangular
                      ((Fin.strictMono_natAdd 1).lt_iff_lt.mp hji))
        · intro i
          obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
          cases i with
          | inl i =>
              rw [finSumFinEquiv_apply_left, LinearMap.toMatrixAlgEquiv_apply,
                extensionBasis_castAdd]
              rw [hp_fixed, extensionBasis_repr_castAdd]
              simp
          | inr i =>
              rw [finSumFinEquiv_apply_right, LinearMap.toMatrixAlgEquiv_apply,
                extensionBasis_repr_natAdd]
              rw [← q_apply]
              rw [Submodule.mkQ_apply, extensionBasis_natAdd_mkQ]
              simpa only [LinearMap.toMatrixAlgEquiv_apply] using hbq g |>.apply_diag i
      · let _ : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
        have hzero : finrank K V = 0 := Module.finrank_zero_of_subsingleton
        let b : Basis (Fin 0) K V := finBasisOfFinrankEq K V hzero
        refine ⟨0, b, fun g ↦ ?_⟩
        rw [Matrix.isUpperUnitriangular_def]
        exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

/-- If a normal subgroup and a second subgroup generate the ambient group and each acts
unipotently, then the whole group acts unipotently. -/
theorem _root_.Representation.isNilpotent_sub_one_of_normal_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G) [U.Normal]
    (hUW : U ⊔ W = ⊤)
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) (g : G) :
    IsNilpotent (rho g - 1) := by
  obtain ⟨n, b, hb⟩ :=
    rho.exists_basis_isUpperUnitriangular_of_normal_isUnipotent U W hUW hU hW
  rw [← IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv b).injective]
  simpa only [map_sub, map_one] using (hb g).isNilpotent_sub_one

/-- Every element of the join of a normal unipotent subgroup and a second unipotent subgroup acts
unipotently.

This is the form used for products of subgroup schemes: normality makes the setwise product a
subgroup, and the join is that product. -/
theorem _root_.Representation.isNilpotent_sub_one_of_mem_sup_of_normal_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G) [U.Normal]
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) {g : G} (hg : g ∈ U ⊔ W) :
    IsNilpotent (rho g - 1) := by
  let J : Subgroup G := U ⊔ W
  let U' : Subgroup J := U.comap J.subtype
  let W' : Subgroup J := W.comap J.subtype
  let rhoJ : Representation K J V := rho.comp J.subtype
  have hU_le : U ≤ J := le_sup_left
  have hW_le : W ≤ J := le_sup_right
  have hU_range : U ≤ J.subtype.range := by simpa only [Subgroup.range_subtype] using hU_le
  have hW_range : W ≤ J.subtype.range := by simpa only [Subgroup.range_subtype] using hW_le
  have hsup : U' ⊔ W' = ⊤ := by
    rw [show U' ⊔ W' = (U ⊔ W).comap J.subtype from
      Subgroup.comap_sup_eq_of_le_range J.subtype hU_range hW_range]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_top, iff_true]
    exact x.2
  have hU' (u : U') : IsNilpotent (rhoJ u - 1) := by
    exact hU ⟨u, u.2⟩
  have hW' (w : W') : IsNilpotent (rhoJ w - 1) := by
    exact hW ⟨w, w.2⟩
  let gJ : J := ⟨g, hg⟩
  exact rhoJ.isNilpotent_sub_one_of_normal_isUnipotent U' W' hsup hU' hW' gJ

end

end TauCeti
