/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Solvability of faithful unipotent representations

Kolchin's common fixed-vector theorem constructs a complete invariant flag for a
finite-dimensional representation whose every operator is unipotent. Relative to a basis adapted
to this flag, every representing matrix is upper unitriangular. Consequently a group admitting a
faithful representation of this kind embeds in an upper-unitriangular matrix group and is
solvable.

## Main declarations

* `Representation.exists_basis_isUpperUnitriangular_of_isUnipotent`: simultaneous
  upper-unitriangularization of a unipotent monoid representation.
* `Representation.isSolvable_of_injective_of_isUnipotent`: a group with a faithful
  finite-dimensional unipotent representation is solvable.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the Lie--Kolchin solvability step in Layer 5 of the ReductiveGroups roadmap.
-/

public section

open Module

namespace TauCeti.Representation

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

section Monoid

variable [Monoid G]

/-- Extend bases of a submodule and its quotient to a basis of the ambient module. -/
private def extensionBasis {m n : ℕ} (p : Submodule K V)
    (bp : Basis (Fin m) K p) (bq : Basis (Fin n) K (V ⧸ p)) :
    Basis (Fin (m + n)) K V :=
  (bp.sumQuot bq).reindex finSumFinEquiv

@[simp]
private theorem extensionBasis_castAdd {m n : ℕ} (p : Submodule K V)
    (bp : Basis (Fin m) K p) (bq : Basis (Fin n) K (V ⧸ p)) (i : Fin m) :
    extensionBasis p bp bq (Fin.castAdd n i) = bp i := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_inl]

@[simp]
private theorem extensionBasis_natAdd_mkQ {m n : ℕ} (p : Submodule K V)
    (bp : Basis (Fin m) K p) (bq : Basis (Fin n) K (V ⧸ p)) (j : Fin n) :
    Submodule.Quotient.mk (extensionBasis p bp bq (Fin.natAdd m j)) = bq j := by
  rw [extensionBasis, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_inr]

@[simp]
private theorem extensionBasis_repr_castAdd {m n : ℕ} (p : Submodule K V)
    (bp : Basis (Fin m) K p) (bq : Basis (Fin n) K (V ⧸ p)) (x : p) (i : Fin m) :
    (extensionBasis p bp bq).repr x (Fin.castAdd n i) = bp.repr x i := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Basis.sumQuot_repr_inl]

@[simp]
private theorem extensionBasis_repr_natAdd {m n : ℕ} (p : Submodule K V)
    (bp : Basis (Fin m) K p) (bq : Basis (Fin n) K (V ⧸ p)) (x : V) (j : Fin n) :
    (extensionBasis p bp bq).repr x (Fin.natAdd m j) = bq.repr (p.mkQ x) j := by
  rw [extensionBasis, Basis.repr_reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Basis.sumQuot_repr_inr]

/-- A finite-dimensional monoid representation by unipotent operators has a basis in which all
representing matrices are upper unitriangular. -/
theorem _root_.Representation.exists_basis_isUpperUnitriangular_of_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (hunipotent : ∀ g, IsNilpotent (rho g - 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n) K V),
      ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular := by
  generalize hdim : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      by_cases hV : Nontrivial V
      · let _ : Nontrivial V := hV
        obtain ⟨p, hpdim, hfixed⟩ :=
          rho.exists_fixed_submodule_finrank_eq_one_of_isUnipotent hunipotent
        have hp (g : G) : p ≤ p.comap (rho g) := by
          intro x hx
          -- Membership in the comap unfolds to membership of the image in `p`.
          change rho g x ∈ p
          rw [hfixed g x hx]
          exact hx
        let q : Representation K G (V ⧸ p) := rho.quotient p hp
        have q_apply (g : G) (x : V) : q g (p.mkQ x) = p.mkQ (rho g x) := by
          simp [q, Representation.quotient_apply, Submodule.mapQ_apply]
        have hq (g : G) : IsNilpotent (q g - 1) := by
          have hsub : p ≤ p.comap (rho g - 1) := by
            intro x hx
            -- After unfolding the comap and subtraction of endomorphisms, this is invariance.
            change rho g x - x ∈ p
            exact p.sub_mem (hp g hx) hx
          have hnil := Module.End.IsNilpotent.mapQ hsub (hunipotent g)
          have heq : q g - 1 = p.mapQ p (rho g - 1) hsub := by
            ext x
            simp [q, Representation.quotient_apply, Submodule.mapQ_apply]
          rw [heq]
          exact hnil
        have hqdim : finrank K (V ⧸ p) < d := by
          have hsum := Module.finrank_quotient_add_finrank_le p
          rw [hpdim, hdim] at hsum
          omega
        obtain ⟨n, bq, hbq⟩ := ih (finrank K (V ⧸ p)) hqdim q hq rfl
        let bp : Basis (Fin 1) K p := finBasisOfFinrankEq K p hpdim
        let b := extensionBasis p bp bq
        refine ⟨1 + n, b, fun g ↦ ?_⟩
        rw [Matrix.isUpperUnitriangular_def]
        constructor
        -- The extension basis lists the fixed line `p` before a lift of the quotient basis.
        -- We check the four resulting matrix blocks: the first two index configurations are
        -- impossible below the diagonal, the lower-left block vanishes by invariance of `p`,
        -- and the lower-right block is upper triangular by the induction hypothesis on `V ⧸ p`.
        · intro i j hji
          obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
          obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
          cases i with
          | inl i =>
              cases j with
              | inl j =>
                  -- The fixed-line block is `1 × 1`, so it has no entry below the diagonal.
                  simp only [finSumFinEquiv_apply_left] at hji
                  have := (Fin.strictMono_castAdd n).lt_iff_lt.mp hji
                  omega
              | inr j =>
                  -- A quotient column follows every fixed-line row in the extension basis.
                  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hji
                  -- The order on `Fin (1 + n)` unfolds to the displayed inequality of values.
                  change 1 + j.val < i.val at hji
                  omega
          | inr i =>
              cases j with
              | inl j =>
                  -- The lower-left block is zero because every operator preserves `p`.
                  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
                    LinearMap.toMatrixAlgEquiv_apply]
                  have hmem : rho g (bp j : V) ∈ p := hp g (bp j).2
                  rw [extensionBasis_castAdd,
                    extensionBasis_repr_natAdd p bp bq (rho g (bp j : V)) i]
                  simp only [Submodule.mkQ_apply,
                    (Submodule.Quotient.mk_eq_zero p).mpr hmem, map_zero,
                    Finsupp.zero_apply]
              | inr j =>
                  -- The lower-right block represents the induced action on `V ⧸ p`.
                  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
                    LinearMap.toMatrixAlgEquiv_apply,
                    extensionBasis_repr_natAdd]
                  rw [← q_apply]
                  rw [Submodule.mkQ_apply, extensionBasis_natAdd_mkQ]
                  simpa only [LinearMap.toMatrixAlgEquiv_apply] using
                    (hbq g |>.isUpperTriangular
                      ((Fin.strictMono_natAdd 1).lt_iff_lt.mp hji))
        -- On the diagonal, the fixed-line block is the identity by construction and the
        -- quotient block has diagonal entries one by the induction hypothesis.
        · intro i
          obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
          cases i with
          | inl i =>
              rw [finSumFinEquiv_apply_left, LinearMap.toMatrixAlgEquiv_apply,
                extensionBasis_castAdd]
              have hfix : rho g (bp i : V) = bp i := hfixed g (bp i) (bp i).2
              rw [hfix, extensionBasis_repr_castAdd]
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

end Monoid

variable [Group G]

/-- Embed a representation into an upper-unitriangular group using a basis in which all of its
operators are upper unitriangular. -/
private def _root_.Representation.toUpperUnitriangularGroup {n : ℕ}
    (rho : Representation K G V)
    (b : Basis (Fin n) K V)
    (h : ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular) :
    G →* TauCeti.upperUnitriangularGroup (Fin n) K := by
  let f : G →* Matrix.GeneralLinearGroup (Fin n) K :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp rho.asGroupHom
  exact
    { toFun := fun g ↦ ⟨f g, by
        apply TauCeti.UpperUnitriangularGroup.mem_iff.mpr
        simp only [f, MonoidHom.comp_apply, Units.coe_map,
          Representation.asGroupHom_apply]
        rw [Matrix.isUpperUnitriangular_def]
        refine ⟨?_, h g |>.apply_diag⟩
        intro i j hji
        apply (h g).isUpperTriangular
        -- The inherited order on `Fin n` is definitionally the order on its values.
        change j.val < i.val at hji ⊢
        exact hji⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun g h ↦ Subtype.ext (map_mul f g h) }

/-- A group admitting a faithful finite-dimensional representation by unipotent operators is
solvable. -/
theorem _root_.Representation.isSolvable_of_injective_of_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (hinjective : Function.Injective rho.asGroupHom)
    (hunipotent : ∀ g, IsNilpotent (rho g - 1)) : Group.IsSolvable G := by
  obtain ⟨n, b, hb⟩ :=
    _root_.Representation.exists_basis_isUpperUnitriangular_of_isUnipotent rho hunipotent
  apply Group.isSolvable_of_isSolvable_injective
    (f := _root_.Representation.toUpperUnitriangularGroup rho b hb)
  intro g h hgh
  apply hinjective
  apply Units.ext
  apply (LinearMap.toMatrixAlgEquiv b).injective
  exact congrArg (fun x : TauCeti.upperUnitriangularGroup (Fin n) K ↦
    ((x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) hgh

end

end TauCeti.Representation
