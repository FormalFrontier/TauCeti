/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Extension
public import TauCeti.Algebra.Coalgebra.Comodule.WeightVector

/-!
# Building upper-triangular bases from weight vectors

Suppose every nonzero finite-dimensional comodule over a coalgebra has a nonzero weight vector
with weight drawn from a prescribed set `S`, that is, a vector `v` with coaction `v ↦ v ⊗ c` for
some `c ∈ S`. Repeatedly choose such a vector and pass to the quotient by its span. Induction on
dimension, together with the extension basis from
`TauCeti.Algebra.Coalgebra.Comodule.Flag.Extension`, gives a basis whose coefficient matrix is
upper triangular with diagonal entries in `S`.

This is the formal induction step behind both Kolchin arguments in Layer 5 of the ReductiveGroups
roadmap. Taking `S = {1}` recovers the unitriangular statement used for unipotent groups, where
Kolchin's theorem supplies genuine fixed vectors; taking `S` to be the set of group-like elements
gives the triangular statement Lie--Kolchin needs for solvable groups, where only eigenvectors are
available and group-like elements survive on the diagonal. When `C` is the coordinate Hopf algebra
of an affine group, these group-like elements are its diagonal characters.

## Main declarations

* `TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperTriangular_diag_mem_of_weight_vectors`:
  the induction, with the weights confined to a prescribed set.
* `TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors`: its
  group-like specialization, with group-like diagonal coefficients.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 6.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open Module

universe u v w

noncomputable section

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- The span of a weight vector, bundled as a subcomodule. -/
private def weightSpan (v : M) (c : C)
    (hv : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) :
    Subcomodule k C M :=
  Subcomodule.ofSubmodule (k ∙ v) fun m hm ↦ by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨a • ((⟨v, Submodule.mem_span_singleton_self v⟩ : k ∙ v) ⊗ₜ[k] c), ?_⟩
    simp only [map_smul, TensorProduct.map_tmul, Submodule.coe_subtype,
      LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', hv]

/-- The carrier module of `weightSpan` is the span used to construct it. -/
private theorem weightSpan_toSubmodule (v : M) (c : C)
    (hv : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) :
    (weightSpan v c hv).toSubmodule = k ∙ v :=
  rfl

/-- A bundled subcomodule has the same dimension as its underlying submodule. -/
private theorem finrank_toSubmodule (N : Subcomodule k C M) :
    finrank k N.toSubmodule = finrank k N :=
  rfl

/-- Every vector in the subcomodule spanned by a weight vector has the same weight. -/
private theorem weightSpan_coact [Module.Flat k C] (v : M) (c : C)
    (hv : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) (x : weightSpan v c hv) :
    coact (R := k) (C := C) (M := weightSpan v c hv) x = x ⊗ₜ[k] c := by
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (SMulMemClass.subtype (weightSpan v c hv)) Subtype.val_injective
  rw [Subcomodule.subtype_rTensor_coact]
  -- After applying the subtype tensor map, expose the ambient vectors on both sides.
  change coact (R := k) (C := C) (M := M) (x : M) = (x : M) ⊗ₜ[k] c
  exact coact_eq_tmul_of_mem_span hv x.2

/-- The subcomodule spanned by a nonzero weight vector has dimension one. -/
private theorem weightSpan_finrank (v : M) (c : C)
    (hv : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) (hv₀ : v ≠ 0) :
    finrank k (weightSpan v c hv) = 1 := by
  rw [← finrank_toSubmodule, weightSpan_toSubmodule]
  exact finrank_span_singleton hv₀

/-- If every nonzero finite-dimensional `C`-comodule has a nonzero weight vector whose weight lies
in `S`, then every finite-dimensional `C`-comodule has a basis whose coefficient matrix is upper
triangular with diagonal entries in `S`.

The hypothesis is deliberately uniform in the comodule: the induction applies it to successive
quotients. The conclusion allows an arbitrary finite index `n`; the exhibited basis itself
certifies that `n` is the dimension of `M`. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_diag_mem_of_weight_vectors
    (S : Set C) [FiniteDimensional k M]
    (hweight : ∀ (V : Type w) [AddCommGroup V] [Module k V] [Comodule k C V]
      [FiniteDimensional k V] [Nontrivial V],
      ∃ (v : V) (c : C), v ≠ 0 ∧ c ∈ S ∧
        coact (R := k) (C := C) (M := V) v = v ⊗ₜ[k] c) :
    ∃ (n : ℕ) (b : Basis (Fin n) k M),
      (coefficientMatrix (C := C) b).IsUpperTriangular ∧
        ∀ i, coefficientMatrix (C := C) b i i ∈ S := by
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  generalize hdim : finrank k M = d
  induction d using Nat.strong_induction_on generalizing M with
  | h d ih =>
      by_cases hM : Nontrivial M
      · let _ : Nontrivial M := hM
        obtain ⟨v, c, hv, hc, hvcoact⟩ := hweight M
        let L : Subcomodule k C M := weightSpan v c hvcoact
        let _ : AddCommGroup L := Module.addCommMonoidToAddCommGroup k
        have hLfinrank : finrank k L = 1 := weightSpan_finrank v c hvcoact hv
        let vL : L := ⟨v, Submodule.mem_span_singleton_self v⟩
        have hvL : vL ≠ 0 := fun h ↦ hv (congrArg Subtype.val h)
        let bL : Basis (Fin 1) k L :=
          FiniteDimensional.basisSingleton (Fin 1) hLfinrank vL hvL
        have hbL_weight (i : Fin 1) :
            coact (R := k) (C := C) (M := L) (bL i) = bL i ⊗ₜ[k] c :=
          weightSpan_coact v c hvcoact (bL i)
        have hbL : (coefficientMatrix (C := C) bL).IsUpperTriangular ∧
            ∀ i, coefficientMatrix (C := C) bL i i = c := by
          rw [coefficientMatrix_isUpperTriangular_and_diag_iff bL fun _ ↦ c]
          intro i
          rw [hbL_weight i]
          simp
        let Q := M ⧸ L.toSubmodule
        have hQdim : finrank k Q < d := by
          -- Unfold the local quotient abbreviation so the generic finrank bound applies.
          change finrank k (M ⧸ L.toSubmodule) < d
          have hsum := Module.finrank_quotient_add_finrank_le L.toSubmodule
          have hLto : finrank k L.toSubmodule = 1 :=
            (finrank_toSubmodule L).trans hLfinrank
          rw [hLto, hdim] at hsum
          omega
        obtain ⟨n, bQ, hbQtri, hbQdiag⟩ := ih (finrank k Q) hQdim (M := Q) rfl
        refine ⟨1 + n, extensionBasis L bL bQ,
          coefficientMatrix_extensionBasis_isUpperTriangular L bL bQ hbL.1 hbQtri, ?_⟩
        intro i
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        cases i with
        | inl i =>
            rw [finSumFinEquiv_apply_left, coefficientMatrix_extensionBasis_castAdd_castAdd,
              hbL.2 i]
            exact hc
        | inr i =>
            rw [finSumFinEquiv_apply_right, coefficientMatrix_extensionBasis_natAdd_natAdd]
            exact hbQdiag i
      · let _ : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
        have hzero : finrank k M = 0 := Module.finrank_zero_of_subsingleton
        let b : Basis (Fin 0) k M := finBasisOfFinrankEq k M hzero
        exact ⟨0, b, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

/-- If every nonzero finite-dimensional `C`-comodule has a nonzero weight vector, then every
finite-dimensional `C`-comodule has a basis whose coefficient matrix is upper triangular with
group-like diagonal entries. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
    [FiniteDimensional k M]
    (hweight : ∀ (V : Type w) [AddCommGroup V] [Module k V] [Comodule k C V]
      [FiniteDimensional k V] [Nontrivial V], HasNonzeroWeightVector k C V) :
    ∃ (n : ℕ) (b : Basis (Fin n) k M),
      (coefficientMatrix (C := C) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := C) b i i) := by
  exact exists_basis_coefficientMatrix_isUpperTriangular_diag_mem_of_weight_vectors
    {c : C | IsGroupLikeElem k c} fun V _ _ _ _ _ ↦ by
        obtain ⟨v, c, hv, hc, hvcoact⟩ :=
          (hasNonzeroWeightVector_iff (k := k) (C := C)).mp (hweight V)
        exact ⟨v, c, hv, hc, hvcoact⟩

end

end TauCeti.Comodule
