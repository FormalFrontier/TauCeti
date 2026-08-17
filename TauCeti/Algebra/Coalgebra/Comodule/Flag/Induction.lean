/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Extension

/-!
# Building upper-unitriangular bases from fixed vectors

Suppose every nonzero finite-dimensional comodule over a coalgebra with a distinguished element
`1` has a nonzero fixed vector, that is, a vector `v` with coaction `v ↦ v ⊗ 1`. Repeatedly choose
such a vector and pass to the quotient by its span. Induction on dimension, together with the
extension basis from `Comodule.Flag.Extension`, gives a basis whose coefficient matrix is upper
unitriangular.

This is the formal induction step common to the Kolchin arguments in Layer 5 of the
ReductiveGroups roadmap. Lie–Kolchin supplies eigenlines for solvable groups; for a unipotent
group every resulting character is trivial, so the lines are fixed. The theorem here turns that
fixed-vector statement into the complete flag needed to embed a faithful representation into an
upper-unitriangular group.

## Main declarations

* `TauCeti.Comodule.HasNonzeroFixedVector`: a comodule contains a nonzero vector with coaction
  `v ↦ v ⊗ 1`.
* `TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperUnitriangular_of_fixed_vectors`:
  if every nonzero finite-dimensional comodule has such a vector, every finite-dimensional
  comodule admits an upper-unitriangular basis.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open Module

universe u v w

noncomputable section

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H] [One H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- A comodule has a nonzero fixed vector if some nonzero `v` has coaction `v ⊗ 1`.

For the comodule corresponding to a group representation, this says that the represented group
fixes `v`. -/
def HasNonzeroFixedVector (k : Type u) (H : Type v) (M : Type w)
    [Field k] [AddCommGroup H] [Module k H] [Coalgebra k H] [One H]
    [AddCommGroup M] [Module k M] [Comodule k H M] : Prop :=
  ∃ v : M, v ≠ 0 ∧ coact (R := k) (C := H) (M := M) v = v ⊗ₜ[k] (1 : H)

/-- The defining characterization of a nonzero fixed vector. -/
@[simp]
theorem hasNonzeroFixedVector_iff :
    HasNonzeroFixedVector k H M ↔
      ∃ v : M, v ≠ 0 ∧ coact (R := k) (C := H) (M := M) v = v ⊗ₜ[k] (1 : H) :=
  Iff.rfl

/-- The span of a fixed vector, bundled as a subcomodule. -/
private def fixedSpan (v : M)
    (hv : coact (R := k) (C := H) (M := M) v = v ⊗ₜ[k] (1 : H)) :
    Subcomodule k H M :=
  Subcomodule.ofSubmodule (k ∙ v) fun m hm ↦ by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨a •
      ((⟨v, Submodule.mem_span_singleton_self v⟩ : k ∙ v) ⊗ₜ[k] (1 : H)), ?_⟩
    simp only [map_smul, TensorProduct.map_tmul, Submodule.coe_subtype,
      LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', hv]

/-- Every vector in the subcomodule spanned by a fixed vector is fixed. -/
private theorem fixedSpan_coact [Module.Flat k H] (v : M)
    (hv : coact (R := k) (C := H) (M := M) v = v ⊗ₜ[k] (1 : H))
    (x : fixedSpan v hv) :
    coact (R := k) (C := H) (M := fixedSpan v hv) x = x ⊗ₜ[k] (1 : H) := by
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (SMulMemClass.subtype (fixedSpan v hv)) Subtype.val_injective
  rw [Subcomodule.subtype_rTensor_coact]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  -- After applying the subtype tensor map, expose the ambient vectors on both sides.
  change coact (R := k) (C := H) (M := M) (x : M) = (x : M) ⊗ₜ[k] (1 : H)
  rw [← ha, map_smul, hv, TensorProduct.smul_tmul']

/-- A basis consisting of fixed vectors has identity coefficient matrix. -/
private theorem coefficientMatrix_eq_one_of_fixed_basis {n : ℕ} (b : Basis (Fin n) k M)
    (hb : ∀ i, coact (R := k) (C := H) (M := M) (b i) = b i ⊗ₜ[k] (1 : H)) :
    coefficientMatrix (C := H) b = 1 := by
  classical
  ext i j
  rw [coefficientMatrix_apply, matrixCoefficient_def, hb]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, TensorProduct.lid_tmul,
    Basis.coord_apply, Basis.repr_self_apply, Matrix.one_apply]
  simp [eq_comm]

/-- If every nonzero finite-dimensional `H`-comodule has a nonzero fixed vector, then every
finite-dimensional `H`-comodule has a basis with upper-unitriangular coefficient matrix.

The hypothesis is deliberately uniform in the comodule: the induction applies it to successive
quotients. The conclusion allows an arbitrary finite index `n`; the exhibited basis itself
certifies that `n` is the dimension of `M`. -/
theorem exists_basis_coefficientMatrix_isUpperUnitriangular_of_fixed_vectors
    [FiniteDimensional k M]
    (hfixed : ∀ (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], HasNonzeroFixedVector k H V) :
    ∃ (n : ℕ) (b : Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperUnitriangular := by
  generalize hdim : finrank k M = d
  induction d using Nat.strong_induction_on generalizing M with
  | h d ih =>
      by_cases hM : Nontrivial M
      · let _ : Nontrivial M := hM
        let _ : Module.Flat k H := Module.Flat.of_free
        obtain ⟨v, hv, hvcoact⟩ := (hasNonzeroFixedVector_iff (k := k) (H := H) (M := M)).mp
          (hfixed M)
        let L : Subcomodule k H M := fixedSpan v hvcoact
        let _ : AddCommGroup L := Module.addCommMonoidToAddCommGroup k
        have hLfinrank : finrank k L = 1 := by
          -- The subtype `L` and the span used as its carrier have definitionally equal finranks.
          change finrank k (k ∙ v) = 1
          exact finrank_span_singleton hv
        let vL : L := ⟨v, Submodule.mem_span_singleton_self v⟩
        have hvL : vL ≠ 0 := by
          intro h
          exact hv (congrArg Subtype.val h)
        let bL : Basis (Fin 1) k L :=
          FiniteDimensional.basisSingleton (Fin 1) hLfinrank vL hvL
        have hbL_fixed (i : Fin 1) :
            coact (R := k) (C := H) (M := L) (bL i) = bL i ⊗ₜ[k] (1 : H) :=
          fixedSpan_coact v hvcoact (bL i)
        have hbL : (coefficientMatrix (C := H) bL).IsUpperUnitriangular := by
          rw [coefficientMatrix_eq_one_of_fixed_basis bL hbL_fixed]
          exact Matrix.isUpperUnitriangular_one
        let Q := M ⧸ L.toSubmodule
        have hQdim : finrank k Q < d := by
          -- Unfold the local quotient abbreviation so the generic finrank bound applies.
          change finrank k (M ⧸ L.toSubmodule) < d
          have hsum := Module.finrank_quotient_add_finrank_le L.toSubmodule
          have hLto : finrank k L.toSubmodule = 1 := by
            -- The carrier of `L` is definitionally the span of the chosen fixed vector.
            change finrank k (k ∙ v) = 1
            exact finrank_span_singleton hv
          rw [hLto, hdim] at hsum
          omega
        obtain ⟨n, bQ, hbQ⟩ := ih (finrank k Q) hQdim (M := Q) rfl
        exact ⟨1 + n, extensionBasis L bL bQ,
          coefficientMatrix_extensionBasis_isUpperUnitriangular L bL bQ hbL hbQ⟩
      · let _ : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
        have hzero : finrank k M = 0 := Module.finrank_zero_of_subsingleton
        let b : Basis (Fin 0) k M := finBasisOfFinrankEq k M hzero
        refine ⟨0, b, ?_⟩
        rw [Matrix.isUpperUnitriangular_def]
        exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

end

end TauCeti.Comodule
