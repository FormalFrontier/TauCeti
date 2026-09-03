/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular

/-!
# Building upper-unitriangular bases from fixed vectors

Suppose every nonzero finite-dimensional comodule over a coalgebra with a distinguished element
`1` has a nonzero fixed vector, that is, a vector `v` with coaction `v ↦ v ⊗ 1`. Then every
finite-dimensional comodule has a basis whose coefficient matrix is upper unitriangular: this is
the weight-vector induction of `TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular` with the
weights confined to `{1}`.

This is the fixed-vector case of the induction common to the Kolchin arguments in Layer 5 of the
ReductiveGroups roadmap. Lie–Kolchin supplies eigenlines for solvable groups; for a unipotent
group every resulting character is trivial, so the lines are fixed. The theorem here turns that
fixed-vector statement into the complete flag needed to embed a faithful representation into an
upper-unitriangular group.

## Main declarations

* `TauCeti.Comodule.HasNonzeroFixedVector`: a comodule contains a nonzero vector with coaction
  `v ↦ v ⊗ 1`.
* `TauCeti.Comodule.hasNonzeroFixedVector_iff_fixedSubcomodule_ne_bot`: that happens exactly when
  the fixed subcomodule is nonzero.
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

/-- A comodule has a nonzero fixed vector exactly when its fixed subcomodule is nonzero. -/
theorem hasNonzeroFixedVector_iff_fixedSubcomodule_ne_bot :
    HasNonzeroFixedVector k H M ↔ fixedSubcomodule k H M ≠ ⊥ := by
  rw [hasNonzeroFixedVector_iff, Subcomodule.ne_bot_iff]
  exact ⟨fun ⟨v, hv, hvc⟩ ↦ ⟨v, mem_fixedSubcomodule.mpr hvc, hv⟩,
    fun ⟨v, hvm, hv⟩ ↦ ⟨v, hv, mem_fixedSubcomodule.mp hvm⟩⟩

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
  have hweight : ∀ (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V],
      ∃ (v : V) (c : H), v ≠ 0 ∧ c ∈ ({1} : Set H) ∧
        coact (R := k) (C := H) (M := V) v = v ⊗ₜ[k] c := by
    intro V _ _ _ _ _
    obtain ⟨v, hv, hvcoact⟩ :=
      (hasNonzeroFixedVector_iff (k := k) (H := H) (M := V)).mp (hfixed V)
    exact ⟨v, 1, hv, rfl, hvcoact⟩
  obtain ⟨n, b, htri, hdiag⟩ :=
    exists_basis_coefficientMatrix_isUpperTriangular_diag_mem_of_weight_vectors
      (M := M) ({1} : Set H) hweight
  exact ⟨n, b, (Matrix.isUpperUnitriangular_def _).mpr ⟨htri, fun i ↦ hdiag i⟩⟩

end

end TauCeti.Comodule
