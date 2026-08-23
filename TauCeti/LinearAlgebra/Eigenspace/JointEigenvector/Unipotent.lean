/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
public import TauCeti.LinearAlgebra.Eigenspace.Unipotent

/-!
# Common fixed vectors for commuting unipotent automorphisms

A unipotent automorphism has only the eigenvalue one.  Consequently, the joint eigenvector of a
commuting family of unipotent automorphisms is fixed by every member of the family.  We record both
the resulting common fixed vector and the one-dimensional fixed submodule that it spans.

## Main declarations

* `TauCeti.exists_common_fixed_vector_of_pairwise_commute_of_isUnipotent`: a commuting family of
  unipotent automorphisms of a nonzero finite-dimensional space has a common nonzero fixed vector.
* `TauCeti.exists_fixed_submodule_finrank_eq_one_of_pairwise_commute_of_isUnipotent`: such a family
  fixes a one-dimensional submodule pointwise.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti

open LinearMap

universe u v w

noncomputable section

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A pairwise-commuting family of unipotent automorphisms of a nonzero finite-dimensional vector
space has a common nonzero fixed vector. -/
theorem exists_common_fixed_vector_of_pairwise_commute_of_isUnipotent
    [FiniteDimensional K V] [Nontrivial V] (f : ι → GeneralLinearGroup K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hunipotent : ∀ i, GeneralLinearGroup.IsUnipotent (f i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, (f i : Module.End K V) v = v := by
  let fEnd : ι → Module.End K V := fun i ↦ f i
  have hcommEnd : Pairwise fun i j ↦ Commute (fEnd i) (fEnd j) := fun i j hij ↦
    (hcomm hij).units_val
  have htri (i : ι) : ⨆ μ, (fEnd i).maxGenEigenspace μ = ⊤ := by
    apply top_unique
    rw [← TauCeti.GeneralLinearGroup.IsUnipotent.maxGenEigenspace_one_eq_top (hunipotent i)]
    exact le_iSup (fun μ ↦ (fEnd i).maxGenEigenspace μ) 1
  obtain ⟨χ, v, hv, heigen⟩ :=
    exists_jointEigenvector_of_pairwise_commute fEnd hcommEnd htri
  refine ⟨v, hv, fun i ↦ ?_⟩
  have hχ : χ i = 1 :=
    TauCeti.GeneralLinearGroup.IsUnipotent.eigenvalue_eq_one (hunipotent i) hv
      (Module.End.mem_eigenspace_iff.mp (heigen i))
  simpa [fEnd, hχ] using Module.End.mem_eigenspace_iff.mp (heigen i)

/-- A pairwise-commuting family of unipotent automorphisms of a nonzero finite-dimensional vector
space fixes a one-dimensional submodule pointwise. -/
theorem exists_fixed_submodule_finrank_eq_one_of_pairwise_commute_of_isUnipotent
    [FiniteDimensional K V] [Nontrivial V]
    (f : ι → GeneralLinearGroup K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hunipotent : ∀ i, GeneralLinearGroup.IsUnipotent (f i)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧
      ∀ i, ∀ x ∈ p, (f i : Module.End K V) x = x := by
  apply exists_fixed_submodule_finrank_eq_one_of_exists_common_fixed_vector
    (fun i ↦ (f i : Module.End K V))
  exact exists_common_fixed_vector_of_pairwise_commute_of_isUnipotent f hcomm hunipotent

end

end TauCeti
