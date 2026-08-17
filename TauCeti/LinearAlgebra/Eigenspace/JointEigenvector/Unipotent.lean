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

For a representation of a commutative group, commutativity of the image is automatic.  The final
two results therefore give the fixed-vector and fixed-line forms used as the abelian base case in
the fixed-line induction for the Lie--Kolchin theorem.

## Main declarations

* `TauCeti.exists_common_fixedVector_of_pairwise_commute_of_isUnipotent`: a commuting family of
  unipotent automorphisms of a nonzero finite-dimensional space has a common nonzero fixed vector.
* `TauCeti.exists_fixedLine_of_pairwise_commute_of_isUnipotent`: such a family fixes a
  one-dimensional submodule pointwise.
* `TauCeti.exists_fixedLine_of_isUnipotent`: a unipotent representation of a commutative group has
  a pointwise-fixed line.

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
theorem exists_common_fixedVector_of_pairwise_commute_of_isUnipotent
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
theorem exists_fixedLine_of_pairwise_commute_of_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (f : ι → GeneralLinearGroup K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hunipotent : ∀ i, GeneralLinearGroup.IsUnipotent (f i)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧
      ∀ i, ∀ x ∈ p, (f i : Module.End K V) x = x := by
  obtain ⟨v, hv, hfixed⟩ :=
    exists_common_fixedVector_of_pairwise_commute_of_isUnipotent f hcomm hunipotent
  refine ⟨K ∙ v, finrank_span_singleton hv, fun i x hx ↦ ?_⟩
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp [hfixed]

variable {G : Type w} [CommGroup G]

/-- A unipotent representation of a commutative group on a nonzero finite-dimensional vector space
has a common nonzero fixed vector. -/
theorem exists_common_fixedVector_of_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* GeneralLinearGroup K V)
    (hunipotent : ∀ g, GeneralLinearGroup.IsUnipotent (ρ g)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, (ρ g : Module.End K V) v = v := by
  apply exists_common_fixedVector_of_pairwise_commute_of_isUnipotent ρ _ hunipotent
  intro g h _
  exact (ρ.map_mul g h).symm.trans ((congrArg ρ (mul_comm g h)).trans (ρ.map_mul h g))

/-- A unipotent representation of a commutative group on a nonzero finite-dimensional vector space
fixes a one-dimensional submodule pointwise. -/
theorem exists_fixedLine_of_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* GeneralLinearGroup K V)
    (hunipotent : ∀ g, GeneralLinearGroup.IsUnipotent (ρ g)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧
      ∀ g, ∀ x ∈ p, (ρ g : Module.End K V) x = x := by
  apply exists_fixedLine_of_pairwise_commute_of_isUnipotent ρ _ hunipotent
  intro g h _
  exact (ρ.map_mul g h).symm.trans ((congrArg ρ (mul_comm g h)).trans (ρ.map_mul h g))

end

end TauCeti
