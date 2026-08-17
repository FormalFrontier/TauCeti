/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent

/-!
# Common fixed vectors for commuting unipotent automorphisms

A unipotent automorphism has only the eigenvalue one.  Consequently, the joint eigenvector of a
commuting family of unipotent automorphisms is fixed by every member of the family.  We record both
the resulting common fixed vector and the one-dimensional fixed submodule that it spans.

For a representation of a commutative group, commutativity of the image is automatic.  The final
two results therefore give the fixed-vector and fixed-line forms used as the abelian base case in
the fixed-line induction for the Lie--Kolchin theorem.

## Main declarations

* `TauCeti.GeneralLinearGroup.IsUnipotent.eigenvalue_eq_one`: every eigenvalue of a unipotent
  automorphism is one.
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

namespace GeneralLinearGroup

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

/-- The maximal generalized eigenspace for the eigenvalue one of a unipotent automorphism is the
whole space. -/
theorem IsUnipotent.maxGenEigenspace_one_eq_top {g : GeneralLinearGroup K V}
    (hg : IsUnipotent g) :
    Module.End.maxGenEigenspace (g : Module.End K V) 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Module.End.mem_maxGenEigenspace]
  rw [isUnipotent_def] at hg
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  simpa using LinearMap.congr_fun hn x

/-- The generalized eigenspaces of a unipotent automorphism span the whole space.  This is the
triangularizability hypothesis needed by the joint-eigenvector existence theorem. -/
theorem IsUnipotent.iSup_maxGenEigenspace_eq_top {g : GeneralLinearGroup K V}
    (hg : IsUnipotent g) :
    ⨆ μ, Module.End.maxGenEigenspace (g : Module.End K V) μ = ⊤ := by
  apply top_unique
  rw [← hg.maxGenEigenspace_one_eq_top]
  exact le_iSup (fun μ ↦ Module.End.maxGenEigenspace (g : Module.End K V) μ) 1

/-- Every eigenvalue of a unipotent automorphism is one. -/
theorem IsUnipotent.eigenvalue_eq_one {g : GeneralLinearGroup K V} (hg : IsUnipotent g)
    {v : V} (hv : v ≠ 0) {μ : K} (heigen : (g : Module.End K V) v = μ • v) :
    μ = 1 := by
  have hpow_apply (m : ℕ) : (((g : Module.End K V) - 1) ^ m) v = (μ - 1) ^ m • v := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hsub : μ • v - v = (μ - 1) • v := by rw [sub_smul, one_smul]
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply,
          Module.End.one_apply, heigen, hsub, smul_smul, pow_succ]
  rw [isUnipotent_def] at hg
  obtain ⟨n, hn⟩ := hg
  have hzero : (μ - 1) ^ n • v = 0 := by
    rw [← hpow_apply n, hn]
    rfl
  have hpow : (μ - 1) ^ n = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hv
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)

end GeneralLinearGroup

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
  have htri (i : ι) : ⨆ μ, (fEnd i).maxGenEigenspace μ = ⊤ :=
    (hunipotent i).iSup_maxGenEigenspace_eq_top
  obtain ⟨χ, v, hv, heigen⟩ :=
    exists_jointEigenvector_of_pairwise_commute fEnd hcommEnd htri
  refine ⟨v, hv, fun i ↦ ?_⟩
  have hχ : χ i = 1 :=
    (hunipotent i).eigenvalue_eq_one hv (Module.End.mem_eigenspace_iff.mp (heigen i))
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
  change ρ g * ρ h = ρ h * ρ g
  rw [← map_mul, mul_comm g h, map_mul]

/-- A unipotent representation of a commutative group on a nonzero finite-dimensional vector space
fixes a one-dimensional submodule pointwise. -/
theorem exists_fixedLine_of_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* GeneralLinearGroup K V)
    (hunipotent : ∀ g, GeneralLinearGroup.IsUnipotent (ρ g)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧
      ∀ g, ∀ x ∈ p, (ρ g : Module.End K V) x = x := by
  apply exists_fixedLine_of_pairwise_commute_of_isUnipotent ρ _ hunipotent
  intro g h _
  change ρ g * ρ h = ρ h * ρ g
  rw [← map_mul, mul_comm g h, map_mul]

end

end TauCeti
