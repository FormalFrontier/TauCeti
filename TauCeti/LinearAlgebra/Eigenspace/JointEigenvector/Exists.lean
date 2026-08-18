/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Existence of joint eigenvectors for commuting endomorphisms

Every commuting family of triangularizable endomorphisms of a nonzero finite-dimensional vector
space has a joint eigenvector.  The proof is by induction on the dimension: either every
endomorphism is scalar, or the eigenspace of a nonscalar member is a nonzero proper subspace
preserved by the whole family.  Over an algebraically closed field, the triangularizability
hypothesis is automatic.

For a group representation with commuting, triangularizable image, such a joint eigenvector
exists.  The general `unitHomOfJointEigenvector` construction from `JointEigenvector/Basic.lean`
packages its eigenvalue function as a unit-valued character.  Thus every such representation has
a one-dimensional submodule on which the group acts through that character.  Over an algebraically
closed field, triangularizability is automatic.  This is the abelian base step for the fixed-line
induction in the Lie--Kolchin theorem.

## Main declarations

* `TauCeti.exists_jointEigenvector_of_pairwise_commute`: a commuting triangularizable family has
  a joint eigenvector.
* `TauCeti.exists_iInf_eigenspace_ne_bot_of_pairwise_commute`: the same result in the joint
  eigenspace API.
* `TauCeti.exists_unitHom_jointEigenvector_of_pairwise_commute`: a group representation with
  commuting, triangularizable image has a joint eigenvector whose eigenvalues form a unit-valued
  character.
* `TauCeti.exists_unitHom_submodule_finrank_eq_one_of_pairwise_commute`: the resulting
  one-dimensional submodule, together with the character through which the group acts on it.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti

open Set

universe u v w

noncomputable section

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A pairwise-commuting family of triangularizable endomorphisms of a nonzero finite-dimensional
vector space has a joint eigenvector. -/
theorem exists_jointEigenvector_of_pairwise_commute [FiniteDimensional K V] [Nontrivial V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (htri : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, v ∈ (f i).eigenspace (χ i) := by
  generalize hdim : Module.finrank K V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      classical
      by_cases hscalar : ∀ i, ∃ μ : K, f i = μ • (1 : Module.End K V)
      · choose χ hχ using hscalar
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine ⟨χ, v, hv, fun i ↦ Module.End.mem_eigenspace_iff.mpr ?_⟩
        rw [hχ i]
        simp
      · push Not at hscalar
        obtain ⟨i, hi⟩ := hscalar
        obtain ⟨μ, hμ⟩ := Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top ⊤ (htri i)
        let p : Submodule K V := (f i).eigenspace μ
        have hp_ne_bot : p ≠ ⊥ := hμ
        have hp_ne_top : p ≠ ⊤ := by
          intro hp
          apply hi μ
          ext x
          have hx : x ∈ p := by rw [hp]; exact Submodule.mem_top
          simpa using Module.End.mem_eigenspace_iff.mp hx
        have hp (j : ι) : MapsTo (f j) p p := by
          apply (f i).mapsTo_genEigenspace_of_comm (g := f j) _ μ 1
          rcases eq_or_ne i j with rfl | hij
          · exact Commute.refl _
          · exact hcomm hij
        let f' : ι → Module.End K p := fun j ↦ (f j).restrict (hp j)
        have hcomm' : Pairwise fun j l ↦ Commute (f' j) (f' l) := by
          intro j l hjl
          exact LinearMap.restrict_commute (hcomm hjl) (hp j) (hp l)
        have htri' (j : ι) : ⨆ μ, (f' j).maxGenEigenspace μ = ⊤ :=
          Module.End.genEigenspace_restrict_eq_top (hp j) (htri j)
        have hp_finrank : Module.finrank K p < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hp_ne_top
        let _ : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp_ne_bot
        obtain ⟨χ, v, hv, hv_mem⟩ :=
          ih (Module.finrank K p) hp_finrank f' hcomm' htri' rfl
        refine ⟨χ, v, Submodule.coe_eq_zero.not.mpr hv, fun j ↦ ?_⟩
        apply (f j).eigenspace_restrict_le_eigenspace (hp j) (χ j)
        exact ⟨v, by simpa [f'] using hv_mem j, rfl⟩

/-- Over an algebraically closed field, every pairwise-commuting family of endomorphisms of a
nonzero finite-dimensional vector space has a joint eigenvector. -/
theorem exists_jointEigenvector_of_pairwise_commute_of_isAlgClosed [IsAlgClosed K]
    [FiniteDimensional K V] [Nontrivial V] (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, v ∈ (f i).eigenspace (χ i) :=
  exists_jointEigenvector_of_pairwise_commute f hcomm fun i ↦
    Module.End.iSup_maxGenEigenspace_eq_top (f i)

/-- A pairwise-commuting family of triangularizable endomorphisms has a nonzero joint
eigenspace. -/
theorem exists_iInf_eigenspace_ne_bot_of_pairwise_commute [FiniteDimensional K V] [Nontrivial V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (htri : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ∃ χ : ι → K, (⨅ i, (f i).eigenspace (χ i)) ≠ ⊥ := by
  obtain ⟨χ, v, hv, hv_mem⟩ := exists_jointEigenvector_of_pairwise_commute f hcomm htri
  exact ⟨χ, (Submodule.ne_bot_iff _).mpr ⟨v, (Submodule.mem_iInf _).mpr hv_mem, hv⟩⟩

/-- Over an algebraically closed field, a pairwise-commuting family of endomorphisms has a
nonzero joint eigenspace. -/
theorem exists_iInf_eigenspace_ne_bot_of_pairwise_commute_of_isAlgClosed [IsAlgClosed K]
    [FiniteDimensional K V] [Nontrivial V] (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) :
    ∃ χ : ι → K, (⨅ i, (f i).eigenspace (χ i)) ≠ ⊥ :=
  exists_iInf_eigenspace_ne_bot_of_pairwise_commute f hcomm fun i ↦
    Module.End.iSup_maxGenEigenspace_eq_top (f i)

variable {G : Type w} [Group G]

/-- Every nonzero finite-dimensional representation with pairwise-commuting triangularizable
image has a joint eigenvector, and its eigenvalues form a unit-valued character. -/
theorem exists_unitHom_jointEigenvector_of_pairwise_commute [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* Module.End K V) (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h))
    (htri : ∀ g, ⨆ μ, (ρ g).maxGenEigenspace μ = ⊤) :
    ∃ (χ : G →* Kˣ) (v : V), v ≠ 0 ∧ ∀ g, ρ g v = (χ g : K) • v := by
  obtain ⟨χ, v, hv, hv_mem⟩ :=
    exists_jointEigenvector_of_pairwise_commute (fun g ↦ ρ g) hcomm htri
  let χ' : G →* Kˣ :=
    unitHomOfJointEigenvector ρ χ v hv hv_mem
  refine ⟨χ', v, hv, fun g ↦ ?_⟩
  rw [unitHomOfJointEigenvector_apply]
  exact Module.End.mem_eigenspace_iff.mp (hv_mem g)

/-- Over an algebraically closed field, every nonzero finite-dimensional representation with
pairwise-commuting image has a joint eigenvector whose eigenvalues form a unit-valued character. -/
theorem exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed [IsAlgClosed K]
    [FiniteDimensional K V] [Nontrivial V] (ρ : G →* Module.End K V)
    (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h)) :
    ∃ (χ : G →* Kˣ) (v : V), v ≠ 0 ∧ ∀ g, ρ g v = (χ g : K) • v :=
  exists_unitHom_jointEigenvector_of_pairwise_commute ρ hcomm fun g ↦
    Module.End.iSup_maxGenEigenspace_eq_top (ρ g)

/-- A group representation with pairwise-commuting triangularizable image has a nonzero joint
eigenspace indexed by a unit-valued character. -/
theorem exists_unitHom_iInf_eigenspace_ne_bot_of_pairwise_commute [FiniteDimensional K V]
    [Nontrivial V] (ρ : G →* Module.End K V)
    (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h))
    (htri : ∀ g, ⨆ μ, (ρ g).maxGenEigenspace μ = ⊤) :
    ∃ χ : G →* Kˣ, (⨅ g, (ρ g).eigenspace (χ g)) ≠ ⊥ := by
  obtain ⟨χ, v, hv, heigen⟩ :=
    exists_unitHom_jointEigenvector_of_pairwise_commute ρ hcomm htri
  refine ⟨χ, (Submodule.ne_bot_iff _).mpr ⟨v, (Submodule.mem_iInf _).mpr fun g ↦ ?_, hv⟩⟩
  exact Module.End.mem_eigenspace_iff.mpr (heigen g)

/-- Over an algebraically closed field, a group representation with pairwise-commuting image has a
nonzero joint eigenspace indexed by a unit-valued character. -/
theorem exists_unitHom_iInf_eigenspace_ne_bot_of_pairwise_commute_of_isAlgClosed [IsAlgClosed K]
    [FiniteDimensional K V] [Nontrivial V] (ρ : G →* Module.End K V)
    (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h)) :
    ∃ χ : G →* Kˣ, (⨅ g, (ρ g).eigenspace (χ g)) ≠ ⊥ :=
  exists_unitHom_iInf_eigenspace_ne_bot_of_pairwise_commute ρ hcomm fun g ↦
    Module.End.iSup_maxGenEigenspace_eq_top (ρ g)

/-- For a group representation with pairwise-commuting triangularizable image, there is a
one-dimensional submodule and a unit-valued character through which the group acts on it. -/
theorem exists_unitHom_submodule_finrank_eq_one_of_pairwise_commute [FiniteDimensional K V]
    [Nontrivial V] (ρ : G →* Module.End K V)
    (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h))
    (htri : ∀ g, ⨆ μ, (ρ g).maxGenEigenspace μ = ⊤) :
    ∃ (χ : G →* Kˣ) (p : Submodule K V), Module.finrank K p = 1 ∧
      ∀ g, ∀ x ∈ p, ρ g x = (χ g : K) • x := by
  obtain ⟨χ, v, hv, heigen⟩ :=
    exists_unitHom_jointEigenvector_of_pairwise_commute ρ hcomm htri
  refine ⟨χ, K ∙ v, finrank_span_singleton hv, fun g x hx ↦ ?_⟩
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp only [map_smul, heigen, smul_smul, mul_comm]

/-- Over an algebraically closed field, a group representation with pairwise-commuting image has a
one-dimensional submodule and a unit-valued character through which the group acts on it. -/
theorem exists_unitHom_submodule_finrank_eq_one_of_pairwise_commute_of_isAlgClosed
    [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (ρ : G →* Module.End K V)
    (hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h)) :
    ∃ (χ : G →* Kˣ) (p : Submodule K V), Module.finrank K p = 1 ∧
      ∀ g, ∀ x ∈ p, ρ g x = (χ g : K) • x :=
  exists_unitHom_submodule_finrank_eq_one_of_pairwise_commute ρ hcomm fun g ↦
    Module.End.iSup_maxGenEigenspace_eq_top (ρ g)

end

end TauCeti
