/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector

/-!
# Common eigenvectors of commuting endomorphisms

Over an algebraically closed field, every commuting family of endomorphisms of a nonzero
finite-dimensional vector space has a common eigenvector.  The proof is by induction on the
dimension: either every endomorphism is scalar, or the eigenspace of a nonscalar member is a
nonzero proper subspace preserved by the whole family.

For a representation of a commutative group, the common eigenvalues form a unit-valued
character.  Thus every nonzero finite-dimensional representation of a commutative group has an
invariant line.  This is the abelian base step for the fixed-line induction in the Lie--Kolchin
theorem.

## Main declarations

* `TauCeti.exists_common_eigenvector_of_pairwise_commute`: a commuting family over an
  algebraically closed field has a common eigenvector.
* `TauCeti.exists_character_eigenvector_of_commutative`: for a commutative group representation,
  the simultaneous eigenvalues form a character.
* `TauCeti.exists_invariant_line_of_commutative`: a nonzero finite-dimensional representation of
  a commutative group has an invariant one-dimensional subspace.

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
variable [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]

/-- A pairwise-commuting family of endomorphisms of a nonzero finite-dimensional vector space
over an algebraically closed field has a common eigenvector. -/
theorem exists_common_eigenvector_of_pairwise_commute [FiniteDimensional K V] [Nontrivial V]
    (f : ι → Module.End K V) (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) :
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
        obtain ⟨μ, hμ⟩ := (f i).exists_eigenvalue
        let p : Submodule K V := (f i).eigenspace μ
        have hp_ne_bot : p ≠ ⊥ := hμ
        have hp_ne_top : p ≠ ⊤ := by
          intro hp
          apply hi μ
          ext x
          have hx : x ∈ p := by rw [hp]; exact Submodule.mem_top
          exact Module.End.mem_eigenspace_iff.mp hx
        have hp (j : ι) : MapsTo (f j) p p := by
          apply (f i).mapsTo_genEigenspace_of_comm (g := f j) _ μ 1
          rcases eq_or_ne i j with rfl | hij
          · exact Commute.refl _
          · exact hcomm hij
        let f' : ι → Module.End K p := fun j ↦ (f j).restrict (hp j)
        have hcomm' : Pairwise fun j l ↦ Commute (f' j) (f' l) := by
          intro j l hjl
          exact LinearMap.restrict_commute (hcomm hjl) (hp j) (hp l)
        have hp_finrank : Module.finrank K p < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hp_ne_top
        let _ : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp_ne_bot
        obtain ⟨χ, v, hv, hv_mem⟩ := ih (Module.finrank K p) hp_finrank f' hcomm' rfl
        refine ⟨χ, v, Subtype.coe_ne_coe.mpr hv, fun j ↦ ?_⟩
        apply Module.End.mem_eigenspace_iff.mpr
        exact congrArg Subtype.val
          (Module.End.mem_eigenspace_iff.mp (hv_mem j))

variable {G : Type w} [CommGroup G]

/-- Every nonzero finite-dimensional representation of a commutative group over an algebraically
closed field has a common eigenvector, and its eigenvalues form a unit-valued character. -/
theorem exists_character_eigenvector_of_commutative [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* Module.End K V) :
    ∃ (χ : G →* Kˣ) (v : V), v ≠ 0 ∧ ∀ g, ρ g v = (χ g : K) • v := by
  have hcomm : Pairwise fun g h ↦ Commute (ρ g) (ρ h) := by
    intro g h _
    change ρ g * ρ h = ρ h * ρ g
    rw [← ρ.map_mul, mul_comm, ρ.map_mul]
  obtain ⟨χ, v, hv, hv_mem⟩ :=
    exists_common_eigenvector_of_pairwise_commute (fun g ↦ ρ g) hcomm
  let χ' : G →* Kˣ :=
    unitHomOfJointEigenvector ρ χ v hv hv_mem
  refine ⟨χ', v, hv, fun g ↦ ?_⟩
  rw [unitHomOfJointEigenvector_apply]
  exact Module.End.mem_eigenspace_iff.mp (hv_mem g)

/-- Every nonzero finite-dimensional representation of a commutative group over an algebraically
closed field preserves a one-dimensional subspace. -/
theorem exists_invariant_line_of_commutative [FiniteDimensional K V] [Nontrivial V]
    (ρ : G →* Module.End K V) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧ ∀ g, MapsTo (ρ g) p p := by
  obtain ⟨χ, v, hv, heigen⟩ := exists_character_eigenvector_of_commutative ρ
  refine ⟨K ∙ v, finrank_span_singleton hv, fun g x hx ↦ ?_⟩
  change x ∈ K ∙ v at hx
  change ρ g x ∈ K ∙ v
  rw [Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a * (χ g : K), by rw [map_smul, heigen, smul_smul, mul_comm]⟩

end

end TauCeti
