/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent

/-!
# Eigenspaces of unipotent automorphisms

A unipotent automorphism has maximal generalized `1`-eigenspace equal to the whole space and has
no eigenvalues other than one.

## Main declarations

* `TauCeti.GeneralLinearGroup.IsUnipotent.maxGenEigenspace_one_eq_top`: the maximal generalized
  `1`-eigenspace of a unipotent automorphism is the whole space.
* `TauCeti.GeneralLinearGroup.IsUnipotent.eigenvalue_eq_one`: every eigenvalue of a unipotent
  automorphism is one.

## References

* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti

open LinearMap

universe u v

noncomputable section

namespace GeneralLinearGroup

variable {K : Type u} {V : Type v}

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V]

/-- The maximal generalized eigenspace for the eigenvalue one of a unipotent automorphism is the
whole space. -/
@[simp]
theorem IsUnipotent.maxGenEigenspace_one_eq_top {g : GeneralLinearGroup K V}
    (hg : LinearMap.GeneralLinearGroup.IsUnipotent g) :
    Module.End.maxGenEigenspace (g : Module.End K V) 1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Module.End.mem_maxGenEigenspace]
  rw [LinearMap.GeneralLinearGroup.isUnipotent_def] at hg
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  simpa using LinearMap.congr_fun hn x

end CommRing

section Field

variable [Field K] [AddCommGroup V] [Module K V]

/-- Every eigenvalue of a unipotent automorphism is one. -/
theorem IsUnipotent.eigenvalue_eq_one {g : GeneralLinearGroup K V}
    (hg : LinearMap.GeneralLinearGroup.IsUnipotent g)
    {v : V} (hv : v ≠ 0) {μ : K} (heigen : (g : Module.End K V) v = μ • v) :
    μ = 1 := by
  rw [LinearMap.GeneralLinearGroup.isUnipotent_def] at hg
  have heigenvalue : Module.End.HasEigenvalue (g : Module.End K V) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr heigen, hv⟩
  have hsub : Module.End.HasEigenvalue ((g : Module.End K V) - 1) (μ - 1) := by
    have hshift : Module.End.HasEigenvalue (g : Module.End K V) ((μ - 1) + 1) := by
      simpa using heigenvalue
    simpa only [one_smul, Module.End.one_eq_id] using
      (Module.End.hasEigenvalue_sub_iff (f := (g : Module.End K V))
        (ρ := (1 : K)) (μ := μ - 1)).mpr hshift
  exact sub_eq_zero.mp (hsub.isNilpotent_of_isNilpotent hg).eq_zero

end Field

end GeneralLinearGroup

end

end TauCeti
