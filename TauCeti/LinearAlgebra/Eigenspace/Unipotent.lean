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

/-- Every eigenvalue of a unipotent automorphism is one. -/
theorem IsUnipotent.eigenvalue_eq_one {g : GeneralLinearGroup K V} (hg : IsUnipotent g)
    {v : V} (hv : v ≠ 0) {μ : K} (heigen : (g : Module.End K V) v = μ • v) :
    μ = 1 := by
  have hpow_apply (m : ℕ) : (((g : Module.End K V) - 1) ^ m) v = (μ - 1) ^ m • v := by
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          (((g : Module.End K V) - 1) ^ m.succ) v =
              ((g : Module.End K V) - 1) ((μ - 1) ^ m • v) := by
            rw [pow_succ', Module.End.mul_apply, ih]
          _ = (μ - 1) ^ m • ((μ - 1) • v) := by
            simp only [map_smul, LinearMap.sub_apply, Module.End.one_apply, heigen, sub_smul,
              one_smul]
          _ = (μ - 1) ^ m.succ • v := by rw [smul_smul, pow_succ]
  rw [isUnipotent_def] at hg
  obtain ⟨n, hn⟩ := hg
  have hzero : (μ - 1) ^ n • v = 0 := by
    rw [← hpow_apply n, hn]
    rfl
  have hpow : (μ - 1) ^ n = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hv
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)

end GeneralLinearGroup

end

end TauCeti
