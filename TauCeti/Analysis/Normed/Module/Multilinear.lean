/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps on finitely many finite-dimensional spaces are continuous

A multilinear map `f : MultilinearMap 𝕜 M N` on finitely many finite-dimensional normed spaces
over a complete field is continuous, with no bound assumed:
`MultilinearMap.continuous_of_finiteDimensional`. Expanding each argument in a basis
writes `f` as a finite sum of terms `(∏ i, coordinate) • constant`, and each coordinate is a
linear functional on a finite-dimensional space, hence continuous.

This is the multilinear companion of `LinearMap.continuous_of_finiteDimensional`. Mathlib's
`MultilinearMap.continuous_of_bound` asks for an explicit bound, which is exactly what one does
not have when the multilinear map arrives from algebra — a tensor or symmetric-power
construction, say — rather than from analysis.
-/

public section

namespace MultilinearMap

variable {𝕜 ι : Type*} {M : ι → Type*} {N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Finite ι] [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
  [∀ i, FiniteDimensional 𝕜 (M i)] [NormedAddCommGroup N] [NormedSpace 𝕜 N]

/-- **A multilinear map on finitely many finite-dimensional spaces is continuous.** Over a
complete field, no bound need be assumed: expanding every argument in a basis exhibits the map as
a finite sum of products of coordinates times constant vectors. -/
theorem continuous_of_finiteDimensional (f : MultilinearMap 𝕜 M N) : Continuous f := by
  classical
  cases nonempty_fintype ι
  set b : ∀ i, Module.Basis (Fin (Module.finrank 𝕜 (M i))) 𝕜 (M i) :=
    fun i ↦ Module.finBasis 𝕜 (M i) with hb
  have key : ⇑f = fun m : ∀ i, M i ↦ ∑ r : ∀ i, Fin (Module.finrank 𝕜 (M i)),
      (∏ i, (b i).repr (m i) (r i)) • f fun i ↦ b i (r i) := by
    funext m
    have hm : f m = f fun i ↦ ∑ j, (b i).repr (m i) j • b i j := by
      congr 1 with i
      exact ((b i).sum_repr (m i)).symm
    rw [hm, f.map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ f.map_smul_univ _ _
  rw [key]
  refine continuous_finsetSum _ fun r _ ↦ Continuous.smul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ ↦ ?_
  exact (((b i).coord (r i)).continuous_of_finiteDimensional.comp
    (continuous_apply i)).congr fun m ↦ Module.Basis.coord_apply _ _ _

end MultilinearMap
