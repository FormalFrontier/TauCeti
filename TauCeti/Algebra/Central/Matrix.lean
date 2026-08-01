/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix

/-!
# Centrality descends from a matrix algebra to its coefficients

Mathlib proves that a matrix algebra over a central algebra is central
(`Algebra.IsCentral.matrix`). This file supplies the converse over a nonempty finite index type:
the centre of `Matrix ι ι D` is the image of the centre of `D` under the scalar embedding
`Matrix.scalarAlgHom`, which is injective as soon as `ι` is nonempty, so the centre of `D` is `⊥`
whenever the centre of `Matrix ι ι D` is.

* `TauCeti.isCentral_of_isCentral_matrix`: if `Matrix ι ι D` is central over `K`, then so is `D`;
* `TauCeti.isCentral_matrix_iff` packages this with Mathlib's converse.

## Implementation notes

`TauCeti.isCentral_of_isCentral_matrix` is deliberately *not* an instance: its hypothesis mentions
`Matrix ι ι D` while its conclusion mentions only `D`, so instance search could not run it
backwards, and the index type `ι` is unconstrained by the goal.
-/

public section

namespace TauCeti

variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D]
  (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- If a matrix algebra `Matrix ι ι D` over a nonempty finite index type is central over `K`, then
its coefficient algebra `D` is central over `K`.

The centre of `Matrix ι ι D` is the image of the centre of `D` under the scalar embedding
`Matrix.scalarAlgHom`, which is injective because `ι` is nonempty; so the centre of `D` is `⊥` as
soon as the centre of the matrix algebra is. This is the converse of `Algebra.IsCentral.matrix`. -/
theorem isCentral_of_isCentral_matrix [Algebra.IsCentral K (Matrix ι ι D)] :
    Algebra.IsCentral K D := by
  have hinj : Function.Injective (Matrix.scalarAlgHom ι K : D →ₐ[K] Matrix ι ι D) := fun _ _ h ↦
    Matrix.scalar_inj.mp (by simpa only [Matrix.scalarAlgHom_apply] using h)
  have h : (Subalgebra.center K D).map (Matrix.scalarAlgHom ι K) =
      (⊥ : Subalgebra K D).map (Matrix.scalarAlgHom ι K) := by
    rw [Algebra.map_bot, ← Matrix.subalgebraCenter_eq_scalarAlgHom_map,
      Algebra.IsCentral.center_eq_bot]
  exact ⟨(Subalgebra.map_injective hinj h).le⟩

/-- A matrix algebra over a nonempty finite index type is central exactly when its coefficient
algebra is. -/
@[simp]
theorem isCentral_matrix_iff :
    Algebra.IsCentral K (Matrix ι ι D) ↔ Algebra.IsCentral K D :=
  ⟨fun _ ↦ isCentral_of_isCentral_matrix K D ι, fun _ ↦ Algebra.IsCentral.matrix K D ι⟩

end TauCeti
