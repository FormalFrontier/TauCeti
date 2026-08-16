/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Module.Lattice

/-!
# Rationalizing integral Lie lattices

Let `M` be a free full Lie lattice over a domain `R` in a Lie algebra `L` over its fraction field
`K`. The underlying submodule inclusion exhibits `L` as the scalar extension `K ⊗[R] M`. This file
proves that the canonical rationalization equivalence respects the Lie bracket, giving

```text
K ⊗[R] M ≃ₗ⁅K⁆ L.
```

The source carries Mathlib's scalar-extended Lie bracket. Thus the result identifies the generic
fibre as a Lie algebra, rather than only as a vector space. Its pure-tensor and inverse equations
make the equivalence usable without unfolding either the tensor-product bracket or the lattice
rationalization construction.

## Main declaration

* `TauCeti.LieSubalgebra.rationalizationEquiv`: the canonical Lie equivalence from the scalar
  extension of a free full integral Lie subalgebra to its ambient rational Lie algebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This is the generic-fibre step for the Chevalley integral form used in Layer 9 of the
`ReductiveGroups` roadmap. That pinned Chevalley--Demazure construction is consumed by milestone
L0 of the `CFSGStatement` roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace LieSubalgebra

universe u v w

variable {R : Type u} {K : Type v} {L : Type w}
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [IsScalarTower R K L]

-- Mathlib's scalar-extension bracket and the bracket of the automatically inferred self-module
-- are propositionally equal but not definitionally equal. These elementary consequences of the
-- `LieRing` fields keep the proof on the scalar-extension bracket selected by the goal.
private theorem bracket_zero {A : Type*} [LieRing A] (x : A) : ⁅x, (0 : A)⁆ = 0 := by
  have h := LieRing.lie_add x (0 : A) (0 : A)
  rw [zero_add] at h
  exact (sub_eq_of_eq_add h).symm.trans (sub_self _)

private theorem zero_bracket {A : Type*} [LieRing A] (x : A) : ⁅(0 : A), x⁆ = 0 := by
  have h := LieRing.add_lie (0 : A) (0 : A) x
  rw [zero_add] at h
  exact (sub_eq_of_eq_add h).symm.trans (sub_self _)

private theorem neg_bracket_swap {A : Type*} [LieRing A] (x y : A) : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h := LieRing.lie_self (x + y)
  rw [LieRing.add_lie, LieRing.lie_add, LieRing.lie_add, LieRing.lie_self, LieRing.lie_self,
    zero_add, add_zero] at h
  exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using h)

private theorem bracket_smul_left {R A : Type*} [CommRing R] [LieRing A] [LieAlgebra R A]
    (r : R) (x y : A) : ⁅r • x, y⁆ = r • ⁅x, y⁆ := by
  calc
    ⁅r • x, y⁆ = -⁅y, r • x⁆ := (neg_bracket_swap (r • x) y).symm
    _ = -(r • ⁅y, x⁆) := by rw [LieAlgebra.lie_smul]
    _ = r • -⁅y, x⁆ := by rw [smul_neg]
    _ = r • ⁅x, y⁆ := by rw [neg_bracket_swap]

private theorem rationalizationEquiv_map_lie (M : LieSubalgebra R L)
    [Module.Free R M] [M.toSubmodule.IsLattice K] (x y : K ⊗[R] M) :
    Submodule.rationalizationEquiv M.toSubmodule ⁅x, y⁆ =
      ⁅Submodule.rationalizationEquiv M.toSubmodule x,
        Submodule.rationalizationEquiv M.toSubmodule y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [zero_bracket, map_zero, zero_bracket]
  | tmul q x =>
      induction y using TensorProduct.induction_on with
      | zero => rw [bracket_zero, map_zero, bracket_zero]
      | tmul r y =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul]
          rw [Submodule.rationalizationEquiv_tmul, Submodule.rationalizationEquiv_tmul,
            Submodule.rationalizationEquiv_tmul]
          rw [bracket_smul_left, LieAlgebra.lie_smul, LieSubalgebra.coe_bracket, smul_smul]
      | add y z hy hz =>
          rw [LieRing.lie_add, map_add, hy, hz, map_add, LieRing.lie_add]
  | add x y hx hy =>
      rw [LieRing.add_lie, map_add, hx, hy, map_add, LieRing.add_lie]

/-- The canonical rationalization of a free full integral Lie subalgebra, as a Lie algebra
equivalence.

The underlying linear equivalence is `TauCeti.Submodule.rationalizationEquiv`. The bracket on its
source is Mathlib's scalar-extension bracket on `K ⊗[R] M`. -/
noncomputable def rationalizationEquiv (M : LieSubalgebra R L)
    [Module.Free R M] [M.toSubmodule.IsLattice K] :
    K ⊗[R] M ≃ₗ⁅K⁆ L where
  __ := Submodule.rationalizationEquiv M.toSubmodule
  map_lie' := by
    intro x y
    -- `LieEquiv` exposes the underlying `LinearEquiv` through a generated coercion wrapper.
    change Submodule.rationalizationEquiv M.toSubmodule ⁅x, y⁆ =
      ⁅Submodule.rationalizationEquiv M.toSubmodule x,
        Submodule.rationalizationEquiv M.toSubmodule y⁆
    exact rationalizationEquiv_map_lie M x y

/-- Rationalization sends a pure tensor to scalar multiplication of the embedded integral
element. -/
@[simp]
theorem rationalizationEquiv_tmul (M : LieSubalgebra R L)
    [Module.Free R M] [M.toSubmodule.IsLattice K] (q : K) (x : M) :
    rationalizationEquiv M (q ⊗ₜ[R] x) = q • (x : L) :=
  Submodule.rationalizationEquiv_tmul M.toSubmodule q x

/-- The inverse rationalization sends an embedded integral element to its unit pure tensor. -/
@[simp]
theorem rationalizationEquiv_symm_coe (M : LieSubalgebra R L)
    [Module.Free R M] [M.toSubmodule.IsLattice K] (x : M) :
    (rationalizationEquiv M).symm (x : L) = 1 ⊗ₜ[R] x :=
  Submodule.rationalizationEquiv_symm_coe M.toSubmodule x

end LieSubalgebra

end TauCeti
