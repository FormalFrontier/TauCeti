/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic

/-!
# A genuinely nonlinear constant-structure `J`-holomorphic map

The whole `IsConstStructureJHolomorphic*` family is so far only ever instantiated at the identity,
the constants, and continuous real-linear maps. This file records an acceptance example that the
predicate is not vacuous on its intended nonlinear content: the complex squaring map `z ↦ z²`,
written in real coordinates `ℝ × ℝ ≅ ℂ` as `(x, y) ↦ (x² - y², 2xy)`, is globally
constant-structure `J`-holomorphic for the standard structure `AlmostComplexStructure.product ℝ`,
`(s, t) ↦ (-t, s)`, on both source and target, even though it is genuinely nonlinear.

This is the rule-out-vacuous-definitions check the analytic Heegaard Floer roadmap asks for
(`TauCetiRoadmap/HeegaardFloer/README.md`, the "checks along the way" acceptance criteria that
rule out vacuous or mis-stated definitions): the constant-structure Cauchy--Riemann equation
`df ∘ J = J' ∘ df` really does hold for a map whose derivative varies from point to point, so the
predicate captures ordinary complex differentiability and is not accidentally restricted to the
linear instances.

The proof is the pointwise linear algebra behind the Cauchy--Riemann equations: the Frechet
derivative of `z ↦ z²` at `a` is the real-linear map `(u, v) ↦ (2a₁u - 2a₂v, 2a₂u + 2a₁v)`, which
is multiplication by `2a` in the identification `ℝ × ℝ ≅ ℂ` and therefore commutes with the
standard structure.

## Main declarations

* `TauCeti.sqMap`: the real-coordinate squaring map `(x, y) ↦ (x² - y², 2xy)`.
* `TauCeti.not_isLinearMap_sqMap`: `sqMap` is genuinely nonlinear.
* `TauCeti.isConstStructureJHolomorphicAt_sqMap` and
  `TauCeti.isConstStructureJHolomorphic_sqMap`: `sqMap` is constant-structure `J`-holomorphic at
  every point, hence globally.

The Cauchy--Riemann sign convention matches McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, Section 2.1: `du ∘ j = J ∘ du`.
-/

public section

namespace TauCeti

/-- The complex squaring map `z ↦ z²` on `ℝ²`, written in real coordinates under the
identification `ℝ × ℝ ≅ ℂ` as `(x, y) ↦ (x² - y², 2xy)`. -/
def sqMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 ^ 2 - p.2 ^ 2, 2 * (p.1 * p.2))

@[simp]
lemma sqMap_apply (p : ℝ × ℝ) : sqMap p = (p.1 ^ 2 - p.2 ^ 2, 2 * (p.1 * p.2)) :=
  (rfl)

/-- `sqMap` is genuinely nonlinear: it does not commute with scalar multiplication, so it is not one
of the linear instances of the constant-structure `J`-holomorphic predicate. -/
lemma not_isLinearMap_sqMap : ¬ IsLinearMap ℝ sqMap := by
  intro h
  have hkey := h.map_smul 2 (1, 0)
  simp only [sqMap_apply, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at hkey
  norm_num at hkey

/-- The complex squaring map is constant-structure `J`-holomorphic at every point of `ℝ²` for the
standard almost complex structure on source and target. -/
theorem isConstStructureJHolomorphicAt_sqMap (a : ℝ × ℝ) :
    IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) sqMap a := by
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) a :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) a :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  -- The two real coordinate functions of `z ↦ z²` and their Frechet derivatives.
  have hg := HasFDerivAt.sub (HasFDerivAt.pow hfst 2) (HasFDerivAt.pow hsnd 2)
  have hh := HasFDerivAt.const_mul (HasFDerivAt.mul hfst hsnd) 2
  have hf := HasFDerivAt.prodMk hg hh
  refine isConstStructureJHolomorphicAt_of_hasFDerivAt hf ?_
  -- The derivative is multiplication by `2a` in `ℝ × ℝ ≅ ℂ`, so it commutes with the structure.
  rw [isComplexLinearMap_iff_apply]
  intro v
  apply Prod.ext <;>
    simp [AlmostComplexStructure.product_apply] <;> ring

/-- The complex squaring map is globally constant-structure `J`-holomorphic for the standard almost
complex structure on source and target. This is the roadmap's nonlinear acceptance example. -/
theorem isConstStructureJHolomorphic_sqMap :
    IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) sqMap :=
  isConstStructureJHolomorphic_of_forall isConstStructureJHolomorphicAt_sqMap

end TauCeti
