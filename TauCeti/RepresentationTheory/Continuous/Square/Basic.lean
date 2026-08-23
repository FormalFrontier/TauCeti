/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Symmetric
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation
public import TauCeti.RepresentationTheory.Continuous.TensorProduct

/-!
# The symmetric and exterior squares of a continuous representation

The tensor square `TauCeti.ContRepresentation.tprod π π` of a continuous representation acts on
`V ⊗[𝕜] V` by `π g ⊗ π g`, which commutes with the flip `x ⊗ y ↦ y ⊗ x`. The two eigenspaces of
that flip, `TauCeti.symmetricTensors` and `TauCeti.antisymmetricTensors`, are therefore invariant
submodules, and restricting the tensor square to them gives the **symmetric square** and the
**exterior square** of `π`, again as continuous representations.

Realizing the two squares inside `V ⊗[𝕜] V` rather than as `Sym[𝕜]^2 V` and `⋀[𝕜]^2 V` is what
makes them continuous representations at all: the carrier of a continuous representation has to
carry a topology, and a submodule of the tensor square of an inner product space does, whereas a
quotient or a subobject of a `PiTensorProduct` carries none. Over `RCLike 𝕜`, which has
characteristic zero, the two eigenspaces *are* the symmetric and exterior squares, which is what
the names record; the identification itself is not formalized here.

## Main definitions

* `ContRepresentation.symmetricSquare`: the tensor square of a continuous representation restricted
  to the symmetric tensors of `V ⊗[𝕜] V`.
* `ContRepresentation.exteriorSquare`: its restriction to the antisymmetric tensors.

## Main statements

* `ContRepresentation.continuous_symmetricSquare` and
  `ContRepresentation.continuous_exteriorSquare`: both squares of a continuous representation are
  continuous.
* `ContRepresentation.symmetricSquare_apply` and `ContRepresentation.exteriorSquare_apply`: each
  square acts by the restriction of `π g ⊗ π g`, which is how their characters are computed.

## Implementation notes

Nothing here needs a group, a measure, or compactness, so the statements are made over a
topological monoid with `RCLike` scalars; the consumer is
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantTensors.lean`, where the invariants
of the two squares are what the Frobenius-Schur indicator counts.

All declarations sit in the **root** `ContRepresentation` namespace, so that
`π.symmetricSquare` elaborates: `ContRepresentation` is Mathlib's type, and
`scripts/lint-dot-notation.py` asks that new declarations about it not recreate its namespace
inside `TauCeti`. That is why the ambient `TauCeti` names this file consumes are brought in by
`open`.
-/

public section

open TauCeti TauCeti.ContRepresentation

open scoped TensorProduct

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in
/-- The tensor square of a continuous representation acts on the tensor square by `f ⊗ f`, so the
symmetric tensors are one of its invariant submodules. -/
theorem tprod_self_mem_symmetricTensors (g : G) {x : V ⊗[𝕜] V}
    (hx : x ∈ symmetricTensors 𝕜 V) : tprod π π g x ∈ symmetricTensors 𝕜 V := by
  rw [ContRepresentation.tprod_apply, TensorProduct.mapL_apply]
  exact map_self_mem_symmetricTensors _ hx

omit [TopologicalSpace G] in
/-- The antisymmetric tensors are the other invariant submodule of the tensor square. -/
theorem tprod_self_mem_antisymmetricTensors (g : G) {x : V ⊗[𝕜] V}
    (hx : x ∈ antisymmetricTensors 𝕜 V) : tprod π π g x ∈ antisymmetricTensors 𝕜 V := by
  rw [ContRepresentation.tprod_apply, TensorProduct.mapL_apply]
  exact map_self_mem_antisymmetricTensors _ hx

/-- **The symmetric square** of a continuous representation: its tensor square restricted to the
symmetric tensors. -/
noncomputable def symmetricSquare : ContRepresentation 𝕜 G (symmetricTensors 𝕜 V) :=
  subrepresentation (tprod π π) (symmetricTensors 𝕜 V)
    fun g _ hx ↦ tprod_self_mem_symmetricTensors π g hx

/-- **The exterior square** of a continuous representation: its tensor square restricted to the
antisymmetric tensors. Over `RCLike 𝕜`, which has characteristic zero, those are the exterior
square `⋀[𝕜]^2 V` realized inside `V ⊗[𝕜] V`, which is what the name records; the identification
itself is not formalized here. -/
noncomputable def exteriorSquare : ContRepresentation 𝕜 G (antisymmetricTensors 𝕜 V) :=
  subrepresentation (tprod π π) (antisymmetricTensors 𝕜 V)
    fun g _ hx ↦ tprod_self_mem_antisymmetricTensors π g hx

/-- The symmetric square of a continuous representation is continuous. -/
theorem continuous_symmetricSquare (hπ : Continuous π) : Continuous (symmetricSquare π) :=
  continuous_subrepresentation (continuous_tprod π π hπ hπ)

/-- The exterior square of a continuous representation is continuous. -/
theorem continuous_exteriorSquare (hπ : Continuous π) : Continuous (exteriorSquare π) :=
  continuous_subrepresentation (continuous_tprod π π hπ hπ)

omit [TopologicalSpace G] in
/-- The symmetric square acts by the restriction of `π g ⊗ π g`. -/
@[simp]
theorem symmetricSquare_apply (g : G) :
    ((symmetricSquare π g : symmetricTensors 𝕜 V →L[𝕜] symmetricTensors 𝕜 V) :
        symmetricTensors 𝕜 V →ₗ[𝕜] symmetricTensors 𝕜 V)
      = symmetricTensorsRestrict (π g : V →ₗ[𝕜] V) := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [symmetricSquare, ContRepresentation.tprod_apply]

omit [TopologicalSpace G] in
/-- The exterior square acts by the restriction of `π g ⊗ π g`. -/
@[simp]
theorem exteriorSquare_apply (g : G) :
    ((exteriorSquare π g : antisymmetricTensors 𝕜 V →L[𝕜] antisymmetricTensors 𝕜 V) :
        antisymmetricTensors 𝕜 V →ₗ[𝕜] antisymmetricTensors 𝕜 V)
      = antisymmetricTensorsRestrict (π g : V →ₗ[𝕜] V) := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [exteriorSquare, ContRepresentation.tprod_apply]

end ContRepresentation
