/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Restricting a continuous representation to an invariant submodule

This file restricts a continuous representation of a monoid to a submodule preserved by every
action operator, the continuous counterpart of Mathlib's `Representation.subrepresentation`.

## Main definitions

* `TauCeti.ContRepresentation.subrepresentation`: the restriction of a continuous representation to
  an invariant submodule.

## Main results

* `TauCeti.ContRepresentation.toRepresentation_subrepresentation`: the underlying representation of
  a restricted continuous representation is the restriction of the underlying representation.
* `TauCeti.ContRepresentation.continuous_subrepresentation`: the restriction of a continuous
  representation to an invariant submodule is again continuous.
-/

public section

namespace TauCeti

namespace ContRepresentation

section Restriction

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- The restriction of a continuous representation to an invariant submodule. This is the
continuous counterpart of `Representation.subrepresentation`. -/
def subrepresentation (π : ContRepresentation R G V) (W : Submodule R V)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContRepresentation R G W :=
  .ofMonoidHom
    { toFun g := (π g).restrict (hW g)
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }

variable {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- The restricted action is the ambient action, read on the underlying vectors. -/
@[simp]
theorem coe_subrepresentation_apply (g : G) (v : W) :
    ((subrepresentation π W hW g v : W) : V) = π g (v : V) :=
  (rfl)

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
theorem toRepresentation_subrepresentation :
    (subrepresentation π W hW).toRepresentation
      = π.toRepresentation.subrepresentation W fun g _ hv => hW g _ hv := by
  ext g v
  simp [_root_.ContRepresentation.toMonoidHom_apply]

end Restriction

section Continuity

variable {𝕜 G V : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V] [ContinuousConstSMul 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {W : Submodule 𝕜 V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a continuous representation to an invariant submodule preserves continuity. The
inclusion of `W` is inducing, so this reduces to the continuity of `g ↦ π g ∘L W.subtypeL`, which
is precomposition by a fixed continuous linear map applied to `π`. -/
theorem continuous_subrepresentation (hπ : Continuous π) :
    Continuous (subrepresentation π W hW) := by
  rw [(ContinuousLinearMap.isInducing_postcomp W.subtypeL
    Topology.IsInducing.subtypeVal).continuous_iff]
  exact (ContinuousLinearMap.precomp V W.subtypeL).continuous.comp hπ

end Continuity

end ContRepresentation

end TauCeti
