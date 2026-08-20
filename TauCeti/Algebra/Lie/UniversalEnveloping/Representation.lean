/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# Central elements in enveloping-algebra representations

The canonical algebra map from `U(L)` to the endomorphisms of a Lie module is defined in
`TauCeti.Algebra.Lie.UniversalEnveloping.Basic`. This file develops the consequences of centrality:
a central element acts by an endomorphism commuting with the Lie action, and an eigenvalue on a
Lie-module generator therefore extends to the whole module.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representationLieModuleHomOfMemCenter`: the action of a
  central element, bundled as a Lie-module endomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.representation_lie_of_mem_center`: the image of a central
  element of `U(L)` commutes with the whole action, so its eigenspaces are Lie submodules.
* `TauCeti.UniversalEnvelopingAlgebra.representation_apply_eq_smul_of_lieSpan_eq_top`: a central
  element acting by a scalar on a Lie-module generator acts by that scalar everywhere.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {R L M}

/-- The action of a central element of `U(L)`, bundled as a Lie-module endomorphism. -/
noncomputable def representationLieModuleHomOfMemCenter
    {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) : M →ₗ⁅R,L⁆ M where
  toLinearMap := representation R L M u
  map_lie' := by
    intro x m
    have h := congrArg (fun u ↦ representation R L M u m) (Subalgebra.mem_center_iff.mp hu
      (_root_.UniversalEnvelopingAlgebra.ι R x))
    simp only [map_mul, Module.End.mul_apply, representation_ι_apply] at h
    exact h.symm

/-- Applying the bundled action of a central element is the canonical enveloping-algebra action. -/
@[simp]
theorem representationLieModuleHomOfMemCenter_apply
    {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) (m : M) :
    representationLieModuleHomOfMemCenter hu m = representation R L M u m := by
  simp [representationLieModuleHomOfMemCenter]

/-- A central element of `U(L)` acts by an endomorphism commuting with the action of every element
of `L`. This is what makes the eigenspaces of a central element Lie submodules. -/
theorem representation_lie_of_mem_center {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) (x : L) (m : M) :
    representation R L M u ⁅x, m⁆ = ⁅x, representation R L M u m⁆ :=
  (representationLieModuleHomOfMemCenter hu).map_lie x m

/-- A central element acting by a scalar on a generator of a Lie module acts by that scalar on the
whole module. Its eigenspace is a Lie submodule containing the generator and hence its Lie span. -/
theorem representation_apply_eq_smul_of_lieSpan_eq_top
    {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) {c : R} {v : M}
    (hv : representation R L M u v = c • v) (hgen : LieSubmodule.lieSpan R L {v} = ⊤) (m : M) :
    representation R L M u m = c • m := by
  let f : M →ₗ⁅R,L⁆ M := representationLieModuleHomOfMemCenter (M := M) hu
  let F : M →ₗ⁅R,L⁆ M := f - c • (LieModuleHom.id : M →ₗ⁅R,L⁆ M)
  have hmemF : ∀ z : M, z ∈ F.ker ↔ representation R L M u z = c • z := fun z ↦ by
    simp only [LieModuleHom.mem_ker, F, LieModuleHom.sub_apply, LieModuleHom.smul_apply,
      LieModuleHom.id_apply, f, representationLieModuleHomOfMemCenter_apply, sub_eq_zero]
  have key : (LieSubmodule.lieSpan R L {v} : LieSubmodule R L M) ≤ F.ker :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr ((hmemF v).mpr hv))
  exact (hmemF m).mp (key (by rw [hgen]; trivial))

end TauCeti.UniversalEnvelopingAlgebra
