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

/-- A central element of `U(L)` acts by an endomorphism commuting with the action of every element
of `L`. This is what makes the eigenspaces of a central element Lie submodules. -/
theorem representation_lie_of_mem_center {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) (x : L) (m : M) :
    representation R L M u ⁅x, m⁆ = ⁅x, representation R L M u m⁆ := by
  have h := congrArg (fun u ↦ representation R L M u m) (Subalgebra.mem_center_iff.mp hu
    (_root_.UniversalEnvelopingAlgebra.ι R x))
  simp only [map_mul, Module.End.mul_apply, representation_ι_apply] at h
  exact h.symm

/-- A central element acting by a scalar on a generator of a Lie module acts by that scalar on the
whole module. Its eigenspace is a Lie submodule containing the generator and hence its Lie span. -/
theorem representation_apply_eq_smul_of_lieSpan_eq_top
    {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) {c : R} {v : M}
    (hv : representation R L M u v = c • v) (hgen : LieSubmodule.lieSpan R L {v} = ⊤) (m : M) :
    representation R L M u m = c • m := by
  let F : Module.End R M := representation R L M u - c • LinearMap.id
  have hmemF : ∀ z : M, z ∈ LinearMap.ker F ↔ representation R L M u z = c • z := fun z ↦ by
    simp only [F, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, sub_eq_zero]
  have hstab : ∀ (y : L) (z : M), representation R L M u z = c • z →
      representation R L M u ⁅y, z⁆ = c • ⁅y, z⁆ := fun y z hz ↦ by
    rw [representation_lie_of_mem_center hu y z, hz, lie_smul]
  have key : (LieSubmodule.lieSpan R L {v} : LieSubmodule R L M) ≤
      ({ __ := LinearMap.ker F
         lie_mem := fun {y z} hz ↦ (hmemF _).mpr (hstab y z ((hmemF z).mp hz)) } :
        LieSubmodule R L M) :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr ((hmemF v).mpr hv))
  exact (hmemF m).mp (key (by rw [hgen]; trivial))

end TauCeti.UniversalEnvelopingAlgebra
