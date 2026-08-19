/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# The representation of an enveloping algebra on a Lie module

A module over a Lie algebra `L` is the same thing as a module over the enveloping algebra `U(L)`.
This file records the direction that a construction inside `U(L)` needs: a Lie module `M` carries
an algebra map `U(L) →ₐ[R] Module.End R M` extending the Lie action, obtained from the universal
property applied to `LieModule.toEnd`.

The adjoint representation of `TauCeti/Algebra/Lie/UniversalEnveloping/Basic.lean` is the case
`M = L`, and `TauCeti.UniversalEnvelopingAlgebra.adjointRepresentation_eq_representation` records
that; the two definitions agree by `rfl`, `LieAlgebra.ad` being `LieModule.toEnd` on `L` itself.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.representation`: the algebra map `U(L) →ₐ[R] Module.End R M`
  extending the action of `L` on a Lie module `M`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply`: a canonical Lie generator acts by
  the Lie bracket.
* `TauCeti.UniversalEnvelopingAlgebra.commute_representation_of_mem_center`: the image of a central
  element of `U(L)` commutes with the whole action, so its eigenspaces are Lie submodules.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- **The representation of `U(L)` on a Lie module `M`**: the algebra map extending the action of
`L` on `M`, supplied by the universal property of the enveloping algebra. -/
noncomputable def representation : U →ₐ[R] Module.End R M :=
  _root_.UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)

-- Not a `simp` lemma, for the reason recorded at
-- `TauCeti.UniversalEnvelopingAlgebra.adjointRepresentation_ι`: `simp` rewrites `ι` through
-- Mathlib's `UniversalEnvelopingAlgebra.ι_apply`, so this left-hand side is not in normal form.
/-- The representation acts on a canonical Lie generator by the Lie action. -/
theorem representation_ι (x : L) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) = LieModule.toEnd R L M x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The pointwise form of `TauCeti.UniversalEnvelopingAlgebra.representation_ι`: a canonical Lie
generator acts by the Lie bracket. -/
theorem representation_ι_apply (x : L) (m : M) :
    representation R L M (_root_.UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  rw [representation_ι, LieModule.toEnd_apply_apply]

/-- The adjoint representation of `U(L)` is its representation on `L` itself: `LieAlgebra.ad` is
the Lie action of `L` on itself. -/
theorem adjointRepresentation_eq_representation :
    adjointRepresentation R L = representation R L L :=
  (_root_.UniversalEnvelopingAlgebra.lift_unique R (LieModule.toEnd R L L) _).mp
    (funext fun x ↦ adjointRepresentation_ι R L x)

variable {R L M}

/-- A central element of `U(L)` acts by an endomorphism commuting with the action of every element
of `L`. This is what makes the eigenspaces of a central element Lie submodules. -/
theorem commute_representation_of_mem_center {u : _root_.UniversalEnvelopingAlgebra R L}
    (hu : u ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L)) (x : L) (m : M) :
    representation R L M u ⁅x, m⁆ = ⁅x, representation R L M u m⁆ := by
  have h := congrArg (fun u ↦ representation R L M u m) (Subalgebra.mem_center_iff.mp hu
    (_root_.UniversalEnvelopingAlgebra.ι R x))
  simp only [map_mul, Module.End.mul_apply, representation_ι_apply] at h
  exact h.symm

end TauCeti.UniversalEnvelopingAlgebra
