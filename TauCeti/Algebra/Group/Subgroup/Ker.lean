/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernels and equality loci of group homomorphisms

This file supplies the characteristic membership equation for the subgroup equality locus.
-/

public section

namespace MonoidHom

variable {G M : Type*} [Group G] [Monoid M]

/-- Membership in the equality locus of two group homomorphisms is pointwise equality. -/
@[to_additive (attr := simp)]
theorem mem_eqLocus {f g : G →* M} {x : G} : x ∈ f.eqLocus g ↔ f x = g x :=
  Iff.rfl

end MonoidHom
