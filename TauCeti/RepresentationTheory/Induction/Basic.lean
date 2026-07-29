/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Induced

/-!
# Generators of an induced representation

Mathlib builds the induced representation `Representation.ind φ ρ` on the coinvariants
`Representation.IndV φ ρ` of `k[G'] ⊗[k] A`, with generators `Representation.IndV.mk`. Mathlib's
`Representation.ind_mk` describes the induced *action* on those generators; this file records the
complementary fact, the relation that passing to coinvariants imposes *between* the generators.

## Main statements

* `TauCeti.indV_mk_mul`: translating the group coordinate of a generator by `φ g` is undone by
  acting by `g` on the coefficient.
-/

public section

open Representation TensorProduct

namespace TauCeti

universe u v w

variable {k : Type u} [CommRing k] {G : Type v} {G' : Type w} [Group G] [Group G']
  (φ : G →* G') {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k G A)

/-- The defining relation of the induced representation `Ind_φ ρ`: translating the group
coordinate of a generator by `φ g` is undone by acting by `g` on the coefficient. -/
@[simp]
theorem indV_mk_mul (g : G) (h : G') (a : A) :
    IndV.mk φ ρ (φ g * h) (ρ g a) = IndV.mk φ ρ h a := by
  refine Eq.trans (congrArg
    (Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G').comp φ) ρ)) ?_)
    (Coinvariants.mk_self_apply _ g (MonoidAlgebra.single h 1 ⊗ₜ a))
  simp [leftRegular]

end TauCeti
