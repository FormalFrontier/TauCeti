/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basic
public import Mathlib.RepresentationTheory.Character

/-!
# The action of a class sum on a representation

A representation of a finite group `G` extends to the group algebra, so each class sum `K_C` acts
on it. This file computes that action and its trace: the action is the sum of the actions of the
members of the class, and, the character being constant on a conjugacy class, the trace is the size
of the class times the character value there.

Neither statement needs irreducibility or an algebraically closed field; they are the traces that
turn the defining scalar identity of a central character into the class-sum formula
`ωᵪ(K_C) · χ(1) = |C| · χ(g)`.

## Main statements

* `TauCeti.Representation.asAlgebraHom_classSum`: a class sum acts by the sum of the actions of the
  elements of the class.
* `TauCeti.Representation.trace_asAlgebraHom_classSum`: the trace of that action is
  `|C| · χ(g)` for any `g` in `C`.

## Implementation notes

These declarations live in `TauCeti.Representation`, not in the root `Representation` namespace, so
dot notation on a representation does not reach them.
-/

public section

namespace TauCeti

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w} [Group G] [Fintype G] [DecidableEq G]

section

variable [CommSemiring k] [AddCommMonoid V] [Module k V] (ρ : Representation k G V)

/-- A class sum acts on a representation by the sum of the actions of the elements of the class. -/
theorem asAlgebraHom_classSum (C : ConjClasses G) :
    ρ.asAlgebraHom (classSum k C) = ∑ x : C.carrier, ρ (x : G) := by
  rw [classSum_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun x _ => ρ.asAlgebraHom_of x

end

variable [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The character is constant on a conjugacy class, so the trace of the action of a class sum is
the size of the class times the character value there. -/
theorem trace_asAlgebraHom_classSum {C : ConjClasses G} {g : G} (hg : ConjClasses.mk g = C) :
    LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) = Nat.card C.carrier * ρ.character g := by
  rw [asAlgebraHom_classSum, map_sum]
  have hconst : ∀ x : C.carrier, LinearMap.trace k V (ρ (x : G)) = ρ.character g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm))
    exact ρ.char_conj g c
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

end Representation

end TauCeti
