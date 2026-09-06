/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.GroupTheory.Perm.AlternatingCharacter
public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
public import TauCeti.RepresentationTheory.Induction.Mackey.LinearCharacter

/-!
# Clifford theory along `A₄ ◁ S₄`: the inertia group of a linear character

The alternating group is normal in the symmetric group, so Clifford theory applies to the pair
`alternatingGroup α ◁ Equiv.Perm α`, and the first thing it asks for is the **inertia group** of a
representation of the normal subgroup. This file computes it for a linear character: for a
*nontrivial* `χ : alternatingGroup α →* kˣ`,

`inertia (FDRep.ofLinearCharacter χ) = alternatingGroup α`,

the smallest value Clifford theory allows, `TauCeti.le_inertia` giving the other inclusion for
free. The computation is the group theory of `TauCeti.GroupTheory.Perm.AlternatingCharacter`: an
odd permutation inverts every linear character of the alternating group, so it moves a nontrivial
one, and `χ` and `χ⁻¹` are two distinct characters making up one conjugation orbit.

A minimal inertia group is exactly what the Mackey irreducibility criterion for an induced linear
character wants, so `Ind` of a nontrivial `χ` is irreducible; and induction from a subgroup of
index two doubles the dimension, so what it produces is a **two-dimensional irreducible
representation** of `Equiv.Perm α`.

For `Nat.card α = 4` this is the `A₄ ◁ S₄` case, and it is not vacuous:
`TauCeti.exists_monoidHom_alternatingGroup_ne_one` produces a nontrivial linear character of `A₄`
from the identification of its commutator subgroup with the Klein four subgroup. The last statement
of the file assembles the three facts for that case: over an algebraically closed field of
characteristic zero, `S₄` has a two-dimensional irreducible representation induced from `A₄`.

Two further facts about the pair `A₄ ◁ S₄` lie outside the scope of this file: that the nontrivial
linear characters of `A₄` are *exactly* `χ` and `χ⁻¹`, which needs the order of the character group
and not just the orbit; and that the three-dimensional irreducible of `A₄` is `S₄`-fixed, the case
of the Clifford correspondence complementary to the one treated here.

## Main statements

* `TauCeti.inertia_ofLinearCharacter_alternatingGroup`: **the inertia group of a nontrivial linear
  character of the alternating group is the alternating group.**
* `TauCeti.simple_indFDRep_ofLinearCharacter_alternatingGroup`: **a nontrivial linear character of
  the alternating group induces irreducibly** to the symmetric group.
* `TauCeti.finrank_indFDRep_ofLinearCharacter_alternatingGroup`: what it induces to is
  two-dimensional, the alternating group having index two.
* `TauCeti.exists_simple_finrank_two_indFDRep_alternatingGroup`: **the `A₄ ◁ S₄` case**, where
  such a character exists, so `S₄` has a two-dimensional irreducible induced from `A₄`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 8.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {α k : Type u} [DecidableEq α] [Fintype α] [Field k]

/-- **The inertia group of a nontrivial linear character of the alternating group is the
alternating group itself.** Clifford theory always puts the normal subgroup inside the inertia
group (`TauCeti.le_inertia`); here nothing else is in it, because an odd permutation inverts every
linear character of the alternating group and so moves a nontrivial one. -/
theorem inertia_ofLinearCharacter_alternatingGroup {χ : alternatingGroup α →* kˣ} (hχ : χ ≠ 1) :
    inertia (FDRep.ofLinearCharacter (k := k) χ) = alternatingGroup α := by
  refine le_antisymm (fun g hg => ?_) (le_inertia _)
  by_contra hgnot
  rw [mem_inertia_iff, nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff] at hg
  obtain ⟨x, hx⟩ :=
    exists_map_conjNormal_alternatingGroup_ne χ hχ
      (s := g⁻¹) fun hmem => hgnot (by simpa using inv_mem hmem)
  exact hx (hg x)

variable [IsAlgClosed k] [CharZero k]

/-- **A nontrivial linear character of the alternating group induces irreducibly to the symmetric
group.** The Mackey criterion for an induced linear character asks that no permutation outside the
alternating group stabilize `χ`, which is
`TauCeti.exists_map_conjNormal_alternatingGroup_ne`. -/
theorem simple_indFDRep_ofLinearCharacter_alternatingGroup {χ : alternatingGroup α →* kˣ}
    (hχ : χ ≠ 1) : Simple (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) :=
  (simple_indFDRep_ofLinearCharacter_iff χ).mpr fun _ hs =>
    exists_map_conjNormal_alternatingGroup_ne χ hχ hs

omit [IsAlgClosed k] [CharZero k] in
/-- **What a linear character of the alternating group induces to is two-dimensional**, the
alternating group having index two. Together with
`TauCeti.simple_indFDRep_ofLinearCharacter_alternatingGroup` this is a two-dimensional irreducible
representation of the symmetric group. -/
theorem finrank_indFDRep_ofLinearCharacter_alternatingGroup [Nontrivial α]
    (χ : alternatingGroup α →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) = 2 := by
  rw [finrank_indFDRep_ofLinearCharacter, alternatingGroup.index_eq_two]

/-- **The `A₄ ◁ S₄` case.** Over an algebraically closed field of characteristic zero, `A₄` has a
nontrivial linear character; its inertia group in `S₄` is `A₄`, so it induces irreducibly, and what
it induces to is the two-dimensional irreducible representation of `S₄`. -/
theorem exists_simple_finrank_two_indFDRep_alternatingGroup (hα : Nat.card α = 4) :
    ∃ χ : alternatingGroup α →* kˣ,
      inertia (FDRep.ofLinearCharacter (k := k) χ) = alternatingGroup α ∧
        Simple (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) ∧
        Module.finrank k (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) = 2 := by
  have hnt : Nontrivial α := by
    rw [← Finite.one_lt_card_iff_nontrivial, hα]
    norm_num
  have _ : NeZero ((Monoid.exponent (Abelianization (alternatingGroup α)) : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ, hχ⟩ := exists_monoidHom_alternatingGroup_ne_one (α := α) k hα
  exact ⟨χ, inertia_ofLinearCharacter_alternatingGroup hχ,
    simple_indFDRep_ofLinearCharacter_alternatingGroup hχ,
    finrank_indFDRep_ofLinearCharacter_alternatingGroup χ⟩

end TauCeti
