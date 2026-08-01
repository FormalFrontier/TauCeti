/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The square-class group `Kˣ ⧸ (Kˣ)²`

For a field `K`, the **square-class group** is the quotient of `Kˣ` by its squares. Every element
has order dividing `2`, so the quotient is an `𝔽₂ = ZMod 2`-vector space (Mathlib's
`QuotientAddGroup.zmodModule`, written additively on `Additive Kˣ`).

A `ZMod 2`-linear combination of the classes of a finite family of units is, up to the `{0, 1}`
coefficients, exactly a subset product, and it vanishes precisely when that subset product is a
square. So linear independence of the classes is the **Finset form** of square-class independence
(no nonempty subset product is a square), one subset at a time.

## Main definitions and results

* `TauCeti.SquareClassGroup`: the square-class group `Kˣ ⧸ (Kˣ)²`, an `𝔽₂`-vector space.
* `TauCeti.squareClass`: the class of a unit, with `squareClass_eq_zero_iff` characterising the
  trivial class as the squares.
* `TauCeti.linearIndependent_squareClass_iff`: the classes of `d : ι → Kˣ` are `ZMod 2`-linearly
  independent iff no nonempty subset product is a square.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K]

/-- **The square-class group** `Kˣ ⧸ (Kˣ)²`, written additively on `Additive Kˣ`. -/
abbrev SquareClassGroup (K : Type*) [Field K] : Type _ :=
  Additive Kˣ ⧸ (Subgroup.square Kˣ).toAddSubgroup

/-- The square-class group is a `ZMod 2`-module: every element has order dividing two, since the
double of any unit class is the class of a square. -/
instance : Module (ZMod 2) (SquareClassGroup K) :=
  QuotientAddGroup.zmodModule fun x => by
    rw [Additive.mem_toAddSubgroup, Subgroup.mem_square, toMul_nsmul]
    exact ⟨Additive.toMul x, pow_two _⟩

/-- The square class of a unit. -/
def squareClass (u : Kˣ) : SquareClassGroup K :=
  QuotientAddGroup.mk (Additive.ofMul u)

/-- A unit has trivial square class iff it is a square. -/
@[simp] theorem squareClass_eq_zero_iff (u : Kˣ) : squareClass u = 0 ↔ IsSquare u := by
  rw [squareClass, QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup,
    Subgroup.mem_square]
  simp

/-- The square class of a product is the sum of the square classes. -/
theorem squareClass_prod {ι : Type*} (S : Finset ι) (d : ι → Kˣ) :
    squareClass (∏ i ∈ S, d i) = ∑ i ∈ S, squareClass (d i) := by
  simp only [squareClass, ofMul_prod]
  rw [← QuotientAddGroup.mk'_apply, map_sum]
  simp only [QuotientAddGroup.mk'_apply]

private theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

/-- A `ZMod 2`-linear combination of square classes is the class of the corresponding subset
product (the subset where the coefficient is `1`). -/
private theorem sum_smul_squareClass {ι : Type*} [Fintype ι] (d : ι → Kˣ) (g : ι → ZMod 2) :
    ∑ i, g i • squareClass (d i)
      = squareClass (∏ i ∈ Finset.univ.filter (fun i => g i = 1), d i) := by
  rw [squareClass_prod, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod_two_eq_zero_or_one (g i) with h | h
  · rw [h, zero_smul]; exact (if_neg (by decide)).symm
  · rw [h, one_smul]; exact (if_pos rfl).symm

/-- **Square-class independence is `ZMod 2`-linear independence.** For a finite family of units
`d : ι → Kˣ`, the square classes `squareClass (d i)` are `ZMod 2`-linearly independent in the
square-class group iff no nonempty subset product `∏_{i ∈ S} d i` is a square. The right-hand side
is the Finset form of square-class independence that the multiquadratic degree theorem consumes. -/
theorem linearIndependent_squareClass_iff {ι : Type*} [Finite ι] (d : ι → Kˣ) :
    LinearIndependent (ZMod 2) (fun i => squareClass (d i)) ↔
      ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i) := by
  classical
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  constructor
  · -- A nonempty square subset product would give a nontrivial linear dependence.
    intro H S hS hsq
    set g : ι → ZMod 2 := fun i => if i ∈ S then 1 else 0 with hg
    have hfilter : Finset.univ.filter (fun i => g i = 1) = S := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨-, hi⟩
        by_contra hiS
        rw [hg] at hi
        simp only [hiS, if_false] at hi
        exact absurd hi (by decide)
      · intro hiS
        exact ⟨Finset.mem_univ i, by rw [hg]; simp [hiS]⟩
    have hsum : ∑ i, g i • squareClass (d i) = 0 := by
      rw [sum_smul_squareClass, hfilter, squareClass_eq_zero_iff]
      exact hsq
    obtain ⟨i, hiS⟩ := hS
    have hi0 := H g hsum i
    rw [hg] at hi0
    simp only [hiS, if_true] at hi0
    exact absurd hi0 (by decide)
  · -- A linear dependence singles out a nonempty square subset product.
    intro H g hsum i
    by_contra hgi
    have hg1 : g i = 1 := (zmod_two_eq_zero_or_one (g i)).resolve_left hgi
    set S : Finset ι := Finset.univ.filter (fun j => g j = 1) with hS
    have hiS : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hg1⟩
    rw [sum_smul_squareClass, squareClass_eq_zero_iff] at hsum
    exact H S ⟨i, hiS⟩ hsum

end TauCeti
