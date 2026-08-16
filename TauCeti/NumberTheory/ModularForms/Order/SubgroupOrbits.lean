/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.NumberTheory.ModularForms.Norm.Order

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The order divisor at general level, on the orbit space

For a subgroup `Γ ≤ SL(2, ℤ)`, the vanishing order of a modular form on `Γ` is constant on
`Γ`-orbits of the upper half-plane: every element of `Γ` acts through a matrix of determinant
`1`, and the order is invariant along positive-determinant elements of the group of the form.
This file descends the order to the orbit space `Γ \ ℍ` and records that, for `Γ` of finite
index, only finitely many orbits carry nonzero order — the summation index of the general-level
valence formula.

The orbit space is spelled `MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ`, the
index type the rest of the general-level API already uses; the `Γ`-orbits and the orbits of the
image of `Γ` in `GL (Fin 2) ℝ` are the same subsets of `ℍ`.

Because that is an ordinary `MulAction.orbitRel.Quotient`, the *other* function the valence
formula indexes over it — the stabiliser order — needs no modular-specific definition at all:
`TauCeti.cardStabilizerOnOrbit` in `GroupTheory/GroupAction/Stabilizer.lean` applies to this
quotient directly. Only the vanishing order, below, needs the determinant-`1` argument that
makes it well defined here.

The finiteness is not reproved here. It is
`TauCeti.ModularForm.finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup`, which
bounds the image of the nonzero-order set in `𝒢 \ ℍ` for any `𝒢 ≤ GL (Fin 2) ℝ` of finite
relative index in `𝒮ℒ`, by the norm-map route of the Tau Ceti ModularForms roadmap's Layer 1
milestone **“General level — by the coset norm”**. What this file adds is the order *function*
on the quotient, which that statement deliberately does not provide: a general `𝒢` may contain
elements of negative determinant, under which the order is not known to be invariant, while the
image of a subgroup of `SL(2, ℤ)` has determinant `1` throughout.

## Main declarations

* `TauCeti.ModularForm.orderOfVanishingOnSubgroupOrbit`: the order descended to the
  `Γ`-orbit space.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnSubgroupOrbit`: finite support of
  the interior order divisor of a general-level modular form.
* `TauCeti.ModularForm.orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit`: a
  coset factor of the norm vanishes at `p` to the order `f` has on the orbit `p` is translated
  into.
* `TauCeti.ModularForm.orderOfVanishingAt_norm_eq_finsum_orbit`: hence the order of the norm at
  `p` is a sum over `Γ \ ℍ`, each orbit weighted by how many cosets translate `p` into it.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the descent here is the
  level-one one, `TauCeti.ModularForm.orderOfVanishingOnOrbit` in `Order/Orbits.lean`, which is
  ported from AINTLIB, transposed from `SL(2, ℤ)` to `Γ`.
* `TauCeti.ModularForm.finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup` in
  `Norm/Order.lean` — the general-`𝒢` form of the norm-map route, arrived at concurrently with
  this file and consumed by it here, rather than reproved.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Chapter 3.
-/

public noncomputable section

open UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- The vanishing order of a form for `Γ ≤ SL(2, ℤ)`, descended to the `Γ`-orbit space of
the upper half-plane. -/
public def orderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (q : MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt f) fun _ b ⟨g, hg⟩ ↦ by
    have hg' : g • b = _ := hg
    rw [← hg', Subgroup.smul_def,
      orderOfVanishingAt_smul f g.2 (det_pos_of_mem_slGL (Subgroup.map_le_range _ _ g.2)) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at `p`. -/
@[simp]
public lemma orderOfVanishingOnSubgroupOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ) :
    orderOfVanishingOnSubgroupOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnSubgroupOrbit
  rfl

/-- **The coset factors of the norm see exactly the orbits of the translates of the point.**
The factor indexed by `q` vanishes at `p` to the order `f` itself has on the orbit into which
`q` translates `p`.

This is what turns the coset sum of `orderOfVanishingAt_norm` into a sum over orbits: the
summand depends on `q` only through `orbitOfCosetTranslate p q`. -/
public lemma orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p =
      orderOfVanishingOnSubgroupOrbit f (orbitOfCosetTranslate p q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    rw [_root_.SlashInvariantForm.quotientFunc_mk, orbitOfCosetTranslate_mk,
      orderOfVanishingOnSubgroupOrbit_mk, orderOfVanishingAt_slash (k := k)]
    -- the slash acts by `h⁻¹`, which lies in `𝒮ℒ` and so has positive determinant
    exact det_pos_of_mem_slGL (inv_mem h.2)

/-- A modular form for a finite-index subgroup `Γ ≤ SL(2, ℤ)` has nonzero vanishing order on
only finitely many `Γ`-orbits in the upper half-plane.

This is the finite-support statement for the interior part of the general-level divisor. As at
level one, the zero form needs no exclusion: its order vanishes identically, so its support is
empty. -/
public theorem hasFiniteSupport_orderOfVanishingOnSubgroupOrbit
    [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (orderOfVanishingOnSubgroupOrbit f).HasFiniteSupport := by
  -- an orbit of nonzero order is the class of a point of nonzero order, so the support sits
  -- inside the image that the general-level finiteness lemma bounds
  refine (finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup f).subset ?_
  intro q hq
  induction q using Quotient.inductionOn' with
  | _ p => exact ⟨p, by simpa using hq, rfl⟩

/-- **The order of the norm at a point, regrouped over the orbit space.** The vanishing order
of `ModularForm.norm 𝒮ℒ f` at `p` is the sum, over the `Γ`-orbits of the upper half-plane, of
the descended order of `f` on the orbit weighted by how many cosets translate `p` into it.

This is the interior half of the general-level valence formula: the left-hand side is a level
one quantity, which the level-one formula evaluates, while the right-hand side is indexed by
`Γ \ ℍ`. The fibre counts become the ramification weights `1 / e_P` once the stabiliser
comparison converts them. -/
public theorem orderOfVanishingAt_norm_eq_finsum_orbit
    [(Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex 𝒮ℒ]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (p : ℍ) :
    orderOfVanishingAt (⇑(_root_.ModularForm.norm 𝒮ℒ f)) p =
      ∑ᶠ o : MulAction.orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        Nat.card {q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ //
          orbitOfCosetTranslate p q = o} • orderOfVanishingOnSubgroupOrbit f o := by
  classical
  have _ : Fintype (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  rw [orderOfVanishingAt_norm f hf p, finsum_eq_sum_of_fintype]
  simp only [orderOfVanishingAt_quotientFunc_eq_orderOfVanishingOnSubgroupOrbit]
  -- `𝒢`/`ℋ` are spelled out because `Finset.univ` is otherwise stuck on a metavariable
  rw [← Finset.sum_fiberwise_of_maps_to' fun q _ ↦ Finset.mem_image_of_mem
      (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (ℋ := 𝒮ℒ) p) (Finset.mem_univ q),
    finsum_eq_sum_of_support_subset _ (s := Finset.image
      (orbitOfCosetTranslate (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (ℋ := 𝒮ℒ) p) Finset.univ) ?_]
  · exact Finset.sum_congr rfl fun o _ ↦ by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro o ho
    by_contra hmem
    have : IsEmpty {q // orbitOfCosetTranslate p q = o} :=
      ⟨fun q ↦ hmem (Finset.mem_coe.2 (Finset.mem_image.2 ⟨q.1, Finset.mem_univ _, q.2⟩))⟩
    exact ho (by simp)

end ModularForm

end TauCeti

end
