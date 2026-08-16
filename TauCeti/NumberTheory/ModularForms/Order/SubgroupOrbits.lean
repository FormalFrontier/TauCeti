/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import TauCeti.NumberTheory.ModularForms.Norm.Order

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
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 g.2
    have hg' : g • b = _ := hg
    rw [← hg', Subgroup.smul_def,
      orderOfVanishingAt_smul f g.2
        (by rw [← hγ, ← Matrix.GeneralLinearGroup.val_det_apply,
          Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at `p`. -/
@[simp]
public lemma orderOfVanishingOnSubgroupOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (p : ℍ) :
    orderOfVanishingOnSubgroupOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnSubgroupOrbit
  rfl

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

end ModularForm

end TauCeti

end
