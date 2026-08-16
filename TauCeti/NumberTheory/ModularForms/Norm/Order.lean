/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing
import TauCeti.NumberTheory.ModularForms.Norm.Trace
import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.NumberTheory.ModularForms.Order.Orbits

/-!
# Orders along the norm map

The general-level valence formula reads the level-one formula off the norm
`ModularForm.norm`, so it needs the orders of a form to distribute over the norm's coset
product. This file records that distribution at interior points, for a form on any subgroup
of finite relative index: each coset factor is nonzero when the form is, and the vanishing
order of the norm is the sum of the orders of the factors.

## Main declarations

* `TauCeti.SlashInvariantForm.quotientFunc_ne_zero`: a coset factor of the norm of a nonzero
  form is nonzero.
* `TauCeti.ModularForm.orderOfVanishingAt_norm`: the vanishing order of the norm at a point
  is the sum, over the coset space, of the vanishing orders of the coset factors.
* `TauCeti.ModularForm.orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm`: each coset
  factor vanishes to at most the order the norm does, with
  `TauCeti.ModularForm.orderOfVanishingAt_le_orderOfVanishingAt_norm` as the identity-coset
  corollary — so the zeros of the norm dominate those of the form.
* `TauCeti.ModularForm.finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup`: the
  consumer of that domination — at any level of finite relative index in `𝒮ℒ`, the image in
  `𝒢 \ ℍ` of the points at which a form has nonzero vanishing order is finite. Equivalently,
  those points meet only finitely many `𝒢`-orbits.

## References

* The two-step route used here — order domination under the norm carries the support into the
  finite support of the level-one norm, and finite index makes the fibres of the orbit comparison
  finite — was arrived at independently of, and concurrently with,
  [PR #3330](https://github.com/TauCetiProject/TauCeti/pull/3330), which gives the same argument
  for a subgroup of `SL(2, ℤ)` of finite index. That work has since landed; nothing here depends
  on it, and the two remain independent derivations rather than one building on the other.

  The statements differ in the group: this one takes `𝒢 ≤ GL (Fin 2) ℝ` of finite *relative* index
  in `𝒮ℒ`, which **need not lie inside `𝒮ℒ`**. That is also why the order is not descended to the
  quotient here — `𝒢` may contain elements of negative determinant, under which the vanishing
  order is not known to be invariant (`orderOfVanishingAt_smul` asks for `0 < det`) — so only the
  image of the nonzero-order set in `𝒢 \ ℍ` is claimed, not an order function on it.
-/

open UpperHalfPlane

open scoped ModularForm MatrixGroups

namespace TauCeti

noncomputable section

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace SlashInvariantForm

/-- A coset factor of the norm of a nonzero form is nonzero: the factor is a slash translate
of the form, and the slash action of a group element kills only `0`. -/
public lemma quotientFunc_ne_zero [SlashInvariantFormClass F 𝒢 k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    _root_.SlashInvariantForm.quotientFunc f q ≠ 0 := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [_root_.SlashInvariantForm.quotientFunc_mk]
    exact fun hzero ↦ hf ((SlashAction.slash_eq_zero_iff k g.val⁻¹ (⇑f : ℍ → ℂ)).1 hzero)

end SlashInvariantForm

namespace ModularForm

variable [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]

/-- The vanishing order of the norm at an interior point is the sum of the vanishing orders
of its coset factors. -/
public lemma orderOfVanishingAt_norm (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (p : ℍ) :
    orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p =
      ∑ᶠ q : ℋ ⧸ 𝒢.subgroupOf ℋ,
        orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p := by
  let _ : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, _root_.ModularForm.coe_norm]
  exact orderOfVanishingAt_prod
    (fun q _ ↦ SlashInvariantForm.mdifferentiable_quotientFunc f q)
    (fun q _ ↦ SlashInvariantForm.quotientFunc_ne_zero hf q) p

/-- Each coset factor of the norm of a form vanishes at a point to at most the order the norm
itself does. -/
public lemma orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm (f : F)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) (p : ℍ) :
    orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p ≤
      orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · -- Every coset factor of the zero form is zero, and so is its norm.
    have hq : _root_.SlashInvariantForm.quotientFunc f q = 0 :=
      Quotient.inductionOn q fun g ↦ (SlashAction.slash_eq_zero_iff k g.val⁻¹ _).2 hf
    simp [hq, (_root_.ModularForm.norm_eq_zero_iff ℋ f).mpr hf]
  · rw [orderOfVanishingAt_norm f hf p]
    exact single_le_finsum q (Set.toFinite _) fun r ↦
      orderOfVanishingAt_nonneg (SlashInvariantForm.mdifferentiable_quotientFunc f r) p

/-- The norm vanishes at a point to at least the order the form itself does: the zeros of the
norm dominate the zeros of the form. -/
public lemma orderOfVanishingAt_le_orderOfVanishingAt_norm (f : F) (p : ℍ) :
    orderOfVanishingAt (⇑f) p ≤ orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p := by
  -- The form is the factor at the identity coset. That coset space is not a group —
  -- `𝒢.subgroupOf ℋ` need not be normal — so the identity coset is spelled `⟦1⟧`, not `1`.
  simpa using orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm f
    (⟦1⟧ : ℋ ⧸ 𝒢.subgroupOf ℋ) p

-- Step 1: the nonzero-order points meet only finitely many `SL(2, ℤ)`-orbits, which is the
-- level-one finite-support statement read through the norm.
private lemma finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] [ModularFormClass F 𝒢 k] (f : F) :
    Set.Finite ((Quotient.mk'' : ℍ → MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ''
      {p : ℍ | orderOfVanishingAt f p ≠ 0}) := by
  -- pass to the norm: a level-one form, so only finitely many orbits carry nonzero order
  refine (hasFiniteSupport_orderOfVanishingOnOrbit (_root_.ModularForm.norm 𝒮ℒ f)).subset ?_
  rintro q ⟨p, hp, rfl⟩
  -- a nonzero order is positive, and the norm's order dominates it, so the norm's is nonzero
  simpa only [Function.mem_support, orderOfVanishingOnOrbit_mk] using
    (((orderOfVanishingAt_nonneg (ModularFormClass.holo f) p).lt_of_ne' hp).trans_le
      (orderOfVanishingAt_le_orderOfVanishingAt_norm f p)).ne'

-- `𝒮ℒ` is by definition the image of `SL(2, ℤ)` in `GL (Fin 2) ℝ`, and the action factors
-- through it, so the two orbits of a point are the same subset of `ℍ`.
private lemma orbit_sl_eq_orbit_slGL (z : ℍ) :
    MulAction.orbit SL(2, ℤ) z = MulAction.orbit 𝒮ℒ z := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ g, ⟨g, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨_, g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

-- Step 2, and the crux: a single `SL(2, ℤ)`-orbit meets only finitely many `𝒢`-orbits. This is
-- purely group-theoretic — `𝒢 ⊓ 𝒮ℒ` is a finite-index subgroup of `𝒮ℒ`, so it cuts the
-- pretransitive `𝒮ℒ`-orbit into finitely many pieces, and each piece lies in one `𝒢`-orbit.
private lemma finite_image_orbit_mk_orbit (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex 𝒮ℒ] (z : ℍ) :
    Set.Finite ((Quotient.mk'' : ℍ → MulAction.orbitRel.Quotient 𝒢 ℍ) ''
      MulAction.orbit SL(2, ℤ) z) := by
  rw [orbit_sl_eq_orbit_slGL]
  have : Finite (MulAction.orbitRel.Quotient (𝒢.subgroupOf 𝒮ℒ) (MulAction.orbit 𝒮ℒ z)) :=
    Subgroup.finite_quotient_of_pretransitive_of_index_ne_zero Subgroup.relIndex_ne_zero
  -- the `𝒢`-class of a point of the orbit depends only on its `𝒢 ⊓ 𝒮ℒ`-piece
  set F : MulAction.orbitRel.Quotient (𝒢.subgroupOf 𝒮ℒ) (MulAction.orbit 𝒮ℒ z) →
      MulAction.orbitRel.Quotient 𝒢 ℍ :=
    fun q ↦ Quotient.liftOn' q (fun p ↦ Quotient.mk'' p.val) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨h, hh⟩
      have hval : ((h : ↥𝒮ℒ) : GL (Fin 2) ℝ) • b = a := congrArg Subtype.val hh
      exact Quotient.sound' ⟨(⟨((h : ↥𝒮ℒ) : GL (Fin 2) ℝ), h.2⟩ : ↥𝒢), hval⟩) with hF
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨Quotient.mk'' ⟨p, hp⟩, rfl⟩

/-- **At any level of finite relative index in `𝒮ℒ`, the nonzero-order points of a form meet
only finitely many `𝒢`-orbits**: the image in `𝒢 \ ℍ` of `{p | orderOfVanishingAt f p ≠ 0}` is
finite.

⚠ This is *not* stated as finite support of an order divisor on `𝒢 \ ℍ`, and cannot be: no order
function descends to that quotient here, because `𝒢` need not lie inside `𝒮ℒ` and its
negative-determinant elements are not known to preserve the order. The claim is about the image
of a set of points, nothing more.

The nonzero-order set is covered by the finitely many `SL(2, ℤ)`-orbits its points lie on, and
each of those meets only finitely many `𝒢`-orbits. -/
public lemma finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero_subgroup
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] [ModularFormClass F 𝒢 k] (f : F) :
    Set.Finite ((Quotient.mk'' : ℍ → MulAction.orbitRel.Quotient 𝒢 ℍ) ''
      {p : ℍ | orderOfVanishingAt f p ≠ 0}) := by
  refine ((finite_image_orbit_mk_setOf_orderOfVanishingAt_ne_zero f).biUnion
    (t := fun q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ ↦
      (Quotient.mk'' : ℍ → MulAction.orbitRel.Quotient 𝒢 ℍ) '' q.orbit)
    fun q _ ↦ ?_).subset ?_
  · induction q using Quotient.inductionOn' with
    | _ p => simpa [MulAction.orbitRel.Quotient.orbit_mk] using finite_image_orbit_mk_orbit 𝒢 p
  · rintro _ ⟨p, hp, rfl⟩
    exact Set.mem_biUnion ⟨p, hp, rfl⟩ ⟨p, by simp, rfl⟩

end ModularForm

end

end TauCeti
