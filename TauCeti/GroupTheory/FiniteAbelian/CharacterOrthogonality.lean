/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Column orthogonality for characters of a finite commutative group

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — in both its punctured and its normal form.

## Main results

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.sum_monoidHom_apply_eq_ite`: the same sum in normal form, `Nat.card G` at `g = 1`
  and `0` elsewhere. This is the shape an indicator-formula consumer wants, and it is the `simp`
  normal form for such a sum.

The file also registers `Fintype (G →* Mˣ)`, which Mathlib leaves at `Finite`; without it a
consumer's own character sum does not elaborate, and two ad-hoc `Fintype.ofFinite` introductions
give syntactically distinct sums. That instance needs only `LeftCancelMonoid G`, so it also serves
consumers indexing over the characters of a finite noncommutative group or monoid.

## Row orthogonality is Mathlib's, and is deliberately not restated here

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the analogous statement in the `MulChar`
vocabulary, for a multiplicative character of a finite commutative monoid valued in a domain.)

The column relation genuinely is not in Mathlib in this generality. It appears there only in
specialisations: the `ZMod n` one, `DirichletCharacter.sum_characters_eq_zero` in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`, and the finite-additive-group one
over `ℂ`, `AddChar.sum_apply_eq_ite` in
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` (with
`AddChar.sum_apply_eq_zero_iff_ne_zero` beside it). Neither implies the statement below, which is
multiplicative and valued in an arbitrary domain with enough roots of unity rather than in `ℂ`
or over `ZMod n`.

## References

Only `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one` is adapted from elsewhere: it comes from
`sum_char_apply_eq_zero_of_ne_one` in `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`
of [CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`.
-/

public section

variable {G : Type*} [Finite G] {M : Type*} [CommRing M] [IsDomain M]

/-- The characters of a finite left-cancellative monoid valued in a domain form a `Fintype`.
Mathlib registers only `Finite (G →* Mˣ)`, so a character sum written by a consumer has no
`Finset` to range over without this; it mirrors `AddChar.instFintype`. Neither commutativity nor
invertibility is needed: `Finite (G →* Mˣ)` already holds at `LeftCancelMonoid`, which is where
this is stated. -/
noncomputable instance instFintypeMonoidHomUnits [LeftCancelMonoid G] : Fintype (G →* Mˣ) :=
  Fintype.ofFinite _

namespace CommGroup

variable [CommGroup G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_monoidHom_apply_eq_zero_of_ne_one {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, (χ g : M) = 0 := by
  -- A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
  -- evaluation homomorphism `χ ↦ χ g`.
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp (MonoidHom.eval g))
    fun h ↦ hχ₀ <| Units.val_eq_one.mp <| DFunLike.congr_fun h χ₀

/-- **Column orthogonality in normal form**: the character sum is `Nat.card G` at the identity
and vanishes elsewhere. This covers both cases at once, and states the identity value as the
cardinality of `G` itself rather than of its dual, which is the shape an indicator-formula
consumer wants. -/
@[simp]
theorem sum_monoidHom_apply_eq_ite [DecidableEq G] (g : G) :
    ∑ χ : G →* Mˣ, (χ g : M) = if g = 1 then (Nat.card G : M) else 0 := by
  split
  · next hg =>
    subst hg
    -- the dual of `G` has the cardinality of `G`, by Mathlib's character duality
    have hcard : Fintype.card (G →* Mˣ) = Nat.card G := by
      simpa using card_monoidHom_of_hasEnoughRootsOfUnity G M
    simp [hcard]
  · next hg => exact sum_monoidHom_apply_eq_zero_of_ne_one hg

end CommGroup
