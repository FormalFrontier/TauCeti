/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
public import TauCeti.GroupTheory.IndexNSmul

/-!
# The 2-Selmer group, and the Mordell–Weil rank bound it gives

Explicit `2`-descent cuts the square classes `W.M` of the étale algebra down by two kinds of
condition: a global one, that the norm class is trivial (`WeierstrassCurve.Affine.normM`), and a
local one at each place (`WeierstrassCurve.Affine.localCondition`). The subgroup cut out by all
of them is the **2-Selmer group**, and the descent map `μ` lands inside it.

Its value is as an upper bound on the rank: `ker μ = 2 • W(K)`, so `im μ ≅ W(K)/2W(K)`, whose
order is `2 ^ rank W(K) * #W(K)[2]`. Any *finite* subgroup containing `im μ` therefore bounds the
rank, and that is `pow_rank_le_card_of_range_μ_le`, stated for an arbitrary finite `S` rather
than for the Selmer group itself.

Nothing here establishes that the Selmer group is finite, over the arbitrary Dedekind domain and
auxiliary fields used below or otherwise; that is a separate result, and so is any effective
computation of the resulting bound.

## Main definitions

* `WeierstrassCurve.Affine.selmerGroup₂`: the 2-Selmer group of `W` relative to a Dedekind domain
  `R` with fraction field `K` and an auxiliary family `Loc` of `K`-fields — the square classes
  with trivial norm class satisfying the local condition at every finite place of `R` and at
  every member of `Loc`. For a number field this is the classical 2-Selmer group.

## Main results

* `WeierstrassCurve.Affine.range_μ_le_selmerGroup₂`: the image of the descent map lies in the
  2-Selmer group. With `ker_μ_eq` this embeds `W(K)/2W(K)` into it.
* `WeierstrassCurve.Affine.card_range_μ`: `#(im μ) = 2 ^ rank W(K) * #W(K)[2]`.
* `WeierstrassCurve.Affine.pow_rank_le_card_of_range_μ_le`: **the rank bound**, that any finite
  subgroup of `W.M` containing `im μ` bounds `2 ^ rank W(K) * #W(K)[2]` from above.

## Implementation notes

`card_range_μ` is where the rank enters, through
`AddSubgroup.index_range_nsmul_of_fg` (`TauCeti/GroupTheory/IndexNSmul.lean`): the index of
`2 • W(K)` in `W(K)` is `2 ^ rank * #W(K)[2]` for a finitely generated group. Mathlib's
`AddSubgroup.index_range_nsmul` is the free case only, and the torsion factor is exactly what
the rank bound has to carry, so the free case cannot be substituted here.

`pow_rank_le_card_of_range_μ_le` takes `S` and `[Finite S]` as hypotheses rather than using
`selmerGroup₂` directly. The finiteness of the 2-Selmer group is a separate theorem; stating the
bound this way lets it be applied to any finite group known to contain the image, and keeps this
file independent of that finiteness proof.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`), `EllipticCurves/SelmerGroup.lean`,
its `SelmerGroup` section — declarations `selmerGroup₂`, `mem_selmerGroup₂_iff`,
`range_μ_le_selmerGroup₂`, `card_range_μ` and `pow_rank_le_card_of_range_μ_le`.

Two of the source's conventions are dropped in favour of this repository's. Square classes are
spelled `W.M`, the quotient of `W.Aˣ` by the range of `powMonoidHom 2`, following `XSubT.lean`;
the source's local `Units.modPow` abbreviation is not carried, per the convention recorded in
`XSubT.lean` and `LocalCondition.lean`. And there is no `[DecidableEq K]` section variable:
every declaration here is under `open scoped Classical in`, as in `LocalCondition.lean`.

That second choice is forced, not cosmetic. `DecidableEq K` is what Mathlib's `AddCommGroup
W.Point` instance requires, so `μ` carries it as an instance argument (`XSubT.lean`, where it is
a section variable). `range_μ_le_localCondition` lives in `LocalCondition.lean`, which works
under `open scoped Classical`, so the `μ` in its statement is already pinned to
`Classical.propDecidable`. A file that consumes both that lemma and the group structure of
`W.Point` must therefore supply the same instance: with a `DecidableEq K` section variable the
two disagree and `range_μ_le_selmerGroup₂` will not typecheck, and with neither, `AddGroup
W.Point` fails to synthesize at all.
-/

public section

namespace WeierstrassCurve.Affine

open IsDedekindDomain Module

variable {K : Type*} [Field K] (W : Affine K) [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra K (Loc i)]

open scoped Classical in
/-- The **2-Selmer group** of `W`, relative to a Dedekind domain `R` with fraction field `K` and
an auxiliary family `Loc` of `K`-fields: the square classes in the étale algebra that lie in the
kernel of the norm map and satisfy the local conditions at the completions of `K` at all finite
places of `R` and at all members of `Loc`.

For a number field `F`, with `R = 𝓞 F` and `Loc` the family of completions at the infinite
places, this is the classical 2-Selmer group of `W`, the group of everywhere locally solvable
2-coverings of `W`. -/
noncomputable def selmerGroup₂ : Subgroup W.M :=
  (normM (W := W)).ker ⊓ (⨅ v : HeightOneSpectrum R, W.localCondition (v.adicCompletion K))
    ⊓ ⨅ i, W.localCondition (Loc i)

open scoped Classical in
/-- Membership in the 2-Selmer group, unfolded into its three defining conditions. -/
@[simp]
theorem mem_selmerGroup₂_iff {m : W.M} :
    m ∈ W.selmerGroup₂ R Loc ↔ W.normM m = 1 ∧
      (∀ v : HeightOneSpectrum R, m ∈ W.localCondition (v.adicCompletion K)) ∧
      ∀ i, m ∈ W.localCondition (Loc i) := by
  simp [selmerGroup₂, Subgroup.mem_iInf, and_assoc, MonoidHom.mem_ker]

open scoped Classical in
/-- **The image of the descent map lies in the 2-Selmer group.** Since `ker μ = 2 • W(K)`
(`ker_μ_eq`), this identifies `W(K)/2W(K)` with a subgroup of the 2-Selmer group. -/
theorem range_μ_le_selmerGroup₂ : (μ (W := W)).range ≤ W.selmerGroup₂ R Loc :=
  le_inf (le_inf range_μ_le_ker_normM <| le_iInf fun _ ↦ W.range_μ_le_localCondition _) <|
    le_iInf fun _ ↦ W.range_μ_le_localCondition _

open scoped Classical in
/-- **The size of the image of the descent map**, in terms of the rank and the rational
2-torsion: `im μ ≅ W(K)/2W(K)`, which for a finitely generated `W(K)` has order
`2 ^ rank W(K) * #W(K)[2]`. -/
theorem card_range_μ [AddGroup.FG W.Point] :
    Nat.card (μ (W := W)).range =
      2 ^ finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker := by
  rw [← Subgroup.index_ker (μ (W := W)), ker_μ_eq, AddSubgroup.index_toSubgroup,
    AddSubgroup.index_range_nsmul_of_fg _ two_ne_zero]

open scoped Classical in
/-- **The rank bound from a 2-Selmer group**: any subgroup of `W.M` that is finite and contains
the image of `μ` bounds the rank of `W(K)` from above, through
`2 ^ rank W(K) * #W(K)[2] ≤ #S`.

It applies in particular to `S = W.selmerGroup₂ R Loc`, by `range_μ_le_selmerGroup₂`, once that
group is known to be finite; the hypothesis is stated on an arbitrary `S` so that this file does
not depend on the finiteness proof. -/
theorem pow_rank_le_card_of_range_μ_le [AddGroup.FG W.Point] {S : Subgroup W.M} [Finite S]
    (h : (μ (W := W)).range ≤ S) :
    2 ^ finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker ≤ Nat.card S := by
  rw [← W.card_range_μ]
  exact Subgroup.card_le_of_le h

end WeierstrassCurve.Affine
