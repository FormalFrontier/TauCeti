/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FieldPoints
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius
public import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# The Frobenius-fixed points of the type-A carrier

`TauCeti.SlStd.groupScheme r` is the explicit full-weight Chevalley carrier of type `A_r`, and
`TauCeti.SlStd.frobenius r p k K` is the `p ^ k`-power Frobenius endomorphism of its point group
over a field `K` of exponential characteristic `p`. This file identifies the subgroup that
endomorphism fixes: writing `𝔽` for the Frobenius-fixed subfield
`TauCeti.frobeniusFixedSubfield K p k`, it is `SL_{r+1}(𝔽)`.

Two results on `main` come close without pinning the fixed group down.
`TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq` says the fixed points are the carrier's
points over the Frobenius-fixed *subring*, which is a statement about the carrier and not about a
matrix group; `TauCeti.SlStd.points_eq_range_toGL` identifies the carrier's points over a field
with `SL_{r+1}` of that field, but says nothing about a Frobenius. Composing them needs the
observation that over a field the fixed subring is a subfield, which is
`TauCeti.toSubring_frobeniusFixedSubfield`, and the composite is what turns the fixed group into
an explicit matrix group.

The consequence that makes the construction worth performing is finiteness: over a field of
characteristic `p` and for `k ≠ 0` the subfield `𝔽` is finite, so the fixed group is a finite
matrix group. For `p` prime, `k ≠ 0` and `K` separably closed of characteristic `p`, `𝔽` has
exactly `p ^ k` elements by `TauCeti.card_frobeniusFixedSubfield`, so that group is `SL_{r+1}(q)`
with `q = p ^ k`. The isomorphism `𝔽 ≃+* GaloisField p k` is not canonical, so nothing below
phrases the fixed group over `GaloisField p k`.

At `k = 0` the fixed subfield is all of `K` and the statements degenerate to
`TauCeti.SlStd.points_eq_range_toGL`, which is correct rather than vacuous: the zeroth Frobenius
iterate is the identity and fixes every point.

Nothing here asserts that the carrier is reductive, that the fixed group is perfect or simple, or
that it is isomorphic to any other construction of a finite group of Lie type. The corresponding
statement for the graph-twisted Frobenius is not a corollary of anything below: that map couples
the matrix entries, so its fixed set is not the points over a subfield.

## Main definitions

* `TauCeti.SlStd.specialLinearToFixedSubgroupFrobenius`: the homomorphism from `SL_{r+1}(𝔽)` to the
  Frobenius-fixed points of the type-`A_r` carrier, given by including the matrix entries.
* `TauCeti.SlStd.specialLinearMulEquivFixedSubgroupFrobenius`: it is an isomorphism.

## Main results

* `TauCeti.SlStd.mem_fixedSubgroup_frobenius_iff`: a carrier point is Frobenius-fixed exactly when
  all of its matrix entries lie in the Frobenius-fixed subfield.
* `TauCeti.SlStd.mapGL_mem_fixedSubgroup_frobenius` and
  `TauCeti.SlStd.exists_mapGL_eq_of_mem_fixedSubgroup_frobenius`: the two directions of the
  identification, before it is packaged as a homomorphism.
* `TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq_range_mapGL`: read inside `GL_{r+1}(K)`,
  the Frobenius-fixed points are exactly the image of `SL_{r+1}(𝔽)`, and
  `TauCeti.SlStd.mem_map_subtype_fixedSubgroup_frobenius_iff` is the entrywise form of that: they
  are the invertible matrices of determinant one with entries in `𝔽`.
* `TauCeti.SlStd.finite_fixedSubgroup_frobenius` and
  `TauCeti.SlStd.finite_fixedSubgroup_frobenius_of_charP`: the fixed group is finite.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances the target "points over an algebraically closed field as a group, functorially in
the field, so that a field endomorphism induces a group endomorphism of the points. The `q`-power
Frobenius is the case a consumer asks for first" in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, by saying which points that endomorphism fixes. Its
consumer is milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`, which sets `H_d` to be the
fixed subgroup of the Steinberg map of a valid Lie-type index; on the untwisted type-`A` branch
the Steinberg map is the Frobenius, and this says what `H_d` is there.
-/

public section

namespace TauCeti.SlStd

universe u

variable (r p k : ℕ) {K : Type u} [Field K]

noncomputable section

section

variable [ExpChar K p]

/-! ## The fixed points as matrices over the fixed subfield -/

/-- **A type-`A_r` carrier point over a field is fixed by the `p ^ k`-power Frobenius exactly when
all of its matrix entries lie in the Frobenius-fixed subfield.** This is
`TauCeti.SlStd.frobenius_eq_self_iff` read over a field, where the fixed subring is a subfield. -/
theorem mem_fixedSubgroup_frobenius_iff (g : points r K) :
    g ∈ fixedSubgroup (frobenius r p k K) ↔
      ∀ i j, ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K) i j ∈ frobeniusFixedSubfield K p k := by
  rw [mem_fixedSubgroup, frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, mem_frobeniusFixedSubfield]

/-- **The image of a determinant-one matrix over the Frobenius-fixed subfield is a Frobenius-fixed
carrier point**: its entries lie in the fixed subfield by construction. -/
theorem mapGL_mem_fixedSubgroup_frobenius
    (x : Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k)) :
    (⟨Matrix.SpecialLinearGroup.mapGL K x, toGL_mem_points r _⟩ : points r K) ∈
      fixedSubgroup (frobenius r p k K) := by
  rw [mem_fixedSubgroup_frobenius_iff]
  intro i j
  exact (x i j).2

/-- **The homomorphism from `SL_{r+1}` over the Frobenius-fixed subfield to the Frobenius-fixed
points of the full-weight type-`A_r` carrier**, given by including the matrix entries into `K`.

`TauCeti.SlStd.coe_specialLinearToFixedSubgroupFrobenius` below, which says that the underlying
general linear matrix is the entrywise inclusion, is the whole content of the definition. -/
def specialLinearToFixedSubgroupFrobenius :
    Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k) →*
      ↥(fixedSubgroup (frobenius r p k K)) :=
  MonoidHom.codRestrict
    (MonoidHom.codRestrict (Matrix.SpecialLinearGroup.mapGL (n := Fin (r + 1))
      (R := ↥(frobeniusFixedSubfield K p k)) K) (points r K) (fun _ => toGL_mem_points r _))
    (fixedSubgroup (frobenius r p k K)) (mapGL_mem_fixedSubgroup_frobenius r p k)

/-- The general linear matrix underlying the image of `x` is the entrywise inclusion of `x`. -/
@[simp]
theorem coe_specialLinearToFixedSubgroupFrobenius
    (x : Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k)) :
    ((specialLinearToFixedSubgroupFrobenius r p k x : points r K) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) K) =
      Matrix.SpecialLinearGroup.mapGL K x := by
  -- `specialLinearToFixedSubgroupFrobenius` is not `@[expose]`d, so its body is reached through
  -- its equation lemma rather than by definitional unfolding.
  rw [specialLinearToFixedSubgroupFrobenius]
  rfl

/-! ## Bijectivity -/

/-- Including the entries of a determinant-one matrix into `K` loses nothing. -/
private theorem specialLinearToFixedSubgroupFrobenius_injective :
    Function.Injective (specialLinearToFixedSubgroupFrobenius r p k (K := K)) := by
  intro x y hxy
  apply Matrix.SpecialLinearGroup.mapGL_injective (n := Fin (r + 1)) (S := K)
  rw [← coe_specialLinearToFixedSubgroupFrobenius r p k x,
    ← coe_specialLinearToFixedSubgroupFrobenius r p k y, hxy]

/-- **Every Frobenius-fixed carrier point comes from a determinant-one matrix over the
Frobenius-fixed subfield.** Its entries lie in that subfield, and its determinant is one there
because the inclusion into `K` is injective. -/
theorem exists_mapGL_eq_of_mem_fixedSubgroup_frobenius {g : points r K}
    (hg : g ∈ fixedSubgroup (frobenius r p k K)) :
    ∃ x : Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k),
      Matrix.SpecialLinearGroup.mapGL K x =
        (g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) := by
  have hmem := (mem_fixedSubgroup_frobenius_iff r p k g).mp hg
  set N : Matrix (Fin (r + 1)) (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k) :=
    fun i j => ⟨_, hmem i j⟩
  -- Including the entries of `N` back into `K` returns the original matrix.
  have hmap : N.map (frobeniusFixedSubfield K p k).subtype =
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K) := rfl
  -- The determinant of `N` is one, since it is one after the injective inclusion into `K`.
  have hdet : N.det = 1 := by
    have hdet' : ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) K).det = 1 := by
      simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
        congrArg Units.val ((mem_points_iff_det_eq_one r _).mp g.2)
    apply (frobeniusFixedSubfield K p k).subtype_injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hdet', map_one]
  refine ⟨⟨N, hdet⟩, ?_⟩
  ext i j
  -- entry by entry this is `hmap`, since `mapGL` acts by the entrywise inclusion
  rfl

/-- Every Frobenius-fixed carrier point is in the image. -/
private theorem specialLinearToFixedSubgroupFrobenius_surjective :
    Function.Surjective (specialLinearToFixedSubgroupFrobenius r p k (K := K)) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx⟩ := exists_mapGL_eq_of_mem_fixedSubgroup_frobenius r p k hg
  refine ⟨x, ?_⟩
  -- the target is a subgroup of the carrier points, which are a subgroup of `GL_{r+1}(K)`
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_specialLinearToFixedSubgroupFrobenius, hx]

/-- The homomorphism onto the Frobenius-fixed points is bijective. Consumers should read this off
`TauCeti.SlStd.specialLinearMulEquivFixedSubgroupFrobenius` instead. -/
private theorem specialLinearToFixedSubgroupFrobenius_bijective :
    Function.Bijective (specialLinearToFixedSubgroupFrobenius r p k (K := K)) :=
  ⟨specialLinearToFixedSubgroupFrobenius_injective r p k,
    specialLinearToFixedSubgroupFrobenius_surjective r p k⟩

/-- **The Frobenius-fixed points of the full-weight type-`A_r` carrier over a field are
`SL_{r+1}` over the Frobenius-fixed subfield.** For `p` prime, `k ≠ 0` and `K` separably closed of
characteristic `p`, the subfield is the field of `p ^ k` elements, so this is the finite group
`SL_{r+1}(q)`.

`TauCeti.SlStd.specialLinearMulEquivFixedSubgroupFrobenius_apply` below identifies the underlying
map with `TauCeti.SlStd.specialLinearToFixedSubgroupFrobenius`, and hence gives the matrix
description of the isomorphism. -/
def specialLinearMulEquivFixedSubgroupFrobenius :
    Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k) ≃*
      ↥(fixedSubgroup (frobenius r p k K)) :=
  MulEquiv.ofBijective _ (specialLinearToFixedSubgroupFrobenius_bijective r p k)

/-- The isomorphism is the homomorphism it is built from. -/
@[simp]
theorem specialLinearMulEquivFixedSubgroupFrobenius_apply
    (x : Matrix.SpecialLinearGroup (Fin (r + 1)) ↥(frobeniusFixedSubfield K p k)) :
    specialLinearMulEquivFixedSubgroupFrobenius r p k x =
      specialLinearToFixedSubgroupFrobenius r p k x := by
  rw [specialLinearMulEquivFixedSubgroupFrobenius]
  rfl

/-! ## The fixed points inside the general linear group -/

/-- **Read inside `GL_{r+1}(K)`, the Frobenius-fixed points of the full-weight type-`A_r` carrier
are exactly the image of `SL_{r+1}` over the Frobenius-fixed subfield.** This is the subgroup form
of `TauCeti.SlStd.specialLinearMulEquivFixedSubgroupFrobenius`, and refines
`TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq` from the carrier's points over the fixed
subring to a matrix group. -/
theorem map_subtype_fixedSubgroup_frobenius_eq_range_mapGL :
    (fixedSubgroup (frobenius r p k K)).map (points r K).subtype =
      (Matrix.SpecialLinearGroup.mapGL (n := Fin (r + 1))
        (R := ↥(frobeniusFixedSubfield K p k)) K).range := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact exists_mapGL_eq_of_mem_fixedSubgroup_frobenius r p k hy
  · rintro ⟨x, rfl⟩
    exact ⟨specialLinearToFixedSubgroupFrobenius r p k x,
      (specialLinearToFixedSubgroupFrobenius r p k x).2, rfl⟩

/-- **Which matrices the Frobenius-fixed points of the type-`A_r` carrier consist of**: an
invertible matrix over `K` is one exactly when its determinant is one and its entries lie in the
Frobenius-fixed subfield. This is the entrywise reading of
`TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq_range_mapGL`. -/
theorem mem_map_subtype_fixedSubgroup_frobenius_iff
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) :
    g ∈ (fixedSubgroup (frobenius r p k K)).map (points r K).subtype ↔
      Matrix.GeneralLinearGroup.det g = 1 ∧
        ∀ i j, (g : Matrix (Fin (r + 1)) (Fin (r + 1)) K) i j ∈ frobeniusFixedSubfield K p k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(mem_points_iff_det_eq_one r _).mp y.2,
      (mem_fixedSubgroup_frobenius_iff r p k y).mp hy⟩
  · rintro ⟨hdet, hmem⟩
    exact ⟨⟨g, (mem_points_iff_det_eq_one r g).mpr hdet⟩,
      (mem_fixedSubgroup_frobenius_iff r p k _).mpr hmem, rfl⟩

/-! ## Finiteness -/

/-- The Frobenius-fixed points of the type-`A_r` carrier form a finite group as soon as the
Frobenius-fixed subfield is finite. -/
theorem finite_fixedSubgroup_frobenius [Finite ↥(frobeniusFixedSubfield K p k)] :
    Finite ↥(fixedSubgroup (frobenius r p k K)) :=
  .of_equiv _ (specialLinearMulEquivFixedSubgroupFrobenius r p k).toEquiv

end

/-- **The Frobenius-fixed points of the type-`A_r` carrier over a field of characteristic `p` form
a finite group**, for every nonzero exponent: the Frobenius-fixed subfield is a set of roots of
`X ^ p ^ k - X`, hence finite.

Separable closedness is not needed for finiteness, only for the count: when `K` is separably closed
the subfield has exactly `p ^ k` elements by `TauCeti.card_frobeniusFixedSubfield`, so the fixed
group is `SL_{r+1}(q)` with `q = p ^ k`, while over an arbitrary field of characteristic `p` it is
`SL_{r+1}` of a possibly smaller finite field. This is the first point at which the construction
produces a finite group; no order formula, perfectness or simplicity statement is claimed. -/
theorem finite_fixedSubgroup_frobenius_of_charP [Fact p.Prime] [CharP K p]
    (hk : k ≠ 0) : Finite ↥(fixedSubgroup (frobenius r p k K)) :=
  have : Finite ↥(frobeniusFixedSubfield K p k) := finite_frobeniusFixedSubfield K p k hk
  finite_fixedSubgroup_frobenius r p k

end

end TauCeti.SlStd
