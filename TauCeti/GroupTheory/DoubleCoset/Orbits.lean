/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Burnside
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets as orbits

For subgroups `H` and `K` of a group `G`, a double coset is an orbit in two ways.

The double coset `KsH` is the preimage in `G` of the `K`-orbit of the coset `sH`
(`TauCeti.preimage_orbit_eq_doubleCoset`), so the partition of `G ⧸ H` into `K`-orbits is the
partition of `G` into `K`-`H` double cosets.

Globally, the diagonal action of `G` on `(G ⧸ H) × (G ⧸ K)` has
orbits in bijection with the double cosets `H \ G / K`: the orbit of `(aH, bK)` is recorded by the
double coset `H a⁻¹ b K`, and every orbit meets the slice `{(H, gK) | g : G}`.

Combining that bijection with Burnside's lemma counts double cosets by a sum of fixed-point
numbers, which is the group-theoretic half of the statement that the permutation character of
`G` on `G ⧸ H` pairs with the permutation character on `G ⧸ K` to `#(H \ G / K)`.

## Main definitions

* `TauCeti.doubleCosetEquivOrbitQuotient`: the bijection
  `H \ G / K ≃ ((G ⧸ H) × (G ⧸ K)) / G`.
* `TauCeti.orbitOfCosetTranslate`: the `𝒢`-orbit a class in `ℋ ⧸ 𝒢.subgroupOf ℋ` translates a
  point into — the index map along which a coset sum is regrouped into an orbit sum.

## Main statements

* `TauCeti.mem_doubleCoset_iff_mk_mem_orbit`: an element lies in `KsH` exactly when its coset
  lies in the `K`-orbit of `sH`.
* `TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer`: the same for an arbitrary action —
  two translates of a point share a `K`-orbit exactly when the translating elements share a
  `K`-`stabilizer` double coset.
* `TauCeti.orbitOfCosetTranslate_eq_iff`: the fibres of that index map are the orbits of
  `stabilizer ℋ p` on `ℋ ⧸ 𝒢.subgroupOf ℋ`, so a fibre count is an orbit-stabiliser count.
* `TauCeti.preimage_orbit_eq_doubleCoset`: the double coset `KsH` is the preimage of the
  `K`-orbit of `sH`.
* `TauCeti.card_doubleCosetQuotient_eq_card_orbitQuotient`: the two sides of that bijection have
  the same cardinality.
* `TauCeti.sum_card_fixedBy_mul_card_fixedBy_eq_card_doubleCosetQuotient_mul_card_group`:
  Burnside's lemma read through that bijection,
  `∑ g, |(G ⧸ H)^g| * |(G ⧸ K)^g| = #(H \ G / K) * |G|`.

## Implementation notes

Mathlib's `DoubleCoset.Quotient (H : Set G) K` takes the two subgroups as sets, and its
representatives multiply as `h * a * k`. The bijection below is built from the slice map
`g ↦ orbit of (H, gK)`, which is surjective because `a • (H, a⁻¹bK) = (aH, bK)`, and injective
because the pair `(aH, bK)` determines `H a⁻¹ b K`.

## References

This supplies the "`⟨Ind_H^G 1, Ind_H^G 1⟩_G = #(H \ G / H)`" item of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` with its group-theoretic
input.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.3.
-/

public section

open MulAction

namespace TauCeti

variable {G : Type*} [Group G]

section SingleCoset

/-- The double coset `KsH` consists exactly of those `x` whose class in `G ⧸ H` lies in the
`K`-orbit of the class of `s`. -/
@[simp]
theorem mem_doubleCoset_iff_mk_mem_orbit (s : G) (H K : Subgroup G) {x : G} :
    x ∈ DoubleCoset.doubleCoset s (K : Set G) (H : Set G) ↔
      ((x : G ⧸ H)) ∈ orbit K ((s : G ⧸ H)) := by
  rw [DoubleCoset.mem_doubleCoset, mem_orbit_iff]
  -- `K` acts on `G ⧸ H` through `Subgroup.subtype K` (`MulAction.mulLeftCosetsCompSubtypeVal`),
  -- so `MulAction.compHom_smul_def` is what turns a `K`-translate back into a `G`-translate.
  constructor
  · rintro ⟨k, hk, h, hh, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [compHom_smul_def (Subgroup.subtype K), Subgroup.coe_subtype, Quotient.smul_coe,
      smul_eq_mul, QuotientGroup.eq]
    simpa [mul_assoc] using hh
  · rintro ⟨k, hkx⟩
    rw [compHom_smul_def (Subgroup.subtype K), Subgroup.coe_subtype, Quotient.smul_coe,
      smul_eq_mul, QuotientGroup.eq] at hkx
    exact ⟨k, k.2, ((k : G) * s)⁻¹ * x, hkx, (mul_inv_cancel_left _ _).symm⟩

/-- The double coset `KsH` is the preimage, under `G → G ⧸ H`, of the `K`-orbit of the coset `sH`.
So the partition of `G` into `K`-`H` double cosets is the partition of `G ⧸ H` into `K`-orbits. -/
theorem preimage_orbit_eq_doubleCoset (s : G) (H K : Subgroup G) :
    QuotientGroup.mk ⁻¹' (orbit K ((s : G ⧸ H)))
      = DoubleCoset.doubleCoset s (K : Set G) (H : Set G) :=
  Set.ext fun _ => (mem_doubleCoset_iff_mk_mem_orbit s H K).symm

end SingleCoset

section Orbits

variable (H K : Subgroup G)

/-- The orbit of the pair of cosets `(H, gK)` under the diagonal action of `G` on
`(G ⧸ H) × (G ⧸ K)`. Every orbit is of this form, and `doubleCosetOrbit_eq_iff` says that the
double coset `HgK` is a complete invariant of it. -/
def doubleCosetOrbit (g : G) : orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)) :=
  Quotient.mk'' (((1 : G) : G ⧸ H), ((g : G) : G ⧸ K))

variable {H K}

/-- Two points of the slice `{(H, gK) | g : G}` lie in the same orbit exactly when their labels
lie in the same double coset. -/
@[simp]
theorem doubleCosetOrbit_eq_iff {a b : G} :
    doubleCosetOrbit H K a = doubleCosetOrbit H K b ↔
      DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [doubleCosetOrbit, doubleCosetOrbit, Quotient.eq'', eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨g, hg⟩
    rw [Prod.ext_iff] at hg
    obtain ⟨hg₁, hg₂⟩ := hg
    have hgH : g ∈ H := by simpa using H.inv_mem (QuotientGroup.eq.mp hg₁)
    refine ⟨g, hgH, (g * b)⁻¹ * a, QuotientGroup.eq.mp hg₂, ?_⟩
    simp [mul_assoc]
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨h, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨QuotientGroup.eq.mpr (by simpa using H.inv_mem hh),
      QuotientGroup.eq.mpr (by simpa [mul_assoc] using hk)⟩

variable (H K)

/-- **Double cosets are orbits.** The double cosets `H \ G / K` are in bijection with the orbits
of `G` acting diagonally on `(G ⧸ H) × (G ⧸ K)`, the double coset of `g` corresponding to the
orbit of `(H, gK)`. -/
noncomputable def doubleCosetEquivOrbitQuotient :
    DoubleCoset.Quotient (H : Set G) K ≃ orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)) :=
  Equiv.ofBijective
    (Quotient.lift (doubleCosetOrbit H K)
      fun _ _ hab => doubleCosetOrbit_eq_iff.mpr (Quotient.sound hab))
    ⟨by
      refine fun x y => Quotient.inductionOn₂ x y fun a b hab => ?_
      exact doubleCosetOrbit_eq_iff.mp hab, by
      refine fun x => Quotient.inductionOn x fun p => ?_
      obtain ⟨x, y⟩ := p
      refine QuotientGroup.induction_on x fun a => QuotientGroup.induction_on y fun b => ?_
      refine ⟨DoubleCoset.mk H K (a⁻¹ * b), Quotient.sound ⟨a⁻¹, ?_⟩⟩
      rw [Prod.ext_iff]
      exact ⟨by simp, by simp⟩⟩

@[simp]
theorem doubleCosetEquivOrbitQuotient_apply_mk (g : G) :
    doubleCosetEquivOrbitQuotient H K (DoubleCoset.mk H K g) = doubleCosetOrbit H K g :=
  -- The parentheses keep this out of `@[defeq]` inference: the proof is `rfl`, but the two sides
  -- are only definitionally equal after unfolding the (unexposed) definitions above.
  (rfl)

/-- The number of double cosets `H \ G / K` is the number of orbits of `G` on
`(G ⧸ H) × (G ⧸ K)`. -/
theorem card_doubleCosetQuotient_eq_card_orbitQuotient :
    Nat.card (DoubleCoset.Quotient (H : Set G) K) =
      Nat.card (orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K))) :=
  Nat.card_congr (doubleCosetEquivOrbitQuotient H K)


section GeneralAction

variable {α : Type*} [MulAction G α]

/-- **Two translates of a point lie in one `K`-orbit exactly when the translating elements lie
in one double coset.** For `K ≤ G` acting on `α` and a point `p`, the `K`-orbits inside the
`G`-orbit of `p` are indexed by the `K`-`stabilizer G p` double cosets.

This is the companion of `mem_doubleCoset_iff_mk_mem_orbit` for an arbitrary action rather than
the action on `G ⧸ H`: taking `H = stabilizer G p` there and transporting along
`MulAction.orbitEquivQuotientStabilizer` gives the same statement. -/
theorem orbitRel_smul_iff_mem_doubleCoset_stabilizer (K : Subgroup G) (p : α) (x y : G) :
    orbitRel K α (x • p) (y • p) ↔
      x ∈ DoubleCoset.doubleCoset y (K : Set G) (stabilizer G p : Set G) := by
  rw [orbitRel_apply, mem_orbit_iff, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k : G), k.2, y⁻¹ * ((k : G)⁻¹ * x), ?_, by simp [mul_assoc]⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, mul_smul, mul_smul, ← hk, Subgroup.smul_def,
      inv_smul_smul, inv_smul_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [Subgroup.smul_def, mul_smul, mul_smul, mem_stabilizer_iff.mp (SetLike.mem_coe.mp hb)]

/-- **The `𝒢`-orbit that a coset translates a point into.** For `𝒢 ≤ ℋ ≤ G` acting on `α` and a
point `p`, a class in `ℋ ⧸ 𝒢.subgroupOf ℋ` determines the `𝒢`-orbit of `h⁻¹ • p`, independently
of the representative `h`.

Well-definedness is the content: another representative is `h * g` with `g ∈ 𝒢`, and
`(h * g)⁻¹ • p = g⁻¹ • (h⁻¹ • p)` lies in the same `𝒢`-orbit. This is the index map along which
a sum over the coset space `ℋ ⧸ 𝒢.subgroupOf ℋ` is regrouped into a sum over `𝒢`-orbits, with
`orbitRel_smul_iff_mem_doubleCoset_stabilizer` identifying its fibres as double cosets. -/
noncomputable def orbitOfCosetTranslate {𝒢 ℋ : Subgroup G} (p : α) (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    orbitRel.Quotient 𝒢 α :=
  Quotient.liftOn' q (fun h ↦ Quotient.mk'' ((h : G)⁻¹ • p))
    fun a b hab ↦ by
      refine Quotient.sound' ?_
      rw [orbitRel_apply, mem_orbit_iff]
      exact ⟨⟨(a : G)⁻¹ * (b : G),
        (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))⟩, by
        simp [Subgroup.smul_def, mul_smul]⟩

/-- Evaluating `orbitOfCosetTranslate` on the class of `h` gives the orbit of `h⁻¹ • p`. -/
-- The two sides are the same term after `Quotient.liftOn'` reduces on a representative. The
-- definition is deliberately not `@[expose]`d, so the parentheses in `(rfl)` keep the
-- definitional step inside this module and leave this lemma as the whole interface for importers.
@[simp]
theorem orbitOfCosetTranslate_mk {𝒢 ℋ : Subgroup G} (p : α) (h : ℋ) :
    orbitOfCosetTranslate (𝒢 := 𝒢) p (⟦h⟧ : ℋ ⧸ 𝒢.subgroupOf ℋ) = Quotient.mk'' ((h : G)⁻¹ • p) :=
  (rfl)

/-- **The fibres of `orbitOfCosetTranslate` are the `stabilizer ℋ p`-orbits.** Two classes have
the same image exactly when they lie in one orbit of the stabilizer of `p`, acting on the coset
space by left translation.

This is the fibre description the definition exists for: it turns a fibre of that index map into
an orbit, so that a fibre count becomes an orbit-stabiliser count via
`MulAction.index_stabilizer`.

`hle : 𝒢 ≤ ℋ` is what puts the translating element back inside `ℋ`: the witness
`orbitRel_smul_iff_mem_doubleCoset_stabilizer` produces lies in `𝒢`, and the stabilising factor
is an element of `ℋ` only once `𝒢` is. -/
theorem orbitOfCosetTranslate_eq_iff {𝒢 ℋ : Subgroup G} (hle : 𝒢 ≤ ℋ) (p : α)
    (q r : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    orbitOfCosetTranslate p q = orbitOfCosetTranslate (𝒢 := 𝒢) p r ↔
      q ∈ MulAction.orbit (stabilizer ℋ p) r := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    induction r using QuotientGroup.induction_on with
    | H b =>
      rw [orbitOfCosetTranslate_mk, orbitOfCosetTranslate_mk, Quotient.eq'',
        orbitRel_smul_iff_mem_doubleCoset_stabilizer, DoubleCoset.mem_doubleCoset, mem_orbit_iff]
      constructor
      · rintro ⟨x, hx, y, hy, hr⟩
        -- `y` lies in `ℋ`: solving `hr` gives `y = b * x⁻¹ * a⁻¹`, and `𝒢 ≤ ℋ` puts `x` there
        have hyH : y ∈ ℋ := by
          have hy2 : y = (b : G) * x⁻¹ * (a : G)⁻¹ := by rw [hr]; simp [mul_assoc]
          exact hy2 ▸ mul_mem (mul_mem b.2 (inv_mem (hle (SetLike.mem_coe.1 hx)))) (inv_mem a.2)
        have ha : (a : G) = y⁻¹ * (b : G) * x⁻¹ := by
          rw [← inv_inv (a : G), hr]; simp [mul_assoc]
        refine ⟨⟨(⟨y, hyH⟩ : ℋ)⁻¹, inv_mem ((Subgroup.mem_subgroupOf (H := stabilizer G p)).2
          (SetLike.mem_coe.1 hy))⟩, ?_⟩
        -- the action is left translation (the idiom at `mem_doubleCoset_iff_mk_mem_orbit`), so
        -- the goal is a coset equality, with witness `x⁻¹`
        rw [compHom_smul_def (Subgroup.subtype (stabilizer ℋ p)), Subgroup.coe_subtype,
          Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hval : ((((⟨y, hyH⟩ : ℋ)⁻¹ * b)⁻¹ * a : ℋ) : G) = x⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, ha]
          simp [mul_assoc]
        exact hval ▸ SetLike.mem_coe.1 (inv_mem hx)
      · rintro ⟨s, hs⟩
        rw [compHom_smul_def (Subgroup.subtype (stabilizer ℋ p)), Subgroup.coe_subtype,
          Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hs
        refine ⟨(((((s : ℋ) * b)⁻¹ * a : ℋ)⁻¹ : ℋ) : G), SetLike.mem_coe.2 (inv_mem hs),
          ((s : ℋ) : G)⁻¹,
          SetLike.mem_coe.2 (inv_mem ((Subgroup.mem_subgroupOf (H := stabilizer G p)).1 s.2)), ?_⟩
        rw [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
        simp [mul_assoc]

end GeneralAction

end Orbits

/-- **Double cosets are counted by fixed cosets.** For a finite group `G` and subgroups `H` and
`K`, the sum over `g : G` of the number of cosets of `H` fixed by `g` times the number of cosets
of `K` fixed by `g` is the number of double cosets `H \ G / K`, times the order of `G`. -/
theorem sum_card_fixedBy_mul_card_fixedBy_eq_card_doubleCosetQuotient_mul_card_group
    [Fintype G] (H K : Subgroup G) :
    ∑ g : G, Nat.card (fixedBy (G ⧸ H) g) * Nat.card (fixedBy (G ⧸ K) g) =
      Nat.card (DoubleCoset.Quotient (H : Set G) K) * Nat.card G := by
  have : Finite G := Finite.of_fintype G
  rw [card_doubleCosetQuotient_eq_card_orbitQuotient]
  exact sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group (G ⧸ H) (G ⧸ K)

end TauCeti
