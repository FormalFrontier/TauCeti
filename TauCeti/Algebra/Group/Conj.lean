/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index

/-!
# Inversion of conjugacy classes, and the size of a class

Inversion of a group is compatible with conjugacy: `x` and `y` are conjugate exactly when `x⁻¹` and
`y⁻¹` are (`TauCeti.isConj_inv_iff`). So inversion descends to the conjugacy classes, where it is an
involution, recorded here as an `InvolutiveInv (ConjClasses G)` instance; `C⁻¹` is the class of the
inverses of the members of `C`, and it has the same size as `C`. A class fixed by this involution is
a **real** class (`TauCeti.IsRealClass`).

The other fact collected here is that the size of a conjugacy class is the index of the centralizer
of any of its members, and so divides the order of the group: the orbit-stabilizer theorem for the
conjugation action.

## Main statements

* `TauCeti.isConj_inv_iff`: conjugacy is inherited by inverses in both directions.
* `TauCeti.ConjClasses.inv_mk`: the inverse of the class of `g` is the class of `g⁻¹`.
* `TauCeti.IsRealClass`: a class containing an element conjugate to its own inverse, with
  `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `TauCeti.ConjClasses.ncard_carrier_inv` and `TauCeti.ConjClasses.card_carrier_inv`: a conjugacy
  class and its inverse have the same size, in `Set.ncard` and in `Nat.card` form.
* `TauCeti.ConjClasses.ncard_carrier_mk` and `TauCeti.ConjClasses.card_carrier_mk`: the size of a
  conjugacy class is the index of the centralizer of any of its members, in `Set.ncard` and in
  `Nat.card` form.
* `TauCeti.ConjClasses.ncard_carrier_mk_of_mem_center`: the class of a central element is a single
  point.
* `TauCeti.ConjClasses.card_carrier_dvd_card`: the size of a conjugacy class divides the order of
  the group, with `TauCeti.ConjClasses.card_carrier_cast_ne_zero` the consequence that the size of
  a class is nonzero in any semiring where the group order is.

## Implementation notes

The inversion is an instance rather than a plain function so that the notation `C⁻¹`, the
involutivity lemma `inv_inv` and the reindexing equivalence `Equiv.inv` are all available for
conjugacy classes. There is no multiplication on `ConjClasses G` for it to interact with.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- Conjugacy is inherited by inverses in both directions.

Not `@[simp]`: Mathlib's `isConj_iff` is itself `simp`, so the left-hand side simplifies to
`∃ c, c * x⁻¹ * c⁻¹ = y⁻¹` and the simp normal form linter rejects the pair. -/
theorem isConj_inv_iff {x y : G} : IsConj x⁻¹ y⁻¹ ↔ IsConj x y := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this

/-- **Inversion of conjugacy classes.** Inversion of the group respects conjugacy, so it descends
to the conjugacy classes; there it is an involution, because it is one on the group. -/
instance instInvolutiveInvConjClasses : InvolutiveInv (ConjClasses G) where
  inv := Quotient.lift (fun g => ConjClasses.mk g⁻¹) fun _ _ h =>
    ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_inv_iff.mpr h)
  inv_inv C := by
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    exact congrArg ConjClasses.mk (inv_inv g)

namespace ConjClasses

/-- The inverse of the conjugacy class of `g` is the conjugacy class of `g⁻¹`. -/
@[simp]
theorem inv_mk (g : G) : (ConjClasses.mk g)⁻¹ = ConjClasses.mk g⁻¹ :=
  (rfl)

/-- The class of the identity is its own inverse. -/
@[simp]
theorem inv_one : (1 : ConjClasses G)⁻¹ = 1 := by
  rw [ConjClasses.one_eq_mk_one, inv_mk, _root_.inv_one]

/-- An element lies in the inverse of a conjugacy class exactly when its inverse lies in the
class. -/
@[simp]
theorem mem_carrier_inv_iff {C : ConjClasses G} {x : G} :
    x ∈ (C⁻¹).carrier ↔ x⁻¹ ∈ C.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ← inv_mk, inv_eq_iff_eq_inv]

/-- **A conjugacy class and its inverse have the same size**, inversion of the group restricting to
a bijection between them.

This is the `Set.ncard` form, which is the simp normal form: Mathlib's `Nat.card_coe_set_eq` is
itself `simp`. See `TauCeti.ConjClasses.card_carrier_inv` for the `Nat.card` form. -/
@[simp]
theorem ncard_carrier_inv (C : ConjClasses G) :
    Set.ncard (C⁻¹).carrier = Set.ncard C.carrier :=
  Nat.card_congr ((Equiv.inv G).subtypeEquiv fun _ => mem_carrier_inv_iff)

/-- **A conjugacy class and its inverse have the same size**, in `Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(C⁻¹).carrier.ncard` and the simp normal form linter rejects the pair; that normalized form is
`TauCeti.ConjClasses.ncard_carrier_inv`. -/
theorem card_carrier_inv (C : ConjClasses G) : Nat.card (C⁻¹).carrier = Nat.card C.carrier :=
  ncard_carrier_inv C

/-- **The size of a conjugacy class is the index of the centralizer of any of its members.** The
class is the orbit of `g` under the conjugation action and the centralizer is the stabilizer, so
this is the orbit-stabilizer theorem. -/
theorem ncard_carrier_mk (g : G) :
    (ConjClasses.mk g).carrier.ncard = (Subgroup.centralizer {g}).index := by
  have hcomap := (MulAction.stabilizer (ConjAct G) g).index_comap_of_surjective
    (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective
  rw [← ConjAct.orbit_eq_carrier_conjClasses, ← MulAction.index_stabilizer,
    Subgroup.centralizer_eq_comap_stabilizer]
  exact hcomap.symm

/-- **The conjugacy class of a central element is a single point**: nothing moves it. -/
theorem ncard_carrier_mk_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) :
    (ConjClasses.mk g).carrier.ncard = 1 := by
  rw [ncard_carrier_mk, Subgroup.centralizer_eq_top_iff_subset.mpr
    (Set.singleton_subset_iff.mpr hg), Subgroup.index_top]

/-- **The size of a conjugacy class is the index of the centralizer of any of its members**, in
`Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(ConjClasses.mk g).carrier.ncard` and the simp normal form linter rejects the pair; that
normalized form is `TauCeti.ConjClasses.ncard_carrier_mk`. -/
theorem card_carrier_mk (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer {g}).index := by
  rw [Nat.card_coe_set_eq, ncard_carrier_mk]

/-- **The size of a conjugacy class divides the order of the group**, being the index of a
centralizer. -/
theorem card_carrier_dvd_card (C : ConjClasses G) : Nat.card C.carrier ∣ Nat.card G := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
  calc Nat.card (ConjClasses.mk x).carrier
      = (Subgroup.centralizer {x}).index := card_carrier_mk x
    _ ∣ Nat.card G := Subgroup.index_dvd_card _

/-- The size of a conjugacy class is nonzero in any semiring in which the order of the group is
nonzero: it divides that order. -/
theorem card_carrier_cast_ne_zero {R : Type*} [Semiring R] (C : ConjClasses G)
    (h : (Nat.card G : R) ≠ 0) : (Nat.card C.carrier : R) ≠ 0 :=
  ne_zero_of_dvd_ne_zero h (Nat.cast_dvd_cast (card_carrier_dvd_card C))

end ConjClasses

/-- **A real conjugacy class**: one containing an element conjugate to its own inverse. -/
def IsRealClass (C : ConjClasses G) : Prop :=
  ∃ g : G, ConjClasses.mk g = C ∧ IsConj g g⁻¹

/-- **A class is real exactly when inversion fixes it.** -/
@[simp]
theorem isRealClass_iff_inv_eq {C : ConjClasses G} : IsRealClass C ↔ C⁻¹ = C := by
  constructor
  · rintro ⟨g, rfl, hg⟩
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
    exact hg.symm
  · intro h
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
    exact ⟨g, rfl, h.symm⟩

-- Not a `simp` lemma: `isRealClass_iff_inv_eq` and `ConjClasses.inv_mk` already rewrite the
-- left-hand side to `ConjClasses.mk g⁻¹ = ConjClasses.mk g`, so tagging it makes `simpNF` fail.
/-- The class of `g` is real exactly when `g` is conjugate to `g⁻¹`. -/
theorem isRealClass_mk_iff {g : G} : IsRealClass (ConjClasses.mk g) ↔ IsConj g g⁻¹ := by
  rw [isRealClass_iff_inv_eq, ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

end TauCeti
