/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Complement

/-!
# Orthogonal quotients of finite bilinear modules

Let `A` be a finite bilinear module and let `H` be an additive subgroup of it.  The pairing of
`A` restricted to `H⊥` kills the vectors of `H` that lie in `H⊥`, so it descends to the quotient

```text
H⊥ / (H ∩ H⊥).
```

For an isotropic `H`, where `H ≤ H⊥`, this is the classical orthogonal quotient `H⊥ / H`.  The
construction itself needs no isotropy hypothesis, and is given here without one; isotropy is
assumed exactly in the two places where it is used, namely the order computation and the
Lagrangian criterion.

The results are the ones the gluing theory of integral lattices asks of this quotient.  It is
nondegenerate precisely when `H` swallows the radical of `A`, which for nondegenerate `A` is
automatic.  Its order is the index of `H ∩ H⊥` in `H⊥`, so for nondegenerate `A` and isotropic
`H` the double-complement cardinality identity `|H| |H⊥| = |A|` of
`TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Complement` turns into

```text
|H⊥ / H| · |H|² = |A|.
```

The quotient is trivial exactly when `H⊥ ≤ H`, hence — for isotropic `H` — exactly when `H` is
Lagrangian.  Read through the discriminant form of an integral lattice, that last statement is
the module-level form of "an overlattice glued along a Lagrangian subgroup is unimodular".

The quadratic refinement `TauCeti.FiniteQuadraticModule.orthogonalQuotient` of
`TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic` carries a quadratic map on the same
quotient group, and its underlying bilinear module is definitionally the construction of this
file; `TauCeti.FiniteQuadraticModule.orthogonalQuotient_toFiniteBilinearModule` records that
identification, and the quadratic nondegeneracy and order theorems are deduced from the bilinear
ones through it.

## Main declarations

* `TauCeti.FiniteBilinearModule.orthogonalQuotient`: the finite bilinear module induced on
  `H⊥ / (H ∩ H⊥)`.
* `TauCeti.FiniteBilinearModule.orthogonalQuotient_pairing_mk`: its pairing, on representatives.
* `TauCeti.FiniteBilinearModule.radical_orthogonalQuotient`: its radical, as the image of the
  restricted radical.
* `TauCeti.FiniteBilinearModule.isNondegenerate_orthogonalQuotient_iff`: it is nondegenerate
  exactly when `rad(A) ≤ H`.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_card_sq`: the order
  computation `|H⊥ / H| · |H|² = |A|`, for a nondegenerate module and an isotropic subgroup.
* `TauCeti.FiniteBilinearModule.card_orthogonalQuotient_eq_one_iff_isLagrangian`: the quotient of
  an isotropic subgroup is trivial exactly when that subgroup is Lagrangian.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u

variable (A : FiniteBilinearModule.{u})

/-! ## The induced pairing on `H⊥ / (H ∩ H⊥)` -/

/-- **The orthogonal quotient of a finite bilinear module.**  The pairing of `A` is restricted to
`H⊥` and then divided by the part of `H` lying in `H⊥`, which is degenerate for the restricted
pairing by
`TauCeti.FiniteBilinearModule.addSubgroupOf_orthogonalComplement_le_radical_restrict`.

No isotropy hypothesis is needed: `H ∩ H⊥` is always killed by the restricted pairing.  When `H`
is isotropic, so that `H ≤ H⊥`, this is the classical `H⊥ / H`.

Exposed for the same reason as `quotientOfLeRadical`, on which it is built: so that its carrier
reduces to the `Submodule` quotient and maps out of it are definable. -/
@[expose] noncomputable def orthogonalQuotient (H : AddSubgroup A) : FiniteBilinearModule :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The quotient map from `H⊥` onto the orthogonal quotient. -/
noncomputable def orthogonalQuotientMk (H : AddSubgroup A) :
    A.orthogonalComplement H →+ A.orthogonalQuotient H :=
  quotientOfLeRadicalMk (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The pairing of the orthogonal quotient is the pairing of `A` on representatives. -/
@[simp]
theorem orthogonalQuotient_pairing_mk (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    (A.orthogonalQuotient H).pairing (A.orthogonalQuotientMk H x)
      (A.orthogonalQuotientMk H y) = A.pairing x.1 y.1 :=
  quotientOfLeRadical_pairing_mk (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x y

/-- The quotient map onto the orthogonal quotient is surjective. -/
theorem orthogonalQuotientMk_surjective (H : AddSubgroup A) :
    Function.Surjective (A.orthogonalQuotientMk H) :=
  quotientOfLeRadicalMk_surjective (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- Every element of the orthogonal quotient is the class of an element of `H⊥`. -/
@[elab_as_elim]
theorem orthogonalQuotient_induction_on (H : AddSubgroup A)
    {motive : A.orthogonalQuotient H → Prop} (q : A.orthogonalQuotient H)
    (mk : ∀ x : A.orthogonalComplement H, motive (A.orthogonalQuotientMk H x)) : motive q := by
  obtain ⟨x, rfl⟩ := A.orthogonalQuotientMk_surjective H q
  exact mk x

/-- **The radical of the orthogonal quotient** is the image of the radical of the restricted
pairing. -/
@[simp]
theorem radical_orthogonalQuotient (H : AddSubgroup A) :
    (A.orthogonalQuotient H).radical =
      ((H ⊔ A.radical).addSubgroupOf (A.orthogonalComplement H)).map
        (A.orthogonalQuotientMk H) := by
  unfold orthogonalQuotient orthogonalQuotientMk
  rw [radical_quotientOfLeRadical, A.radical_restrict_orthogonalComplement]

/-- An element of `H⊥` has zero class in the orthogonal quotient exactly when it lies in `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_zero_iff (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = 0 ↔ (x : A) ∈ H :=
  quotientOfLeRadicalMk_eq_zero_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x

/-- Two elements of `H⊥` have the same class in the orthogonal quotient exactly when they differ
by an element of `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_iff (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = A.orthogonalQuotientMk H y ↔ (x : A) - y ∈ H :=
  quotientOfLeRadicalMk_eq_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x y

/-! ## Nondegeneracy -/

/-- **Nondegeneracy of the orthogonal quotient.** The quotient `H⊥ / (H ∩ H⊥)` is
nondegenerate exactly when `H` contains the radical of `A`.

Only the radical can survive: an element of `H⊥` orthogonal to all of `H⊥` lies in `H⊥⊥`, which
is `H` enlarged by the radical. -/
theorem isNondegenerate_orthogonalQuotient_iff (H : AddSubgroup A) :
    (A.orthogonalQuotient H).IsNondegenerate ↔ A.radical ≤ H := by
  have hiff := isNondegenerate_quotientOfLeRadical_iff (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)
  rw [A.radical_restrict_orthogonalComplement] at hiff
  refine hiff.trans ⟨fun hle x hx ↦ ?_, fun hle ↦ ?_⟩
  · have hxperp : x ∈ A.orthogonalComplement H := by
      rw [A.mem_orthogonalComplement_iff]
      exact fun y _ ↦ (A.mem_radical_iff x).mp hx y
    exact hle (x := ⟨x, hxperp⟩) (AddSubgroup.mem_addSubgroupOf.mpr (AddSubgroup.mem_sup_right hx))
  · rw [sup_eq_left.mpr hle]

/-- The orthogonal quotient of a nondegenerate finite bilinear module is nondegenerate. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    (H : AddSubgroup A) : (A.orthogonalQuotient H).IsNondegenerate :=
  (A.isNondegenerate_orthogonalQuotient_iff H).mpr (hA.radical_eq_bot ▸ bot_le)

/-! ## Order -/

/-- The order of the orthogonal quotient is the index of `H ∩ H⊥` in `H⊥`. -/
theorem card_orthogonalQuotient (H : AddSubgroup A) :
    Nat.card (A.orthogonalQuotient H) = (H.addSubgroupOf (A.orthogonalComplement H)).index :=
  card_quotientOfLeRadical (A.restrict (A.orthogonalComplement H))
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- **The order of the orthogonal quotient of an isotropic subgroup.**  In a nondegenerate finite
bilinear module, `|H⊥ / H| · |H|² = |A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_sq (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) * Nat.card H ^ 2 = Nat.card A := by
  have hle : H ≤ A.orthogonalComplement H := (A.isIsotropic_iff_le_orthogonalComplement H).mp hH
  have hcard : Nat.card (H.addSubgroupOf (A.orthogonalComplement H)) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  have hquot : Nat.card (A.orthogonalQuotient H) * Nat.card H =
      Nat.card (A.orthogonalComplement H) := by
    rw [A.card_orthogonalQuotient H, ← hcard]
    exact (H.addSubgroupOf (A.orthogonalComplement H)).index_mul_card
  rw [pow_two, ← mul_assoc, hquot, mul_comm]
  exact IsNondegenerate.card_mul_card_orthogonalComplement A hA H

/-! ## The Lagrangian criterion -/

/-- The orthogonal quotient is trivial exactly when `H⊥` is contained in `H`.  No hypothesis on
`A` or on `H` is needed. -/
theorem card_orthogonalQuotient_eq_one_iff (H : AddSubgroup A) :
    Nat.card (A.orthogonalQuotient H) = 1 ↔ A.orthogonalComplement H ≤ H := by
  rw [A.card_orthogonalQuotient H, AddSubgroup.index_eq_one, AddSubgroup.addSubgroupOf_eq_top]

/-- **The Lagrangian criterion.**  The orthogonal quotient of an isotropic subgroup is trivial
exactly when that subgroup is Lagrangian. -/
theorem card_orthogonalQuotient_eq_one_iff_isLagrangian {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) = 1 ↔ A.IsLagrangian H := by
  rw [A.card_orthogonalQuotient_eq_one_iff H, A.isLagrangian_def H]
  exact ⟨fun h ↦ le_antisymm ((A.isIsotropic_iff_le_orthogonalComplement H).mp hH) h,
    fun h ↦ h ▸ le_rfl⟩

/-- The orthogonal quotient of a Lagrangian subgroup is trivial. -/
theorem IsLagrangian.card_orthogonalQuotient_eq_one {H : AddSubgroup A}
    (hH : A.IsLagrangian H) : Nat.card (A.orthogonalQuotient H) = 1 :=
  (A.card_orthogonalQuotient_eq_one_iff_isLagrangian hH.isIsotropic).mpr hH

end TauCeti.FiniteBilinearModule
