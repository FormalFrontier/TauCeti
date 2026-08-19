/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Complement

/-!
# Orthogonal quotients of finite bilinear modules

For a subgroup `H` of a finite bilinear module `A`, the vectors of `H` that lie in the orthogonal
complement `H^⊥` pair trivially with the whole of `H^⊥`, so they sit in the radical of the
pairing restricted to `H^⊥`. Quotienting them out produces the *orthogonal quotient* of `A` by
`H`, carrying the induced pairing

```text
b (x + (H ⊓ H^⊥)) (y + (H ⊓ H^⊥)) = b x y  for x, y ∈ H^⊥.
```

The construction needs no hypothesis on `H` whatsoever, which is why the classes above are taken
modulo `H ⊓ H^⊥` rather than `H`. When `H` is isotropic — the case the theory is about — it is
contained in `H^⊥`, the two agree, and the quotient is the classical `H^⊥/H` whose order
satisfies `|H^⊥/H| · |H|² = |A|` in a nondegenerate module. Nondegeneracy of the quotient itself
needs only nondegeneracy of `A`, since a vector of `H^⊥` orthogonal to all of `H^⊥` lies in
`H^⊥⊥ = H`.

This is the abstract half of Nikulin's `A_{L_H} ≅ H^⊥/H`. Identifying the discriminant form of an
overlattice with this quotient is the lattice-side statement and is not yet formalized.

## Main declarations

* `TauCeti.FiniteBilinearModule.orthogonalQuotient`: the induced module on `H^⊥` modulo the part
  of `H` it contains.
* `TauCeti.FiniteBilinearModule.orthogonalQuotient_pairing_mk`: the representative formula.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.isNondegenerate_orthogonalQuotient`:
  nondegeneracy of the orthogonal quotient.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_card_sq`: the order
  computation `|H^⊥/H| · |H|² = |A|` for isotropic `H`.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_eq_one_iff_isLagrangian`:
  triviality of the quotient characterizes Lagrangian subgroups.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
  Proposition 1.4.1: the induced form on `H^⊥/H` in that proposition, here in the half-norm
  `ℚ/ℤ` convention and at the bilinear level. The proposition itself is the even, quadratic
  overlattice statement in the full-norm `ℚ/2ℤ` convention, and is not being claimed for the
  bilinear case; the quadratic refinement is downstream.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
* `TauCetiRoadmap/IntegralLattices/Suggested.lean` (`subgroupInOrthogonal`,
  `OrthogonalQuotient`), whose pinned signature carries an isotropy hypothesis that the
  construction here does not need.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u

variable (A : FiniteBilinearModule.{u})

/-- Inside the orthogonal complement of `H`, the subgroup cut out by `H` lies in the radical of
the *restricted* pairing: a vector of `H^⊥` is orthogonal to every vector of `H`. -/
theorem addSubgroupOf_orthogonalComplement_le_radical_restrict (H : AddSubgroup A) :
    H.addSubgroupOf (A.orthogonalComplement H) ≤
      (A.restrict (A.orthogonalComplement H)).radical := by
  intro x hx
  rw [mem_radical_iff]
  intro y
  rw [restrict_pairing, A.pairing_comm]
  exact (A.mem_orthogonalComplement_iff H y.1).mp y.2 x.1 hx

/-- The **orthogonal quotient** of a finite bilinear module by a subgroup: the pairing restricted
to `H^⊥`, with the vectors of `H` it contains quotiented out.

No hypothesis on `H` is needed for the pairing to descend, so this is the quotient by `H ⊓ H^⊥`.
The pinned signature in `Suggested.lean` carries `hH : A.IsIsotropic H`; that hypothesis is
dropped here because the construction does not use it, and for isotropic `H`, where `H ≤ H^⊥`,
this is the classical `H^⊥/H`. -/
noncomputable def orthogonalQuotient (H : AddSubgroup A) : FiniteBilinearModule :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The quotient map from the orthogonal complement onto the orthogonal quotient. -/
noncomputable def orthogonalQuotientMk (H : AddSubgroup A) :
    A.orthogonalComplement H →+ A.orthogonalQuotient H :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The induced pairing is represented by the original pairing on representatives. -/
@[simp]
theorem orthogonalQuotient_pairing_mk (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    (A.orthogonalQuotient H).pairing (A.orthogonalQuotientMk H x)
      (A.orthogonalQuotientMk H y) = A.pairing x y :=
  ((A.restrict (A.orthogonalComplement H)).quotientOfLeRadical_pairing_mk
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H) x y).trans
      (A.restrict_pairing (A.orthogonalComplement H) x y)

/-- The quotient map onto the orthogonal quotient is surjective. -/
theorem orthogonalQuotientMk_surjective (H : AddSubgroup A) :
    Function.Surjective (A.orthogonalQuotientMk H) :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk_surjective
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- The kernel of the quotient map is the part of `H` lying in `H^⊥`. -/
@[simp]
theorem orthogonalQuotientMk_ker (H : AddSubgroup A) :
    (A.orthogonalQuotientMk H).ker = H.addSubgroupOf (A.orthogonalComplement H) :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk_ker
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

/-- A class in the orthogonal quotient vanishes exactly when its representative lies in `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_zero_iff (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = 0 ↔ (x : A) ∈ H := by
  rw [← AddMonoidHom.mem_ker, A.orthogonalQuotientMk_ker H]
  exact AddSubgroup.mem_addSubgroupOf

/-- Two classes in the orthogonal quotient agree exactly when their representatives differ by a
vector of `H`. -/
theorem orthogonalQuotientMk_eq_iff (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = A.orthogonalQuotientMk H y ↔
      ((x - y : A.orthogonalComplement H) : A) ∈ H := by
  rw [← A.orthogonalQuotientMk_eq_zero_iff H, map_sub, sub_eq_zero]

/-- In a nondegenerate module the radical of the pairing restricted to `H^⊥` is exactly the part
of `H` inside `H^⊥`, since a vector of `H^⊥` orthogonal to all of `H^⊥` lies in `H^⊥⊥ = H`. -/
theorem IsNondegenerate.radical_restrict_le_addSubgroupOf (hA : A.IsNondegenerate)
    (H : AddSubgroup A) :
    (A.restrict (A.orthogonalComplement H)).radical ≤
      H.addSubgroupOf (A.orthogonalComplement H) := by
  intro x hx
  have hmem : (x : A) ∈ A.orthogonalComplement (A.orthogonalComplement H) := by
    rw [A.mem_orthogonalComplement_iff]
    intro y hy
    have hxy := (mem_radical_iff _ x).mp hx ⟨y, hy⟩
    rwa [restrict_pairing] at hxy
  rw [IsNondegenerate.orthogonalComplement_orthogonalComplement A hA H] at hmem
  exact AddSubgroup.mem_addSubgroupOf.mpr hmem

/-- In a nondegenerate module the orthogonal quotient is nondegenerate. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    (H : AddSubgroup A) : (A.orthogonalQuotient H).IsNondegenerate :=
  ((A.restrict (A.orthogonalComplement H)).isNondegenerate_quotientOfLeRadical_iff
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)).mpr
      (IsNondegenerate.radical_restrict_le_addSubgroupOf A hA H)

/-- For an isotropic subgroup of a nondegenerate module, the order of the orthogonal quotient
satisfies `|H^⊥/H| · |H|² = |A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_sq (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) * Nat.card H ^ 2 = Nat.card A := by
  have hle : H ≤ A.orthogonalComplement H :=
    (A.isIsotropic_iff_le_orthogonalComplement H).mp hH
  have hKcard : Nat.card (H.addSubgroupOf (A.orthogonalComplement H)) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv
  have hindex : (H.addSubgroupOf (A.orthogonalComplement H)).index =
      Nat.card (A.orthogonalQuotient H) := by
    rw [← A.orthogonalQuotientMk_ker H, AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top.mpr (A.orthogonalQuotientMk_surjective H)]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  have hlag := AddSubgroup.card_mul_index (H.addSubgroupOf (A.orthogonalComplement H))
  rw [hKcard, hindex] at hlag
  have hAcard := IsNondegenerate.card_mul_card_orthogonalComplement A hA H
  rw [← hlag] at hAcard
  rw [← hAcard]
  ring

/-- The orthogonal quotient by a Lagrangian subgroup is trivial: `H = H^⊥` leaves nothing behind.

No nondegeneracy is needed; every representative already lies in `H`. -/
theorem IsLagrangian.card_orthogonalQuotient_eq_one {H : AddSubgroup A}
    (hH : A.IsLagrangian H) : Nat.card (A.orthogonalQuotient H) = 1 := by
  have hzero : ∀ q : A.orthogonalQuotient H, q = 0 := by
    intro q
    obtain ⟨x, rfl⟩ := A.orthogonalQuotientMk_surjective H q
    refine (A.orthogonalQuotientMk_eq_zero_iff H x).mpr ?_
    exact ((A.isLagrangian_def H).mp hH).ge x.2
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun q r ↦ (hzero q).trans (hzero r).symm⟩, ⟨0⟩⟩

/-- **Triviality of the orthogonal quotient characterizes Lagrangians.** For an isotropic
subgroup of a nondegenerate module, the quotient collapses exactly when `H = H^⊥`. -/
theorem IsNondegenerate.card_orthogonalQuotient_eq_one_iff_isLagrangian (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H) = 1 ↔ A.IsLagrangian H := by
  refine ⟨fun hcard ↦ ?_, IsLagrangian.card_orthogonalQuotient_eq_one A⟩
  have hsq := IsNondegenerate.card_orthogonalQuotient_mul_card_sq A hA hH
  rw [hcard, one_mul] at hsq
  have hAcard := IsNondegenerate.card_mul_card_orthogonalComplement A hA H
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcards : Nat.card (A.orthogonalComplement H) = Nat.card H := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hAcard, ← hsq, pow_two]
  exact (A.isLagrangian_def H).mpr (AddSubgroup.eq_of_le_of_card_ge
    ((A.isIsotropic_iff_le_orthogonalComplement H).mp hH) hcards.le)

end TauCeti.FiniteBilinearModule
