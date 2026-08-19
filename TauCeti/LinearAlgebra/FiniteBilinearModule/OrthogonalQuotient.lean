/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OrthogonalComplement

/-!
# Orthogonal quotients of finite bilinear modules

For a subgroup `H` of a finite bilinear module `A`, the vectors of `H` that lie in the orthogonal
complement `H^⊥` pair trivially with the whole of `H^⊥`, so they sit in the radical of the
pairing restricted to `H^⊥`. Quotienting them out produces the *orthogonal quotient* of `A` by
`H`, carrying the induced pairing

```text
b (x + H) (y + H) = b x y  for x, y ∈ H^⊥.
```

The construction needs no hypothesis on `H` whatsoever. When `H` is isotropic — the case the
theory is about — it contains no vectors outside `H^⊥`, so the quotient is the classical
`H^⊥/H`, and its order satisfies `|H^⊥/H| · |H|² = |A|` in a nondegenerate module. Nondegeneracy
of the quotient itself needs only nondegeneracy of `A`, since a vector of `H^⊥` orthogonal to all
of `H^⊥` lies in `H^⊥⊥ = H`.

This is the abstract half of Nikulin's `A_{L_H} ≅ H^⊥/H`; identifying the discriminant form of an
overlattice with this quotient is the lattice-side statement and lives downstream.

## Main declarations

* `TauCeti.FiniteBilinearModule.orthogonalQuotient`: the induced module on `H^⊥` modulo `H`.
* `TauCeti.FiniteBilinearModule.orthogonalQuotient_pairing_mk`: the representative formula.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.isNondegenerate_orthogonalQuotient`:
  nondegeneracy of the orthogonal quotient.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_sq`: the order
  computation `|H^⊥/H| · |H|² = |A|` for isotropic `H`.
* `TauCeti.FiniteBilinearModule.IsLagrangian.card_orthogonalQuotient`: the orthogonal quotient
  by a Lagrangian subgroup is trivial.

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

/-- Inside the orthogonal complement of `H`, the subgroup cut out by `H` lies in the radical of
the restricted pairing: a vector of `H^⊥` is orthogonal to every vector of `H`. -/
theorem addSubgroupOf_orthogonalComplement_le_radical (H : AddSubgroup A) :
    H.addSubgroupOf (A.orthogonalComplement H) ≤
      (A.restrict (A.orthogonalComplement H)).radical := by
  intro x hx
  rw [mem_radical_iff]
  intro y
  rw [restrict_pairing, A.pairing_comm]
  exact (A.mem_orthogonalComplement_iff H y.1).mp y.2 x.1 hx

/-- The **orthogonal quotient** of a finite bilinear module by a subgroup: the pairing restricted
to `H^⊥`, with the vectors of `H` it contains quotiented out.

No hypothesis on `H` is needed for the pairing to descend. For isotropic `H`, where `H ≤ H^⊥`,
this is the classical `H^⊥/H`. -/
noncomputable def orthogonalQuotient (H : AddSubgroup A) : FiniteBilinearModule :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical H)

/-- The quotient map from the orthogonal complement onto the orthogonal quotient. -/
noncomputable def orthogonalQuotientMk (H : AddSubgroup A) :
    A.orthogonalComplement H →+ A.orthogonalQuotient H :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical H)

/-- The induced pairing is represented by the original pairing on representatives. -/
@[simp]
theorem orthogonalQuotient_pairing_mk (H : AddSubgroup A) (x y : A.orthogonalComplement H) :
    (A.orthogonalQuotient H).pairing (A.orthogonalQuotientMk H x)
      (A.orthogonalQuotientMk H y) = A.pairing x y :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical_pairing_mk
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical H) x y

/-- The quotient map onto the orthogonal quotient is surjective. -/
theorem orthogonalQuotientMk_surjective (H : AddSubgroup A) :
    Function.Surjective (A.orthogonalQuotientMk H) :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk_surjective
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical H)

/-- The kernel of the quotient map is the part of `H` lying in `H^⊥`. -/
@[simp]
theorem orthogonalQuotientMk_ker (H : AddSubgroup A) :
    (A.orthogonalQuotientMk H).ker = H.addSubgroupOf (A.orthogonalComplement H) :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadicalMk_ker
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical H)

/-- A class in the orthogonal quotient vanishes exactly when its representative lies in `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_zero_iff (H : AddSubgroup A) (x : A.orthogonalComplement H) :
    A.orthogonalQuotientMk H x = 0 ↔ (x : A) ∈ H := by
  rw [← AddMonoidHom.mem_ker, A.orthogonalQuotientMk_ker H]
  exact AddSubgroup.mem_addSubgroupOf

/-- In a nondegenerate module the orthogonal quotient is nondegenerate: a vector of `H^⊥`
orthogonal to all of `H^⊥` lies in `H^⊥⊥ = H`, so its class vanishes. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    (H : AddSubgroup A) : (A.orthogonalQuotient H).IsNondegenerate := by
  apply (A.orthogonalQuotient H).isNondegenerate_of_injective
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := A.orthogonalQuotientMk_surjective H q
  rw [← AddMonoidHom.mem_ker, A.orthogonalQuotientMk_ker H]
  have hx : (x : A) ∈ A.orthogonalComplement (A.orthogonalComplement H) := by
    rw [A.mem_orthogonalComplement_iff]
    intro y hy
    have hxy := DFunLike.congr_fun hq (A.orthogonalQuotientMk H ⟨y, hy⟩)
    calc
      A.pairing x y = (A.orthogonalQuotient H).pairing (A.orthogonalQuotientMk H x)
          (A.orthogonalQuotientMk H ⟨y, hy⟩) :=
        (A.orthogonalQuotient_pairing_mk H x ⟨y, hy⟩).symm
      _ = (0 : CharacterModule (A.orthogonalQuotient H)) (A.orthogonalQuotientMk H ⟨y, hy⟩) := hxy
      _ = 0 := rfl
  rw [IsNondegenerate.orthogonalComplement_orthogonalComplement A hA H] at hx
  exact hx

/-- For an isotropic subgroup of a nondegenerate module, the order of the orthogonal quotient
satisfies `|H^⊥/H| · |H|² = |A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_sq (hA : A.IsNondegenerate)
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

This is the module-level form of the statement that an even overlattice glued along a Lagrangian
subgroup is unimodular. -/
theorem IsLagrangian.card_orthogonalQuotient (hA : A.IsNondegenerate) {H : AddSubgroup A}
    (hH : A.IsLagrangian H) : Nat.card (A.orthogonalQuotient H) = 1 := by
  have hsq := IsLagrangian.card_sq A hH hA
  have hmul := IsNondegenerate.card_orthogonalQuotient_mul_sq A hA hH.isIsotropic
  rw [hsq] at hmul
  have hpos : 0 < Nat.card A := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [one_mul]
  exact hmul

end TauCeti.FiniteBilinearModule
