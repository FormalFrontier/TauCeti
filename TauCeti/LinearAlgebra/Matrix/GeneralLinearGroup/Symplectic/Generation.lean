/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations
import TauCeti.GroupTheory.Commutator

/-!
# Generating the difference-root subgroups of the symplectic group

For the standard type-`C_m` root system, the roots `eᵢ - eⱼ` form its type-`A_(m-1)`
subsystem. This file proves its structure-constant-one Chevalley relation

```text
⁅x_{eᵢ-eⱼ}(a), x_{eⱼ-eₖ}(b)⁆ = x_{eᵢ-eₖ}(ab)
```

and uses it to show that a subgroup containing the difference-root elements at adjacent indices,
in both orientations, contains every difference-root element. This is the first generation step
for identifying the full-weight type-`C` Chevalley carrier with the standard symplectic group: the
numbered short simple roots are adjacent difference roots, while the remaining simple root is
long.

## Main results

* `TauCeti.GLSymplecticFin.commutatorElement_differenceShortRootUnit_differenceShortRootUnit`:
  the Chevalley commutator relation inside the difference-root subsystem.
* `TauCeti.GLSymplecticFin.differenceShortRootUnit_mem_of_adjacent`: adjacent difference-root
  subgroups generate all difference-root subgroups.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it supplies the type-`A` subsystem generation needed
to identify the explicit full-weight type-`C` carrier on field-valued points.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j k : Fin m}

/-- **The structure-constant-one Chevalley relation in the difference-root subsystem.** For
pairwise distinct indices, the commutator of `x_{eᵢ-eⱼ}(a)` and `x_{eⱼ-eₖ}(b)` is
`x_{eᵢ-eₖ}(ab)`. -/
theorem commutatorElement_differenceShortRootUnit_differenceShortRootUnit
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅differenceShortRootUnit hij a, differenceShortRootUnit hjk b⁆ =
      differenceShortRootUnit hik (a * b) := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_commutatorElement]
  -- Expose the ambient general-linear equality so that the explicit matrix formulas apply.
  change
    ⁅((differenceShortRootUnit hij a : GLSymplecticFin m R) : GL (Fin (m + m)) R),
        ((differenceShortRootUnit hjk b : GLSymplecticFin m R) : GL (Fin (m + m)) R)⁆ =
      ((differenceShortRootUnit hik (a * b) : GLSymplecticFin m R) :
        GL (Fin (m + m)) R)
  rw [coe_differenceShortRootUnit, coe_differenceShortRootUnit,
    coe_differenceShortRootUnit]
  let I := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl i)
  let J := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl j)
  let K := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inl k)
  let I' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr i)
  let J' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr j)
  let K' := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Sum.inr k)
  have hIJ : I ≠ J := differenceShortRoot_first_indices_ne hij
  have hJK : J ≠ K := differenceShortRoot_first_indices_ne hjk
  have hIK : I ≠ K := differenceShortRoot_first_indices_ne hik
  have hJ'I' : J' ≠ I' := differenceShortRoot_second_indices_ne hij
  have hK'J' : K' ≠ J' := differenceShortRoot_second_indices_ne hjk
  have hK'I' : K' ≠ I' := differenceShortRoot_second_indices_ne hik
  -- The upper and lower blocks each satisfy the type-A transvection relation.
  have hAC :
      ⁅transvectionUnit hIJ a, transvectionUnit hJK b⁆ =
        transvectionUnit hIK (a * b) :=
    commutatorElement_transvectionUnit hIJ hJK hIK a b
  have hBD :
      ⁅transvectionUnit hJ'I' (-a), transvectionUnit hK'J' (-b)⁆ =
        transvectionUnit hK'I' (-(a * b)) := by
    rw [commutatorElement_transvectionUnit_reverse hJ'I' hK'J' hK'I']
    congr 1
    ring
  -- All cross-block terms commute, including the two factors in the resulting root element.
  have hBC : Commute (transvectionUnit hJ'I' (-a)) (transvectionUnit hJK b) :=
    commute_transvectionUnit hJ'I' hJK
      (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inl_ne_inr k j) _ _
  have hAD : Commute (transvectionUnit hIJ a) (transvectionUnit hK'J' (-b)) :=
    commute_transvectionUnit hIJ hK'J'
      (finSumFinEquiv_inl_ne_inr j k) (finSumFinEquiv_inr_ne_inl j i) _ _
  have hCQ : Commute (transvectionUnit hJK b) (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hJK hK'I'
      (finSumFinEquiv_inl_ne_inr k k) (finSumFinEquiv_inr_ne_inl i j) _ _
  have hAQ : Commute (transvectionUnit hIJ a) (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hIJ hK'I'
      (finSumFinEquiv_inl_ne_inr j k) (finSumFinEquiv_inr_ne_inl i i) _ _
  have hPQ : Commute (transvectionUnit hIK (a * b))
      (transvectionUnit hK'I' (-(a * b))) :=
    commute_transvectionUnit hIK hK'I'
      (finSumFinEquiv_inl_ne_inr k k) (finSumFinEquiv_inr_ne_inl i i) _ _
  -- Expand the commutator of the two paired transvections, commute cross terms, and regroup.
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_mul_right_eq_mul_conj, hBC.commutator_eq, one_mul, hBD,
    hCQ.eq, mul_inv_cancel_right, hAQ.eq, mul_inv_cancel_right,
    commutatorElement_mul_right_eq_mul_conj, hAC, hAD.commutator_eq, mul_one,
    mul_inv_cancel_right, hPQ.eq]

/-- If a subgroup of the standard symplectic group contains every adjacent difference-root
element in both orientations, then it contains every difference-root element. -/
theorem differenceShortRootUnit_mem_of_adjacent
    (H : Subgroup (GLSymplecticFin m R))
    (hadjacent : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → differenceShortRootUnit hij c ∈ H)
    {i j : Fin m} (hij : i ≠ j) (c : R) :
    differenceShortRootUnit hij c ∈ H := by
  exact Subgroup.mem_of_adjacent_of_commutator H
    (fun hij c => differenceShortRootUnit hij c)
    (fun hij hjk hik a b =>
      commutatorElement_differenceShortRootUnit_differenceShortRootUnit hij hjk hik a b)
    hadjacent hij c

end TauCeti.GLSymplecticFin
