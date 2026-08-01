/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.SpinAction

/-!
# The Pin group acting on its quadratic space by twisted conjugation

The Pin group of a quadratic form acts on the underlying quadratic space by *twisted* conjugation,
`v ↦ involute x * ι v * x⁻¹`, and this is the map whose kernel and image make `Pin(Q) → O(Q)` a
double cover. The twist by the grade involution `CliffordAlgebra.involute` is what makes a single
vector act by the reflection in its orthogonal hyperplane rather than by minus that reflection, so
it is the twisted conjugation, not the plain one, that carries the generators of the Lipschitz
group to the generators of the orthogonal group.

Mathlib knows that twisted conjugation by a Lipschitz element keeps vectors as vectors
(`lipschitzGroup.involute_act_ι_mem_range_ι`), but not that the resulting map of the quadratic
space preserves the form, nor that it is a group homomorphism. This file supplies both.
Form-preservation is proved along the generation of `lipschitzGroup Q` by vectors: a vector of
invertible norm acts by `TauCeti.QuadraticMap.reflection`, which is orthogonal, and the orthogonal
group is a subgroup, so every Lipschitz element acts orthogonally. That identification of the
generators is `TauCeti.CliffordAlgebra.lipschitzVectorAction_unitι`, and it is the statement an
eventual Cartan-Dieudonné theorem turns into surjectivity of the double cover.

`TauCeti.CliffordAlgebra.spinToOrthogonal` already describes the spin group acting by *plain*
conjugation. That is not a second action: an element of the spin group is even, so `involute` fixes
it, and `TauCeti.CliffordAlgebra.pinToOrthogonal_spinToPin` records that the two agree there.
Twisted conjugation is the one that extends to the odd part.

## Main definitions

* `TauCeti.CliffordAlgebra.unitι Q v`: a vector of invertible norm, as a unit of the Clifford
  algebra and hence a generator of the Lipschitz group.
* `TauCeti.CliffordAlgebra.lipschitzVectorAction Q x`: the automorphism of the quadratic space
  induced by twisted conjugation by a Lipschitz element.
* `TauCeti.CliffordAlgebra.lipschitzToOrthogonal Q` and
  `TauCeti.CliffordAlgebra.pinToOrthogonal Q`: the resulting homomorphisms to `O(Q)`, along the
  inclusions `TauCeti.CliffordAlgebra.pinToLipschitz` and `TauCeti.CliffordAlgebra.spinToPin`.

## Main results

* `TauCeti.CliffordAlgebra.lipschitzVectorAction_unitι`: **a vector acts by the reflection in its
  orthogonal hyperplane.** This is the identification of the generators referred to above.
* `TauCeti.CliffordAlgebra.lipschitzVectorAction_map_app`: twisted conjugation by a Lipschitz
  element preserves the quadratic form.
* `TauCeti.CliffordAlgebra.ι_mem_pinGroup`: a vector `v` with `Q v = -1` lies in the Pin group, and
  `TauCeti.CliffordAlgebra.pinToOrthogonal_ι_apply` computes the reflection it induces. The sign is
  forced by Mathlib's conventions: `star` is the reversal composed with the grade involution, so
  `star (ι Q v) = -ι Q v` and the unitarity condition defining `pinGroup Q` reads `-Q v = 1` on a
  vector.
* `TauCeti.CliffordAlgebra.pinToOrthogonal_spinToPin`: on the spin group, twisted conjugation is
  plain conjugation.

Surjectivity of `pinToOrthogonal Q` (Cartan-Dieudonné) and the computation of its kernel as `{±1}`
need a field of characteristic not two, a nondegenerate form and finite dimension, and are not
attempted here; everything below holds over a commutative ring, with `2` invertible only where
Mathlib's twisted-conjugation lemmas require it.

## References

This is Layer 2, "The twisted-conjugation homomorphism", of
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2, and C. Chevalley, *The Algebraic Theory of
Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-! ### Twisted conjugation -/

/-- Twisted conjugation by a unit `x` of the Clifford algebra: `a ↦ involute x * a * x⁻¹`.

The twist by the grade involution `CliffordAlgebra.involute` is what makes a vector act by the
reflection in its orthogonal hyperplane (`lipschitzVectorAction_unitι`) rather than by the negative
of it. On the even part `involute` is the identity, so there twisted conjugation agrees with plain
conjugation. -/
private def twistedConj (x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (LinearMap.mulRight R ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)).comp
    (LinearMap.mulLeft R (involute (Q := Q) (x : CliffordAlgebra Q)))

@[simp]
private theorem twistedConj_apply (x : (CliffordAlgebra Q)ˣ) (a : CliffordAlgebra Q) :
    twistedConj Q x a =
      involute (Q := Q) (x : CliffordAlgebra Q) * a *
        ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [twistedConj]
  rfl

private theorem twistedConj_one (a : CliffordAlgebra Q) : twistedConj Q 1 a = a := by
  simp

private theorem twistedConj_mul (x y : (CliffordAlgebra Q)ˣ) (a : CliffordAlgebra Q) :
    twistedConj Q (x * y) a = twistedConj Q x (twistedConj Q y a) := by
  simp only [twistedConj_apply, Units.val_mul, mul_inv_rev, map_mul]
  noncomm_ring

/-! ### Vectors of invertible norm as Lipschitz elements -/

/-- A vector of invertible norm, as a unit of the Clifford algebra. These units generate the
Lipschitz group (`unitι_mem_lipschitzGroup`), and they act on the quadratic space by the
reflections in their orthogonal hyperplanes (`lipschitzVectorAction_unitι`). -/
def unitι (v : M) [Invertible (Q v)] : (CliffordAlgebra Q)ˣ :=
  letI := invertibleιOfInvertible Q v
  unitOfInvertible (ι Q v)

variable {Q}

@[simp]
theorem coe_unitι (v : M) [Invertible (Q v)] : (unitι Q v : CliffordAlgebra Q) = ι Q v := by
  rw [unitι]
  rfl

/-- The vectors of invertible norm are the generators of the Lipschitz group. -/
theorem unitι_mem_lipschitzGroup (v : M) [Invertible (Q v)] : unitι Q v ∈ lipschitzGroup Q := by
  unfold lipschitzGroup
  exact Subgroup.subset_closure ⟨v, (coe_unitι v).symm⟩

/-- A vector of norm `-1` lies in the Pin group. The sign is Mathlib's convention: `star` is the
reversal composed with the grade involution, so `star (ι Q v) = -ι Q v`, and the unitarity
condition `star x * x = 1` defining `pinGroup Q` reads `-Q v = 1` on a vector. -/
theorem ι_mem_pinGroup {v : M} (hv : Q v = -1) : ι Q v ∈ pinGroup Q := by
  letI : Invertible (Q v) := ⟨-1, by rw [hv]; ring, by rw [hv]; ring⟩
  have hsq : ι Q v * ι Q v = -1 := by rw [ι_sq_scalar, hv, map_neg, map_one]
  refine ⟨⟨unitι Q v, unitι_mem_lipschitzGroup v, coe_unitι v⟩, ?_, ?_⟩
  · rw [star_ι, neg_mul, hsq, neg_neg]
  · rw [star_ι, mul_neg, hsq, neg_neg]

/-! ### The induced map on the quadratic space

Twisted conjugation by a Lipschitz element carries vectors to vectors, so it descends to the
quadratic space through the vector part `TauCeti.CliffordAlgebra.ιInv`. The unbundled form
`vectorMap` below is a plain linear endomorphism, defined for every unit but meaningful only for
Lipschitz ones; the bundled automorphism is `lipschitzVectorAction`. -/

variable (Q) [Invertible (2 : R)]

/-- The unbundled twisted-conjugation map on the quadratic space. -/
private def vectorMap (x : (CliffordAlgebra Q)ˣ) : M →ₗ[R] M :=
  (ιInv Q).comp ((twistedConj Q x).comp (ι Q))

private theorem vectorMap_apply (x : (CliffordAlgebra Q)ˣ) (m : M) :
    vectorMap Q x m = ιInv Q (twistedConj Q x (ι Q m)) := by
  rw [vectorMap]
  rfl

private theorem ι_vectorMap_apply {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (m : M) :
    ι Q (vectorMap Q x m) = twistedConj Q x (ι Q m) := by
  rw [vectorMap_apply]
  exact ι_ιInv_of_mem Q ((twistedConj_apply Q x (ι Q m)).symm ▸
    lipschitzGroup.involute_act_ι_mem_range_ι hx m)

private theorem vectorMap_one : vectorMap Q 1 = LinearMap.id := by
  ext m
  apply ι_injective Q
  rw [ι_vectorMap_apply Q (one_mem _), twistedConj_one, LinearMap.id_coe, id_eq]

private theorem vectorMap_mul {x y : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    (hy : y ∈ lipschitzGroup Q) : vectorMap Q (x * y) = vectorMap Q x ∘ₗ vectorMap Q y := by
  ext m
  apply ι_injective Q
  rw [ι_vectorMap_apply Q (mul_mem hx hy), LinearMap.comp_apply, ι_vectorMap_apply Q hx,
    ι_vectorMap_apply Q hy, twistedConj_mul]

/-- Twisted conjugation by a vector of invertible norm is the reflection in its orthogonal
hyperplane. Only the value of the unit matters, so this is stated for an arbitrary unit whose value
is `ι Q v`. -/
private theorem vectorMap_eq_reflection (v : M) [Invertible (Q v)] {x : (CliffordAlgebra Q)ˣ}
    (hx : (x : CliffordAlgebra Q) = ι Q v) :
    vectorMap Q x = (QuadraticMap.reflection Q v : M →ₗ[R] M) := by
  letI := invertibleιOfInvertible Q v
  have hinv : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ⅟(ι Q v) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hx, mul_invOf_self])
  ext m
  have key : twistedConj Q x (ι Q m) = ι Q (QuadraticMap.reflection Q v m) := by
    rw [twistedConj_apply, hx, hinv, involute_ι, neg_mul, neg_mul, ι_mul_ι_mul_invOf_ι,
      QuadraticMap.reflection_apply, ← map_neg, neg_sub]
  rw [vectorMap_apply, key, ιInv_ι]
  rfl

private theorem vectorMap_map_app {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (m : M) :
    Q (vectorMap Q x m) = Q m := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction generalizing m with
  | mem u hu =>
    obtain ⟨a, ha⟩ := hu
    letI := u.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI := invertibleOfInvertibleι Q a
    rw [vectorMap_eq_reflection Q a ha.symm]
    exact QuadraticMap.map_app_of_mem_orthogonalGroup
      (QuadraticMap.reflection_mem_orthogonalGroup Q a) m
  | one => rw [vectorMap_one, LinearMap.id_coe, id_eq]
  | mul y z hy hz ihy ihz => rw [vectorMap_mul Q hy hz, LinearMap.comp_apply, ihy, ihz]
  | inv y hy ihy =>
    have h : vectorMap Q y (vectorMap Q y⁻¹ m) = m := by
      rw [← LinearMap.comp_apply, ← vectorMap_mul Q hy (inv_mem hy), mul_inv_cancel,
        vectorMap_one, LinearMap.id_coe, id_eq]
    calc Q (vectorMap Q y⁻¹ m) = Q (vectorMap Q y (vectorMap Q y⁻¹ m)) := (ihy _).symm
      _ = Q m := by rw [h]

/-! ### The action of the Lipschitz group -/

private def vectorEndHom : lipschitzGroup Q →* Module.End R M where
  toFun x := vectorMap Q (x : (CliffordAlgebra Q)ˣ)
  map_one' := vectorMap_one Q
  map_mul' x y := (vectorMap_mul Q x.2 y.2).trans (Module.End.mul_eq_comp _ _).symm

private def vectorActionHom : lipschitzGroup Q →* M ≃ₗ[R] M :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).toMonoidHom.comp
    (vectorEndHom Q).toHomUnits

/-- The automorphism of the quadratic space induced by twisted conjugation by an element of the
Lipschitz group. It is characterized by `ι_lipschitzVectorAction_apply`, which identifies it with
twisted conjugation inside the Clifford algebra. -/
def lipschitzVectorAction (x : lipschitzGroup Q) : M ≃ₗ[R] M :=
  vectorActionHom Q x

variable {Q}

private theorem lipschitzVectorAction_apply (x : lipschitzGroup Q) (m : M) :
    lipschitzVectorAction Q x m = vectorMap Q (x : (CliffordAlgebra Q)ˣ) m := by
  rw [lipschitzVectorAction, vectorActionHom]
  rfl

/-- A Lipschitz element acts on a vector by twisted conjugation inside the Clifford algebra. -/
@[simp]
theorem ι_lipschitzVectorAction_apply (x : lipschitzGroup Q) (m : M) :
    ι Q (lipschitzVectorAction Q x m) =
      involute (Q := Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [lipschitzVectorAction_apply, ι_vectorMap_apply Q x.2, twistedConj_apply]

/-- **A vector acts by the reflection in its orthogonal hyperplane.** These are the generators of
the Lipschitz group, so this identification is what an eventual Cartan-Dieudonné theorem would turn
into surjectivity of `pinToOrthogonal`. -/
@[simp]
theorem lipschitzVectorAction_unitι (v : M) [Invertible (Q v)] :
    lipschitzVectorAction Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ =
      QuadraticMap.reflection Q v := by
  refine LinearEquiv.ext fun m => ?_
  rw [lipschitzVectorAction_apply]
  exact congrFun (congrArg _ (vectorMap_eq_reflection Q v (coe_unitι v))) m

/-- **Twisted conjugation by a Lipschitz element preserves the quadratic form.** The Lipschitz group
is generated by the vectors of invertible norm, which act by reflections; the orthogonal group is a
subgroup, so the whole Lipschitz group acts orthogonally. -/
@[simp]
theorem lipschitzVectorAction_map_app (x : lipschitzGroup Q) (m : M) :
    Q (lipschitzVectorAction Q x m) = Q m := by
  rw [lipschitzVectorAction_apply]
  exact vectorMap_map_app Q x.2 m

variable (Q)

/-- The twisted-conjugation homomorphism from the Lipschitz group to the orthogonal group of the
quadratic form. -/
def lipschitzToOrthogonal : lipschitzGroup Q →* QuadraticMap.orthogonalGroup Q where
  toFun x :=
    ⟨lipschitzVectorAction Q x,
      QuadraticMap.mem_orthogonalGroup_iff.mpr (lipschitzVectorAction_map_app x)⟩
  map_one' := Subtype.ext (map_one (vectorActionHom Q))
  map_mul' x y := Subtype.ext (map_mul (vectorActionHom Q) x y)

@[simp]
theorem coe_lipschitzToOrthogonal_apply (x : lipschitzGroup Q) (m : M) :
    ((lipschitzToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      lipschitzVectorAction Q x m := by
  rw [lipschitzToOrthogonal]
  rfl

/-! ### The Pin and spin groups -/

omit [Invertible (2 : R)] in
/-- The Pin group sits inside the Lipschitz group. -/
def pinToLipschitz : pinGroup Q →* lipschitzGroup Q where
  toFun x := ⟨pinGroup.toUnits x, pinGroup.units_mem_lipschitzGroup x.2⟩
  map_one' := Subtype.ext (map_one (pinGroup.toUnits (Q := Q)))
  map_mul' x y := Subtype.ext (map_mul (pinGroup.toUnits (Q := Q)) x y)

omit [Invertible (2 : R)] in
@[simp]
theorem coe_pinToLipschitz_apply (x : pinGroup Q) :
    ((pinToLipschitz Q x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (x : CliffordAlgebra Q) := by
  rw [pinToLipschitz]
  rfl

/-- **The twisted-conjugation homomorphism `Pin(Q) → O(Q)`.** Its surjectivity (Cartan-Dieudonné)
and the computation of its kernel as `{±1}` are the content of the double-cover theorem, and need
hypotheses not assumed here. -/
def pinToOrthogonal : pinGroup Q →* QuadraticMap.orthogonalGroup Q :=
  (lipschitzToOrthogonal Q).comp (pinToLipschitz Q)

variable {Q}

/-- A Pin element acts through its image in the Lipschitz group. -/
@[simp]
theorem coe_pinToOrthogonal_apply (x : pinGroup Q) (m : M) :
    ((pinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m =
      lipschitzVectorAction Q (pinToLipschitz Q x) m := by
  rw [pinToOrthogonal, MonoidHom.comp_apply, coe_lipschitzToOrthogonal_apply]

/-- A Pin element acts on a vector by twisted conjugation inside the Clifford algebra. Since a Pin
element is unitary, the inverse appearing there is `star`. -/
@[simp]
theorem ι_pinToOrthogonal_apply (x : pinGroup Q) (m : M) :
    ι Q (((pinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) : M ≃ₗ[R] M) m) =
      involute (Q := Q) (x : CliffordAlgebra Q) * ι Q m * star (x : CliffordAlgebra Q) := by
  have hinv : (((pinToLipschitz Q x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) = star (x : CliffordAlgebra Q) :=
    Units.inv_eq_of_mul_eq_one_right (by
      rw [coe_pinToLipschitz_apply]
      exact pinGroup.mul_star_self_of_mem x.2)
  rw [pinToOrthogonal, MonoidHom.comp_apply, coe_lipschitzToOrthogonal_apply,
    ι_lipschitzVectorAction_apply, coe_pinToLipschitz_apply, hinv]

/-- The reflection cut out by a Pin group vector, computed explicitly. With `Q v = -1` the
normalizing scalar `⅟(Q v)` of `TauCeti.QuadraticMap.reflection` is `-1`, so the reflection reads
`m ↦ m + polar Q v m • v`. -/
@[simp]
theorem pinToOrthogonal_ι_apply {v : M} (hv : Q v = -1) (m : M) :
    ((pinToOrthogonal Q ⟨ι Q v, ι_mem_pinGroup hv⟩ : QuadraticMap.orthogonalGroup Q) :
        M ≃ₗ[R] M) m = m + polar Q v m • v := by
  letI : Invertible (Q v) := ⟨-1, by rw [hv]; ring, by rw [hv]; ring⟩
  have hinvOf : ⅟(Q v) = -1 := invOf_eq_right_inv (by rw [hv]; ring)
  have hpin : pinToLipschitz Q ⟨ι Q v, ι_mem_pinGroup hv⟩ =
      ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ :=
    Subtype.ext (Units.ext (by rw [coe_pinToLipschitz_apply, coe_unitι]))
  rw [pinToOrthogonal, MonoidHom.comp_apply, coe_lipschitzToOrthogonal_apply, hpin,
    lipschitzVectorAction_unitι, QuadraticMap.reflection_apply, hinvOf, neg_mul, one_mul, neg_smul,
    sub_neg_eq_add]

variable (Q)

omit [Invertible (2 : R)] in
/-- The spin group sits inside the Pin group. -/
def spinToPin : spinGroup Q →* pinGroup Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_pin hx

variable {Q}

omit [Invertible (2 : R)] in
@[simp]
theorem coe_spinToPin_apply (x : spinGroup Q) :
    ((spinToPin Q x : pinGroup Q) : CliffordAlgebra Q) = (x : CliffordAlgebra Q) := by
  rw [spinToPin]
  rfl

/-- **On the spin group, twisted conjugation is plain conjugation.** A spin element is even, so the
grade involution fixes it, and `TauCeti.CliffordAlgebra.spinToOrthogonal` is the restriction of
`TauCeti.CliffordAlgebra.pinToOrthogonal` along the inclusion of the spin group. -/
@[simp]
theorem pinToOrthogonal_spinToPin (x : spinGroup Q) :
    pinToOrthogonal Q (spinToPin Q x) = spinToOrthogonal Q x := by
  refine Subtype.ext (LinearEquiv.ext fun m => ι_injective Q ?_)
  rw [ι_pinToOrthogonal_apply, coe_spinToPin_apply, spinGroup.involute_eq x.2,
    coe_spinToOrthogonal_apply, ι_spinVectorAction_apply]

end CliffordAlgebra

end TauCeti
