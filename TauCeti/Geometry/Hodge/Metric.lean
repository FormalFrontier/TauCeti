/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Hodge.Polarization
public import TauCeti.Geometry.Hodge.WeilOperator

import Mathlib.Algebra.Field.NegOnePow

/-!
# The Hodge metric of a polarized Hodge structure

A polarization `Q` and the Weil operator `C` determine a positive-definite Hermitian form on the
complexification of a pure Hodge structure. In Mathlib's convention Hermitian forms are conjugate
linear in the first argument, so the form constructed here is

`h(x, y) = Q(C y, conj x)`.

This is the argument-reversed form of the convention `Q(C x, conj y)` often used in Hodge theory;
the two conventions have the same diagonal. The Hodge--Riemann positivity axiom gives positivity on
each Hodge component. Orthogonality of distinct components and the internal Hodge decomposition then
give positivity on the whole complexification.

## Main declarations

* `TauCeti.Hodge.Polarization.Q_weilOperator`: the Weil operator preserves the complexified
  polarizing form.
* `TauCeti.Hodge.Polarization.hodgeForm`: the sesquilinear Hodge form.
* `TauCeti.Hodge.Polarization.hodgeForm_isSymm`: the Hodge form is Hermitian.
* `TauCeti.Hodge.Polarization.hodgeForm_positive`: the Hodge form is positive on nonzero vectors.
* `TauCeti.Hodge.Polarization.hodgeForm_self_eq_zero`: the diagonal detects the zero vector.
* `TauCeti.Hodge.Polarization.hodgeForm_isPosSemidef`: the Hodge form is positive semidefinite in
  Mathlib's bundled vocabulary.
* `TauCeti.Hodge.Polarization.hodgeInnerProductCore`: the Hodge form packaged as an
  `InnerProductSpace.Core`.

The construction and its sign convention follow Voisin, *Hodge Theory and Complex Algebraic
Geometry I*, Section 7.1.2, and Peters--Steenbrink, *Mixed Hodge Structures*, Section 2. This is the
positive Hermitian form targeted in Layer L1 of `TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge

open scoped ComplexOrder

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

namespace Polarization

variable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n}

private theorem Q_weilOperator_of_mem (P : Polarization hℂ hs) {p q : ℤ} {x y : Vℂ}
    (hx : x ∈ hs.piece p) (hy : y ∈ hs.piece q) :
    P.Q (hs.weilOperator x) (hs.weilOperator y) = P.Q x y := by
  by_cases hpq : p + q = n
  · have hexp : (2 * q - n) + (2 * p - n) = 0 := by omega
    rw [hs.weilOperator_apply_of_mem hx, hs.weilOperator_apply_of_mem hy]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← zpow_add₀ Complex.I_ne_zero, hexp, zpow_zero, one_mul]
  · rw [P.Q_def, P.isPolarization.orthogonal_piece hpq
        (hs.weilOperator_mem_piece hx) (hs.weilOperator_mem_piece hy),
      P.isPolarization.orthogonal_piece hpq hx hy]

/-- The Weil operator preserves the complexified polarizing form: `Q(Cx, Cy) = Q(x, y)`. -/
theorem Q_weilOperator (P : Polarization hℂ hs) (x y : Vℂ) :
    P.Q (hs.weilOperator x) (hs.weilOperator y) = P.Q x y := by
  refine hs.piece_induction_on
    (motive := fun x ↦ P.Q (hs.weilOperator x) (hs.weilOperator y) = P.Q x y) x
    (fun p x hx ↦ ?_) (by simp) fun x₁ x₂ hx₁ hx₂ ↦ ?_
  · refine hs.piece_induction_on
      (motive := fun y ↦ P.Q (hs.weilOperator x) (hs.weilOperator y) = P.Q x y) y
      (fun q y hy ↦ P.Q_weilOperator_of_mem hx hy)
      (by rw [map_zero hs.weilOperator, map_zero, map_zero])
      fun y₁ y₂ hy₁ hy₂ ↦ ?_
    simp only [map_add, hy₁, hy₂]
  · simp only [map_add, LinearMap.add_apply, hx₁, hx₂]

/-- Moving the Weil operator between the two arguments of the polarizing form introduces the
weight sign: `Q(Cx, y) = (-1)^n Q(x, Cy)`. -/
theorem Q_weilOperator_left (P : Polarization hℂ hs) (x y : Vℂ) :
    P.Q (hs.weilOperator x) y = (n.negOnePow : ℤ) * P.Q x (hs.weilOperator y) := by
  have h := P.Q_weilOperator x (hs.weilOperator y)
  have hCC : hs.weilOperator (hs.weilOperator y) = ((-1 : ℂ) ^ n) • y := by
    have hcomp := LinearMap.congr_fun hs.weilOperator_comp_weilOperator y
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using hcomp
  rw [hCC] at h
  rw [map_smul, smul_eq_mul] at h
  have hsign : (((n.negOnePow : ℤ) : ℂ)) = (-1 : ℂ) ^ n := by
    obtain hn | hn := n.even_or_odd
    · simp [Int.negOnePow_even n hn, hn.neg_one_zpow]
    · simp [Int.negOnePow_odd n hn, hn.neg_one_zpow]
  rw [hsign]
  have hsquare : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
    norm_num
  calc
    P.Q (hs.weilOperator x) y = 1 * P.Q (hs.weilOperator x) y := by rw [one_mul]
    _ = (((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) * P.Q (hs.weilOperator x) y := by
      rw [hsquare]
    _ = ((-1 : ℂ) ^ n) * P.Q x (hs.weilOperator y) := by rw [mul_assoc, h]

/-- The Hodge form associated to a polarization, in Mathlib's convention of conjugate linearity in
the first argument: `h(x, y) = Q(Cy, conj x)`. -/
noncomputable def hodgeForm (P : Polarization hℂ hs) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y ↦ P.Q (hs.weilOperator y) (latticeConj hℂ x))
    (by simp) (by simp) (by simp) (by simp)

/-- Evaluation of the Hodge form. -/
@[simp]
theorem hodgeForm_apply (P : Polarization hℂ hs) (x y : Vℂ) :
    P.hodgeForm x y = P.Q (hs.weilOperator y) (latticeConj hℂ x) :=
  (rfl)

/-- Distinct Hodge components are orthogonal for the Hodge form. -/
theorem hodgeForm_orthogonal_piece (P : Polarization hℂ hs) {p q : ℤ} (hpq : p ≠ q)
    {x y : Vℂ} (hx : x ∈ hs.piece p) (hy : y ∈ hs.piece q) :
    P.hodgeForm x y = 0 := by
  rw [P.hodgeForm_apply, hs.weilOperator_apply_of_mem hy]
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, P.Q_def,
    P.isPolarization.orthogonal_piece (p := q) (p' := n - p) (by omega) hy
      (by simpa using hs.conj_mem_piece hx), mul_zero]

/-- On a Hodge component, the diagonal of the Hodge form is exactly the positive expression in the
second Hodge--Riemann relation. -/
theorem hodgeForm_self_of_mem (P : Polarization hℂ hs) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) :
    P.hodgeForm x x = Complex.I ^ (2 * p - n) * P.Q x (latticeConj hℂ x) := by
  rw [P.hodgeForm_apply, hs.weilOperator_apply_of_mem hx, map_smul,
    LinearMap.smul_apply, smul_eq_mul]

/-- The Hodge form is positive on every nonzero vector in a single Hodge component. -/
theorem hodgeForm_positive_of_mem (P : Polarization hℂ hs) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) (hx0 : x ≠ 0) : 0 < P.hodgeForm x x := by
  rw [P.hodgeForm_self_of_mem hx]
  exact P.Q_positive p hx hx0

open scoped Classical in
private theorem hodgeForm_self_eq_sum (P : Polarization hℂ hs) (x : Vℂ) :
    P.hodgeForm x x =
      ∑ p ∈ (hs.decomposition x).support,
        P.hodgeForm ((hs.decomposition x p : hs.piece p) : Vℂ)
          ((hs.decomposition x p : hs.piece p) : Vℂ) := by
  classical
  let z := hs.decomposition x
  have hxsum : x = ∑ p ∈ z.support, ((z p : hs.piece p) : Vℂ) := by
    calc
      x = hs.decomposition.symm z := by simp [z]
      _ = DirectSum.coeLinearMap hs.piece z := hs.decomposition_symm_apply z
      _ = DirectSum.coeLinearMap hs.piece
          (∑ p ∈ z.support, DirectSum.of (fun q ↦ hs.piece q) p (z p)) := by
            rw [DirectSum.sum_support_of]
      _ = ∑ p ∈ z.support, ((z p : hs.piece p) : Vℂ) := by simp
  conv_lhs => rw [hxsum]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  apply Finset.sum_eq_single p
  · intro q hq hqp
    exact P.hodgeForm_orthogonal_piece hqp (z q).property (z p).property
  · exact fun hp' ↦ (hp' hp).elim

/-- The Hodge form is positive definite on the whole complexification. -/
theorem hodgeForm_positive (P : Polarization hℂ hs) {x : Vℂ} (hx : x ≠ 0) :
    0 < P.hodgeForm x x := by
  classical
  rw [P.hodgeForm_self_eq_sum]
  let z := hs.decomposition x
  have hz : z ≠ 0 := by
    intro hz
    apply hx
    apply hs.decomposition.injective
    simpa [z] using hz
  have hsupp : z.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, DFinsupp.support_eq_empty]
    exact hz
  suffices 0 < ∑ p ∈ z.support,
      P.hodgeForm ((z p : hs.piece p) : Vℂ) ((z p : hs.piece p) : Vℂ) by
    simpa [z] using this
  rw [Complex.pos_iff]
  constructor
  · rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
    apply Finset.sum_pos'
    · intro p hp
      by_cases hzp : z p = 0
      · simp [hzp]
      · have hzp' : ((z p : hs.piece p) : Vℂ) ≠ 0 := by
          intro h
          apply hzp
          exact Subtype.ext h
        exact (Complex.nonneg_iff.mp <|
          (P.hodgeForm_positive_of_mem (z p).property hzp').le).1
    · obtain ⟨p, hp⟩ := hsupp
      refine ⟨p, hp, (Complex.pos_iff.mp <| P.hodgeForm_positive_of_mem (z p).property ?_).1⟩
      intro h
      apply DFinsupp.mem_support_iff.mp hp
      exact Subtype.ext h
  · rw [← Complex.imCLM_apply, map_sum]
    simp only [Complex.imCLM_apply]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hzp : z p = 0
    · simp [hzp]
    · have hzp' : ((z p : hs.piece p) : Vℂ) ≠ 0 := by
        intro h
        apply hzp
        exact Subtype.ext h
      exact (Complex.nonneg_iff.mp <|
        (P.hodgeForm_positive_of_mem (z p).property hzp').le).2.symm

/-- The diagonal of the Hodge form is nonnegative. -/
theorem hodgeForm_nonnegative (P : Polarization hℂ hs) (x : Vℂ) :
    0 ≤ P.hodgeForm x x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (P.hodgeForm_positive hx).le

/-- The diagonal of the Hodge form vanishes exactly on the zero vector. -/
@[simp]
theorem hodgeForm_self_eq_zero (P : Polarization hℂ hs) {x : Vℂ} :
    P.Q (hs.weilOperator x) (latticeConj hℂ x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hx0
    exact (P.hodgeForm_positive hx0).ne' hx
  · rintro rfl
    simp

/-- The Hodge form is Hermitian: `conj (h(x, y)) = h(y, x)`. -/
theorem hodgeForm_isSymm (P : Polarization hℂ hs) : P.hodgeForm.IsSymm := by
  constructor
  intro x y
  rw [P.hodgeForm_apply, P.hodgeForm_apply]
  calc
    starRingEnd ℂ (P.Q (hs.weilOperator y) (latticeConj hℂ x)) =
        P.Q (latticeConj hℂ (hs.weilOperator y)) x := by
          rw [← P.Q_conj, latticeConj_apply_apply]
    _ = P.Q (hs.weilOperator (latticeConj hℂ y)) x := by
      exact congrArg (fun z ↦ P.Q z x) <|
        by simpa only [latticeConjugation_toEquiv_apply] using hs.conj_weilOperator y
    _ = (n.negOnePow : ℤ) * P.Q x (hs.weilOperator (latticeConj hℂ y)) :=
      P.Q_symm_weight _ _
    _ = P.Q (hs.weilOperator x) (latticeConj hℂ y) :=
      (P.Q_weilOperator_left x (latticeConj hℂ y)).symm

/-- The Hodge form is positive semidefinite in Mathlib's bundled sesquilinear-form vocabulary. -/
theorem hodgeForm_isPosSemidef (P : Polarization hℂ hs) : P.hodgeForm.IsPosSemidef where
  isSymm := P.hodgeForm_isSymm
  isNonneg := ⟨P.hodgeForm_nonnegative⟩

/-- The Hodge form is nondegenerate. -/
theorem hodgeForm_nondegenerate (P : Polarization hℂ hs) : P.hodgeForm.Nondegenerate := by
  constructor
  · intro x hx
    have hconj : latticeConj hℂ x = 0 := P.Q_nondegenerate.2 _ fun z ↦ by
      let y := hs.weilOperatorEquiv.symm z
      have hy : hs.weilOperator y = z := by
        rw [← hs.weilOperatorEquiv_apply]
        exact hs.weilOperatorEquiv.apply_symm_apply z
      simpa [P.hodgeForm_apply, hy] using hx y
    have h := congrArg (latticeConj hℂ) hconj
    rw [latticeConj_apply_apply, map_zero] at h
    exact h
  · intro y hy
    have hC : hs.weilOperator y = 0 := P.Q_nondegenerate.1 _ fun z ↦ by
      let x := latticeConj hℂ z
      simpa [P.hodgeForm_apply, x] using hy x
    apply hs.weilOperator_bijective.1
    simpa only [map_zero] using hC

/-- The Hodge form, packaged as the core of a complex inner-product-space structure. This is data,
not a global instance, so choosing a polarization does not create competing typeclass instances. -/
@[implicit_reducible]
noncomputable def hodgeInnerProductCore (P : Polarization hℂ hs) :
    InnerProductSpace.Core ℂ Vℂ where
  inner := fun x y ↦ P.hodgeForm x y
  conj_inner_symm x y := P.hodgeForm_isSymm.eq y x
  re_inner_nonneg x := (Complex.nonneg_iff.mp (P.hodgeForm_nonnegative x)).1
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := P.hodgeForm_self_eq_zero.mp hx

/-- The inner product in `hodgeInnerProductCore` is the Hodge form. -/
@[simp]
theorem hodgeInnerProductCore_inner (P : Polarization hℂ hs) (x y : Vℂ) :
    @inner ℂ Vℂ P.hodgeInnerProductCore.toInner x y = P.hodgeForm x y :=
  (rfl)

end Polarization

end TauCeti.Hodge
