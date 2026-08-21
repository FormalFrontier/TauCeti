/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
import Mathlib.Tactic.Abel

/-!
# Splitting the divisor class group along the degree at a rational point

This file records the structural consequence of having a weight-one base point for the abstract
divisor class group of an order system, continuing the Jacobian roadmap's Layer A.

For an `OrderSystem S` on a type of points `X` whose principal divisors have weighted degree
zero, `WeilDivisor.Principal` builds the descended weighted degree `weightedDegreeClass` on the
class group `Cl(X)` and its kernel `picZero`, the abstract `Pic⁰`. Here we add the missing
structural fact: a base point `x₀` with weight `w x₀ = 1` (the residue-field degree of a
`k`-rational point is `1`) makes the descended weighted degree map split.

Concretely the class `[x₀]` provides a degree-one element, so `n ↦ n • [x₀]` is a group-theoretic
section `degreeSection` of `weightedDegreeClass w h`. The descended weighted degree map is
therefore surjective, and the class group decomposes as the internal direct sum of `picZero` and
the line spanned by `[x₀]`:

`Cl(X) ≃+ picZero × ℤ`.

This is the abstract shadow of the geometric statement that, once a `k`-rational point is chosen,
the full Picard group `Pic(X)` of a smooth proper curve splits as `Pic⁰(X) ⊕ ℤ` by the degree.
Without a rational point the weighted degree map need not be surjective (its image is `d·ℤ`
for the index `d` of the residue degrees), so the weight-one hypothesis is essential and the
construction is non-vacuous.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "`Pic⁰ X = ker deg` (as an
abstract group)", by exhibiting `Cl(X)` as an extension of `ℤ` by `Pic⁰` that the rational point
splits, the form in which the degree-zero part is used downstream. It reuses Tau Ceti's
`WeilDivisor` and `OrderSystem` API and Mathlib's `zmultiplesHom` and `AddMonoidHom`/`AddEquiv`
machinery; no external mathematics is vendored.
-/

@[expose] public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-! ### The degree section at a base point -/

/-- The homomorphism `n ↦ n • [x₀]`, sending an integer `n` to the class of `n` copies of
the base point `x₀`. When `w x₀ = 1`, it is a right inverse of `weightedDegreeClass`,
splitting the degree map. -/
noncomputable def degreeSection (x₀ : X) : ℤ →+ S.ClassGroup :=
  zmultiplesHom S.ClassGroup (S.divisorClass (ofPoint x₀))

@[simp]
lemma degreeSection_apply (x₀ : X) (n : ℤ) :
    S.degreeSection x₀ n = n • S.divisorClass (ofPoint x₀) :=
  rfl

lemma degreeSection_one (x₀ : X) :
    S.degreeSection x₀ 1 = S.divisorClass (ofPoint x₀) := by
  simp

/-- The descended weighted degree of the base-point class is the weight of the base point. -/
lemma weightedDegreeClass_divisorClass_ofPoint (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) : weightedDegreeClass w h (S.divisorClass (ofPoint x₀)) = w x₀ := by
  rw [weightedDegreeClass_divisorClass, weightedDegree_ofPoint]

/-- The descended weighted degree of the degree section at `n` is `n * w x₀`. -/
lemma weightedDegreeClass_degreeSection (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) (n : ℤ) :
    weightedDegreeClass w h (S.degreeSection x₀ n) = n * w x₀ := by
  rw [degreeSection_apply, map_zsmul, weightedDegreeClass_divisorClass_ofPoint, zsmul_eq_mul,
    Int.cast_id]

/-- With a weight-one base point, the degree section is a right inverse of the descended
weighted degree: `weightedDegreeClass ∘ degreeSection = id`. -/
lemma weightedDegreeClass_comp_degreeSection (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    (weightedDegreeClass w h).comp (S.degreeSection x₀) = AddMonoidHom.id ℤ :=
  AddMonoidHom.ext fun n => by simp [hx₀]

lemma weightedDegreeClass_degreeSection_of_weight_one (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (n : ℤ) :
    weightedDegreeClass w h (S.degreeSection x₀ n) = n := by
  rw [weightedDegreeClass_degreeSection, hx₀, mul_one]

/-- With a weight-one base point, the descended weighted degree is surjective onto `ℤ`. -/
lemma weightedDegreeClass_surjective (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : Function.Surjective (weightedDegreeClass w h) :=
  Function.RightInverse.surjective fun n =>
    S.weightedDegreeClass_degreeSection_of_weight_one w h hx₀ n

/-- With a weight-one base point, the degree section is injective. -/
lemma degreeSection_injective (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : Function.Injective (S.degreeSection x₀) :=
  Function.LeftInverse.injective fun n =>
    S.weightedDegreeClass_degreeSection_of_weight_one w h hx₀ n

/-! ### The product decomposition -/

/-- The degree-correction homomorphism
`c ↦ c - (weightedDegreeClass w h c) • [x₀]`. With a weight-one base point its image lands in
`picZero`, and together with `degreeSection` it splits the class group as `picZero × ℤ`. -/
noncomputable def degreeCorrection (w : X → ℤ) (h : S.IsWeightedDegreeZero w) (x₀ : X) :
    S.ClassGroup →+ S.ClassGroup :=
  AddMonoidHom.id S.ClassGroup - (S.degreeSection x₀).comp (weightedDegreeClass w h)

@[simp]
lemma degreeCorrection_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w) (x₀ : X)
    (c : S.ClassGroup) :
    S.degreeCorrection w h x₀ c =
      c - (weightedDegreeClass w h c) • S.divisorClass (ofPoint x₀) := by
  simp [degreeCorrection]

/-- Changing the base point in the class-group degree correction adds the weighted degree of the
class times the base-point-change divisor class. -/
lemma degreeCorrection_change_base (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ y₀ : X) (c : S.ClassGroup) :
    S.degreeCorrection w h y₀ c =
      S.degreeCorrection w h x₀ c +
        weightedDegreeClass w h c • S.divisorClass (pointDifference x₀ y₀) := by
  rw [degreeCorrection_apply, degreeCorrection_apply, pointDifference, map_sub, zsmul_sub]
  abel_nf

/-- The degree correction lands in `picZero`: the degree-corrected class has weighted degree zero,
provided the base point has weight one. -/
lemma degreeCorrection_mem_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (c : S.ClassGroup) :
    S.degreeCorrection w h x₀ c ∈ picZero w h := by
  rw [mem_picZero, degreeCorrection_apply, map_sub, map_zsmul,
    weightedDegreeClass_divisorClass_ofPoint, hx₀, smul_eq_mul, mul_one, sub_self]

/-- Degree correction acts on a divisor class by subtracting the base-point divisor scaled by the
weighted degree of any representative. -/
lemma degreeCorrection_divisorClass (w : X → ℤ) (h : S.IsWeightedDegreeZero w) (x₀ : X)
    (D : WeilDivisor X) :
    S.degreeCorrection w h x₀ (S.divisorClass D) =
      S.divisorClass (D - weightedDegree w D • ofPoint x₀) := by
  rw [degreeCorrection_apply, weightedDegreeClass_divisorClass, map_sub, map_zsmul]

/-- A class already in `picZero` is unchanged by degree correction. -/
lemma degreeCorrection_eq_self_of_mem_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) {c : S.ClassGroup} (hc : c ∈ picZero w h) :
    S.degreeCorrection w h x₀ c = c := by
  rw [degreeCorrection_apply, (mem_picZero w h).mp hc, zero_zsmul, sub_zero]

/-- The degree correction of a coerced `picZero` class is the same class in the ambient class
group. -/
lemma degreeCorrection_coe_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) (p : picZero w h) :
    S.degreeCorrection w h x₀ (p : S.ClassGroup) = p :=
  S.degreeCorrection_eq_self_of_mem_picZero w h x₀ p.property

/-- The forward map
`c ↦ (c - (weightedDegreeClass w h c) • [x₀], weightedDegreeClass w h c)` of the degree splitting
at a weight-one base point `x₀`: the first component is the weighted-degree-corrected class,
which lands in `picZero`, and the second is the descended weighted degree. Together with
`degreeSplitInverse` this assembles the product decomposition
`classGroupAddEquivPicZeroProdInt`. -/
noncomputable def degreeSplitForward (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : S.ClassGroup →+ picZero w h × ℤ :=
  ((S.degreeCorrection w h x₀).codRestrict (picZero w h)
      (S.degreeCorrection_mem_picZero w h hx₀)).prod (weightedDegreeClass w h)

@[simp]
private lemma degreeSplitForward_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (c : S.ClassGroup) :
    S.degreeSplitForward w h hx₀ c =
      (⟨S.degreeCorrection w h x₀ c, S.degreeCorrection_mem_picZero w h hx₀ c⟩,
        weightedDegreeClass w h c) :=
  rfl

/-- The inverse map `(p, n) ↦ p + n • [x₀]` of the degree splitting at a base point `x₀`:
add `n` copies of the base-point class to a class of weighted degree zero. -/
noncomputable def degreeSplitInverse (w : X → ℤ) (h : S.IsWeightedDegreeZero w) (x₀ : X) :
    picZero w h × ℤ →+ S.ClassGroup :=
  (picZero w h).subtype.comp (AddMonoidHom.fst (picZero w h) ℤ) +
    (S.degreeSection x₀).comp (AddMonoidHom.snd (picZero w h) ℤ)

@[simp]
private lemma degreeSplitInverse_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w) (x₀ : X)
    (p : picZero w h) (n : ℤ) :
    S.degreeSplitInverse w h x₀ (p, n) =
      (p : S.ClassGroup) + n • S.divisorClass (ofPoint x₀) := by
  simp [degreeSplitInverse]

lemma degreeSplitInverse_degreeSplitForward (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (c : S.ClassGroup) :
    S.degreeSplitInverse w h x₀ (S.degreeSplitForward w h hx₀ c) = c := by
  rw [degreeSplitForward_apply, degreeSplitInverse_apply]
  -- The preceding rewrites leave only the subtype coercion from the `picZero` component.
  change S.degreeCorrection w h x₀ c +
    (weightedDegreeClass w h c) • S.divisorClass (ofPoint x₀) = c
  rw [degreeCorrection_apply, sub_add_cancel]

private lemma degreeSplitForward_degreeSplitInverse (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (p : picZero w h) (n : ℤ) :
    S.degreeSplitForward w h hx₀ (S.degreeSplitInverse w h x₀ (p, n)) = (p, n) := by
  have hp : weightedDegreeClass w h (p : S.ClassGroup) = 0 := (mem_picZero w h).mp p.property
  have key : weightedDegreeClass w h (S.degreeSplitInverse w h x₀ (p, n)) = n := by
    rw [degreeSplitInverse_apply, map_add, map_zsmul, weightedDegreeClass_divisorClass_ofPoint,
      hx₀, hp, smul_eq_mul, mul_one, zero_add]
  refine Prod.ext (Subtype.ext ?_) ?_
  · -- `Prod.ext` and `Subtype.ext` reduce the first projection to equality in `S.ClassGroup`.
    change S.degreeCorrection w h x₀ (S.degreeSplitInverse w h x₀ (p, n)) = (p : S.ClassGroup)
    rw [degreeCorrection_apply, key, degreeSplitInverse_apply, add_sub_cancel_right]
  · -- The second projection is definitionally the weighted degree of the reconstructed class.
    change weightedDegreeClass w h (S.degreeSplitInverse w h x₀ (p, n)) = n
    exact key

/-- The class group of an order system with weighted-degree-zero principal divisors and a
weight-one base point splits as the direct product of the abstract `Pic⁰` and `ℤ`.

The forward map sends a class `c` to its weighted-degree-corrected part
`c - (weightedDegreeClass w h c) • [x₀]` in `picZero` together with
`weightedDegreeClass w h c`; the inverse sends `(p, n)` to `p + n • [x₀]`. This is the abstract
form of the splitting `Pic(X) ≃ Pic⁰(X) ⊕ ℤ` of a smooth proper curve with a rational point. -/
noncomputable def classGroupAddEquivPicZeroProdInt (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.ClassGroup ≃+ picZero w h × ℤ :=
  AddMonoidHom.toAddEquiv (S.degreeSplitForward w h hx₀) (S.degreeSplitInverse w h x₀)
    (AddMonoidHom.ext fun c => S.degreeSplitInverse_degreeSplitForward w h hx₀ c)
    (AddMonoidHom.ext fun x => by
      obtain ⟨p, n⟩ := x
      exact S.degreeSplitForward_degreeSplitInverse w h hx₀ p n)

@[simp]
lemma classGroupAddEquivPicZeroProdInt_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (c : S.ClassGroup) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀ c =
      (⟨S.degreeCorrection w h x₀ c, S.degreeCorrection_mem_picZero w h hx₀ c⟩,
        weightedDegreeClass w h c) :=
  rfl

@[simp]
lemma classGroupAddEquivPicZeroProdInt_symm_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (p : picZero w h) (n : ℤ) :
    (S.classGroupAddEquivPicZeroProdInt w h hx₀).symm (p, n) =
      (p : S.ClassGroup) + n • S.divisorClass (ofPoint x₀) :=
  S.degreeSplitInverse_apply w h x₀ p n

/-- Under the splitting `Cl(X) ≃+ picZero × ℤ`, a coerced `picZero` class has `Pic⁰` component
itself and degree component `0`. -/
lemma classGroupAddEquivPicZeroProdInt_coe_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (p : picZero w h) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀ (p : S.ClassGroup) = (p, 0) := by
  rw [classGroupAddEquivPicZeroProdInt_apply]
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact S.degreeCorrection_coe_picZero w h x₀ p
  · exact (mem_picZero w h).mp p.property

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
