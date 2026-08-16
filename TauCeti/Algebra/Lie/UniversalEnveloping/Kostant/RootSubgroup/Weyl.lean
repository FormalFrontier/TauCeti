/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Lie.Sl2.WeylAutomorphism
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic

/-!
# The Weyl element of a Kostant root subgroup pair

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ`, let `M ≤ V` be a
`U_ℤ`-stable additive subgroup, and let `eᵢ`, `eⱼ` be distinguished root vectors whose images span,
together with a distinguished Cartan vector `h c`, an `sl₂` triple in `Module.End ℚ V`. Chevalley's
**Weyl element** is the product of root subgroup elements

```text
n = x_i(1) x_j(-1) x_i(1),
```

the group-level representative of the reflection `s_α` for `α` the root of `eᵢ`.

Its two defining properties are proved here over an *arbitrary* commutative ring of points, not
only over `ℚ`. First, `n` is defined over `ℤ`: the three exponentials have integer parameters, so
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints` is the scalar extension of one integral
automorphism of the lattice `M`, namely the restriction of the unit
`TauCeti.weylUnit = exp ρ(eᵢ) · exp (-ρ(eⱼ)) · exp ρ(eᵢ)` of `Module.End ℚ V`. Second, conjugation
by it interchanges the two root subgroups with a sign,

```text
n x_i(u) n⁻¹ = x_j(-u)     for every u in the ring of points,
```

which is `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_baseChangeExp`. Nothing about
the parameter ring enters that proof: the whole content is the Lie-algebra identity
`n ρ(eᵢ) n⁻¹ = -ρ(eⱼ)` of `TauCeti.weylUnit_conj_e`, which passes through the divided powers
because conjugation by a unit is an algebra automorphism. In particular the relation holds in
characteristic two and three, where the exponential series itself is unavailable.

The same mechanism gives the action on weights:
`TauCeti.UniversalEnvelopingAlgebra.weylUnit_apply_eigenvector` says that `n` carries an
eigenvector of `ρ(h c)` of eigenvalue `m` inside `M` to an eigenvector of eigenvalue `-m`, again
inside `M`. That is the reflection `s_α` acting on the weight lattice, realised by an element of the
Chevalley group rather than only by an automorphism of the Lie algebra.

This is the normaliser-of-the-torus half of the pinning data of Layer 9 of the ReductiveGroups
roadmap: the Chevalley commutator relations of
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Commutator.lean` describe how two
root subgroups interact, and the relations here describe how the reflection permutes them.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints`: the Weyl element on points valued in an
  arbitrary commutative ring.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_toLinearMap_eq`: it is the product
  `x_i(1) x_j(-1) x_i(1)` of root subgroup elements.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_conj_baseChangeExp`: conjugating the root
  subgroup of `eᵢ` by it gives the root subgroup of `eⱼ` with a negated parameter.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantWeylPoints`: it is natural in the ring of points.
* `TauCeti.UniversalEnvelopingAlgebra.weylUnit_apply_eigenvector`: it reflects the weight of an
  eigenvector of a distinguished Cartan vector.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable {i j : ι} {c : κ}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))

include hM hi hj hT

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-! ## Stability of the lattice under the Weyl element -/

/-- The Weyl element of a Kostant root pair preserves the lattice: it is a product of root
subgroup elements at integer parameters, each of which does. -/
theorem weylUnit_smul_mem {v : V} (hv : v ∈ M) :
    ((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) • v ∈ M := by
  rw [coe_weylUnit, mul_smul, mul_smul]
  exact exp_smul_mem hi (fun n _ hw =>
      dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hw)
    (exp_neg_smul_mem hj (fun n _ hw =>
      dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hw)
      (exp_smul_mem hi (fun n _ hw =>
        dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hw) hv))

/-- The inverse of the Weyl element preserves the lattice, by the same computation with every
exponent negated. -/
theorem inv_weylUnit_smul_mem {v : V} (hv : v ∈ M) :
    (((weylUnit hT hi hj : (Module.End ℚ V)ˣ)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) • v ∈ M := by
  rw [coe_inv_weylUnit, mul_smul, mul_smul]
  exact exp_neg_smul_mem hi (fun n _ hw =>
      dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hw)
    (exp_smul_mem hj (fun n _ hw =>
      dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hw)
      (exp_neg_smul_mem hi (fun n _ hw =>
        dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hw) hv))

/-- The Weyl element restricted to an integral automorphism of the lattice. -/
noncomputable def kostantWeylRestrict : M ≃ₗ[ℤ] M :=
  integralUnitRestrict (weylUnit hT hi hj) M
    (fun _ hv => weylUnit_smul_mem e h ρ M hM hi hj hT hv)
    (fun _ hv => inv_weylUnit_smul_mem e h ρ M hM hi hj hT hv)

@[simp]
theorem coe_kostantWeylRestrict_apply (v : M) :
    ((kostantWeylRestrict e h ρ M hM hi hj hT v : M) : V) =
      ((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) • (v : V) := by
  simp [kostantWeylRestrict]

section Points

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-! ## The Weyl element on points -/

/-- **The Weyl element of a Kostant root pair**, on points valued in a commutative ring `A`.

It is the scalar extension of a single integral automorphism of the lattice `M`. That it is also
the Chevalley product `x_i(1) x_j(-1) x_i(1)` of root subgroup elements is
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_toLinearMap_eq`. -/
noncomputable def kostantWeylPoints (A : Type*) [CommRing A] [Algebra ℤ A] :
    A ⊗[ℤ] M ≃ₗ[A] A ⊗[ℤ] M :=
  LinearEquiv.ofLinearMap
    ((kostantWeylRestrict e h ρ M hM hi hj hT : M →ₗ[ℤ] M).baseChange A)
    (((kostantWeylRestrict e h ρ M hM hi hj hT).symm : M →ₗ[ℤ] M).baseChange A)
    (by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r v => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb])
    (by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r v => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb])

@[simp]
theorem kostantWeylPoints_toLinearMap :
    (kostantWeylPoints e h ρ M hM hi hj hT A).toLinearMap =
      (kostantWeylRestrict e h ρ M hM hi hj hT : M →ₗ[ℤ] M).baseChange A :=
  (rfl)

@[simp]
theorem kostantWeylPoints_symm_toLinearMap :
    (kostantWeylPoints e h ρ M hM hi hj hT A).symm.toLinearMap =
      ((kostantWeylRestrict e h ρ M hM hi hj hT).symm : M →ₗ[ℤ] M).baseChange A :=
  (rfl)

@[simp]
theorem kostantWeylPoints_apply_tmul (r : A) (v : M) :
    kostantWeylPoints e h ρ M hM hi hj hT A (r ⊗ₜ[ℤ] v) =
      r ⊗ₜ[ℤ] kostantWeylRestrict e h ρ M hM hi hj hT v := by
  rw [← LinearEquiv.coe_coe, kostantWeylPoints_toLinearMap, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe]

/-- **The Weyl element is the Chevalley product `x_i(1) x_j(-1) x_i(1)`.**

Each factor is a root subgroup element at an integer parameter, hence already defined over `ℤ`;
this identifies their product with the scalar extension of the integral automorphism
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict`. -/
theorem kostantWeylPoints_toLinearMap_eq :
    (kostantWeylPoints e h ρ M hM hi hj hT A).toLinearMap =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
          (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
          (1 : A) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) M
          (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv)
          (-1 : A) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
          (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
          (1 : A) := by
  have hone : ((1 : ℤ) : A) = (1 : A) := Int.cast_one
  have hneg : ((-1 : ℤ) : A) = (-1 : A) := by rw [Int.cast_neg, Int.cast_one]
  rw [kostantWeylPoints_toLinearMap, ← hneg, ← hone,
    baseChangeExp_intCast (R := A) _ M _ hi 1, baseChangeExp_intCast (R := A) _ M _ hj (-1),
    ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul]
  congr 1
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [LinearEquiv.coe_coe, coe_kostantWeylRestrict_apply, coe_integralExpZSMul_apply,
    coe_weylUnit, one_zsmul, neg_one_zsmul, mul_smul]

/-- **Conjugation by the Weyl element interchanges the two root subgroups.** Over every ring of
points, `n x_i(u) n⁻¹ = x_j(-u)`.

Only the Lie-algebra relation `n ρ(eᵢ) n⁻¹ = -ρ(eⱼ)` is used, so the identity is insensitive to
the characteristic of the ring of points. -/
theorem kostantWeylPoints_conj_baseChangeExp (u : A) :
    (kostantWeylPoints e h ρ M hM hi hj hT A).toLinearMap *
          baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
            (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv) u *
        (kostantWeylPoints e h ρ M hM hi hj hT A).symm.toLinearMap =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) M
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv) (-u) := by
  have hMj : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) • v ∈ M :=
    fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv
  have hMneg : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (-ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) • v ∈ M := by
    intro n v hv
    rcases Nat.even_or_odd n with hn | hn
    · rw [Associative.dividedPower_neg, hn.neg_one_pow, one_smul]
      exact hMj n v hv
    · rw [Associative.dividedPower_neg, hn.neg_one_pow, neg_one_smul, neg_smul]
      exact neg_mem (hMj n v hv)
  have hconj : ((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) *
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) *
      (((weylUnit hT hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V) =
        -ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j)) := weylUnit_conj_e hT hi hj
  have hMconj : ∀ n, ∀ v ∈ M, Associative.dividedPower n
      (((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) *
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) *
        (((weylUnit hT hi hj)⁻¹ : (Module.End ℚ V)ˣ) : Module.End ℚ V)) • v ∈ M := by
    rw [hconj]
    exact hMneg
  rw [kostantWeylPoints_toLinearMap, kostantWeylPoints_symm_toLinearMap, kostantWeylRestrict,
    baseChange_integralUnitRestrict_conj_baseChangeExp
      (R := A) _ M _ _ _ _ hMconj hi u,
    baseChangeExp_congr hconj M hMconj hMneg, baseChangeExp_neg _ M hMneg hMj hj]

/-- The Weyl element is natural in the ring of points: it is the scalar extension of a single
integral automorphism, so applying a ring homomorphism to the scalar coordinate of every tensor
intertwines the two. -/
theorem map_kostantWeylPoints {B : Type*} [CommRing B] [Algebra ℤ B] (φ : A →ₐ[ℤ] B)
    (z : A ⊗[ℤ] M) :
    TensorProduct.map φ.toLinearMap LinearMap.id
        (kostantWeylPoints e h ρ M hM hi hj hT A z) =
      kostantWeylPoints e h ρ M hM hi hj hT B
        (TensorProduct.map φ.toLinearMap LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => simp
  | add a b ha hb => simp [ha, hb]

end Points

/-! ## The reflected weight -/

omit hM in
/-- **The Weyl element reflects weights.** If `v` is an eigenvector of a distinguished Cartan
vector with eigenvalue `m`, then its image under the Weyl element is an eigenvector with the
reflected eigenvalue `-m`; by `TauCeti.UniversalEnvelopingAlgebra.weylUnit_smul_mem` that image
again lies in the lattice.

For the `sl₂` triple of a root `α` this is the reflection `s_α` acting on the weight lattice of
`M`, realised by an element of the Chevalley group rather than only by an automorphism of the Lie
algebra. -/
theorem weylUnit_apply_eigenvector {v : V} {m : ℚ}
    (hmv : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)) v = m • v) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c))
        (((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) =
      (-m) • (((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) := by
  have hw : ((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) *
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)) =
        -ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)) *
          ((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) := by
    rw [← weylUnit_conj_h hT hi hj, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have happ := congrArg (fun f : Module.End ℚ V => f v) hw
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at happ
  have key : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c))
      (((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V) v) =
        -(((weylUnit hT hi hj : (Module.End ℚ V)ˣ) : Module.End ℚ V)
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)) v)) := by
    rw [happ, neg_neg]
  rw [key, hmv, map_smul, ← neg_smul]

end TauCeti.UniversalEnvelopingAlgebra
