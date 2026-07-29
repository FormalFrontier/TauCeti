/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring

/-!
# Weil divisors as finite integer combinations of points

This file provides the first, purely combinatorial piece of the Jacobian roadmap's Layer A:
Weil divisors are finite formal integer sums of points. The scheme-theoretic predicates
which decide which points are codimension-one points, the principal-divisor map, and the
comparison with Cartier divisors are deliberately not bundled here; those are later geometric
constructions.

The API here records the free-abelian-group operations needed before that geometry exists:
point divisors, effectivity, pushforward of formal sums along a map of point sets, and both
the unweighted degree and the weighted degree used for curves over a field. It also packages
the degree-zero subgroups that later receive principal divisors and model the abstract
`Pic⁰` kernel before the Picard functor and Picard scheme exist.

For a curve over `k`, the intended weighted degree has weight
`x ↦ [κ(x) : k]`; this file only supplies the formal finite-sum operation against an arbitrary
integer-valued weight.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve: Weil divisors
`⊕_x ℤ`", "Degree", and "`Pic⁰ X = ker deg` (as an abstract group)".
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

/-- A Weil divisor on a type of points `X` is a finite formal integer sum of points of `X`. -/
abbrev WeilDivisor (X : Type*) : Type _ :=
  X →₀ ℤ

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

/-- The coefficient of a point in a Weil divisor. -/
@[expose] def coeff (D : WeilDivisor X) (x : X) : ℤ :=
  D x

@[simp]
lemma coeff_zero (x : X) : coeff (0 : WeilDivisor X) x = 0 :=
  rfl

@[simp]
lemma coeff_add (D E : WeilDivisor X) (x : X) :
    coeff (D + E) x = coeff D x + coeff E x :=
  rfl

@[simp]
lemma coeff_neg (D : WeilDivisor X) (x : X) : coeff (-D) x = -coeff D x :=
  rfl

@[simp]
lemma coeff_sub (D E : WeilDivisor X) (x : X) :
    coeff (D - E) x = coeff D x - coeff E x :=
  rfl

@[ext]
lemma ext {D E : WeilDivisor X} (h : ∀ x, coeff D x = coeff E x) : D = E :=
  Finsupp.ext h

/-- A point lies in the support of a Weil divisor exactly when its coefficient is nonzero. This
is the `coeff`-level restatement of `Finsupp.mem_support_iff`. -/
@[grind =]
lemma mem_support_iff {D : WeilDivisor X} {x : X} : x ∈ D.support ↔ coeff D x ≠ 0 :=
  Finsupp.mem_support_iff

/-- The prime/point divisor supported at a single point with coefficient `1`. -/
noncomputable def ofPoint (x : X) : WeilDivisor X :=
  Finsupp.single x 1

@[simp]
lemma coeff_ofPoint_self (x : X) : coeff (ofPoint x) x = 1 :=
  Finsupp.single_eq_same

@[simp]
lemma coeff_ofPoint_of_ne {x y : X} (h : y ≠ x) : coeff (ofPoint x) y = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
lemma support_ofPoint (x : X) : (ofPoint x).support = {x} :=
  Finsupp.support_single x one_ne_zero

/-- The scaled point divisor `b • ofPoint a` is the single spike `Finsupp.single a b`. This is the
`ofPoint`/`Finsupp.single` bridge in its integer-scaled form, shared by the divisor files that
expand a divisor into its point contributions. -/
lemma single_eq_zsmul_ofPoint (a : X) (b : ℤ) :
    (Finsupp.single a b : WeilDivisor X) = b • ofPoint a :=
  (Finsupp.smul_single_one a b).symm

/-- A divisor is effective when every coefficient is nonnegative. -/
def IsEffective (D : WeilDivisor X) : Prop :=
  ∀ x, 0 ≤ coeff D x

lemma isEffective_iff (D : WeilDivisor X) : IsEffective D ↔ ∀ x, 0 ≤ coeff D x :=
  Iff.rfl

@[simp]
lemma isEffective_zero : IsEffective (0 : WeilDivisor X) := by
  intro x
  simp

lemma IsEffective.add {D E : WeilDivisor X} (hD : IsEffective D) (hE : IsEffective E) :
    IsEffective (D + E) := by
  intro x
  simpa [IsEffective] using add_nonneg (hD x) (hE x)

lemma IsEffective.nsmul {D : WeilDivisor X} (hD : IsEffective D) (n : ℕ) :
    IsEffective (n • D) := by
  intro x
  simpa [IsEffective, coeff] using nsmul_nonneg (hD x) n

/-- A nonzero effective divisor has some point with positive coefficient. -/
lemma IsEffective.exists_pos_coeff_of_ne_zero {D : WeilDivisor X} (hD : IsEffective D)
    (hD0 : D ≠ 0) : ∃ x, 0 < coeff D x := by
  classical
  by_contra h
  push Not at h
  apply hD0
  ext x
  exact le_antisymm (h x) (hD x)

@[simp]
lemma isEffective_ofPoint (x : X) : IsEffective (ofPoint x) := by
  intro y
  by_cases h : y = x
  · subst h
    norm_num [coeff_ofPoint_self]
  · rw [coeff_ofPoint_of_ne h]

/-- Effective Weil divisors form an additive submonoid of the group of all Weil divisors. -/
def effectiveSubmonoid (X : Type*) : AddSubmonoid (WeilDivisor X) where
  carrier := {D | IsEffective D}
  zero_mem' := isEffective_zero
  add_mem' := by
    intro D E hD hE
    exact IsEffective.add hD hE

@[simp]
lemma mem_effectiveSubmonoid (D : WeilDivisor X) :
    D ∈ effectiveSubmonoid X ↔ IsEffective D :=
  Iff.rfl

/-- Reindexing a Weil divisor along an equivalence preserves effectivity. -/
@[simp]
lemma isEffective_equivMapDomain_iff (e : X ≃ Y) (D : WeilDivisor X) :
    IsEffective (Finsupp.equivMapDomain e D) ↔ IsEffective D := by
  constructor
  · intro h x
    simpa only [coeff, Finsupp.equivMapDomain_apply,
      Equiv.symm_apply_apply] using h (e x)
  · intro h y
    simpa only [coeff, Finsupp.equivMapDomain_apply] using h (e.symm y)

/-- An equivalence of point types reindexes effective Weil divisors additively. -/
noncomputable def effectiveSubmonoidAddEquiv (e : X ≃ Y) :
    effectiveSubmonoid X ≃+ effectiveSubmonoid Y where
  toFun D :=
    ⟨Finsupp.domCongr e D, by
      simpa only [Finsupp.domCongr_apply, mem_effectiveSubmonoid] using
        (isEffective_equivMapDomain_iff e D).mpr D.property⟩
  invFun D :=
    ⟨Finsupp.domCongr e.symm D, by
      simpa only [Finsupp.domCongr_apply, mem_effectiveSubmonoid] using
        (isEffective_equivMapDomain_iff e.symm D).mpr D.property⟩
  left_inv D := Subtype.ext <| by
    simpa only [Finsupp.domCongr_symm] using
      (Finsupp.domCongr e).symm_apply_apply (D : WeilDivisor X)
  right_inv D := Subtype.ext <| by
    simpa only [Finsupp.domCongr_symm] using
      (Finsupp.domCongr e).apply_symm_apply (D : WeilDivisor Y)
  map_add' D E := Subtype.ext <| by
    simpa only [AddSubmonoid.coe_add] using
      (Finsupp.domCongr e).map_add (D : WeilDivisor X) E

/-- After forgetting effectivity, `effectiveSubmonoidAddEquiv` is ordinary reindexing. -/
@[simp]
lemma coe_effectiveSubmonoidAddEquiv (e : X ≃ Y) (D : effectiveSubmonoid X) :
    ((effectiveSubmonoidAddEquiv e D : effectiveSubmonoid Y) : WeilDivisor Y) =
      Finsupp.domCongr e D := by
  simp only [effectiveSubmonoidAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]

/-- After forgetting effectivity, the inverse of `effectiveSubmonoidAddEquiv` is inverse
reindexing. -/
@[simp]
lemma coe_effectiveSubmonoidAddEquiv_symm (e : X ≃ Y) (D : effectiveSubmonoid Y) :
    (((effectiveSubmonoidAddEquiv e).symm D : effectiveSubmonoid X) : WeilDivisor X) =
      (Finsupp.domCongr e).symm D := by
  apply (Finsupp.domCongr e).injective
  rw [← coe_effectiveSubmonoidAddEquiv e ((effectiveSubmonoidAddEquiv e).symm D),
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Push forward a formal divisor along a map of point sets by summing coefficients over
fibres.  Geometric pushforward of Weil divisors will specialize this once the relevant point
maps and residue-degree factors are available. -/
@[expose] noncomputable def pushforward (f : X → Y) : WeilDivisor X →+ WeilDivisor Y :=
  (Finsupp.lmapDomain ℤ ℤ f).toAddMonoidHom

/-- The explicit unfolding equation for formal pushforward: `pushforward f D` is `D.mapDomain f`.
Use this for manual rewriting rather than as a simp normal form. -/
lemma pushforward_apply (f : X → Y) (D : WeilDivisor X) :
    pushforward f D = D.mapDomain f :=
  rfl

/-- The coefficient of the pushed-forward divisor at `y` is the sum of the coefficients over
the fibre of `f` above `y`. -/
lemma coeff_pushforward [DecidableEq Y] (f : X → Y) (D : WeilDivisor X) (y : Y) :
    coeff (pushforward f D) y = ∑ x ∈ D.support with f x = y, coeff D x := by
  rcases em (y ∈ Set.range f) with ⟨x, rfl⟩ | hy
  · simp [coeff, pushforward_apply, Finsupp.mapDomain_apply_eq_sum]
  · rw [coeff, pushforward_apply, Finsupp.mapDomain_of_notMem_range]
    · refine (Finset.sum_eq_zero fun x hx => ?_).symm
      rw [Finset.mem_filter] at hx
      exact (hy ⟨x, hx.2⟩).elim
    · exact hy

lemma pushforward_zero (f : X → Y) : pushforward f (0 : WeilDivisor X) = 0 :=
  map_zero (pushforward f)

@[simp]
lemma pushforward_add (f : X → Y) (D E : WeilDivisor X) :
    pushforward f (D + E) = pushforward f D + pushforward f E :=
  map_add (pushforward f) D E

@[simp]
lemma pushforward_ofPoint (f : X → Y) (x : X) :
    pushforward f (ofPoint x) = ofPoint (f x) := by
  simp [pushforward, ofPoint, Finsupp.mapDomain_single]

@[simp]
lemma pushforward_id : pushforward (fun x : X => x) = AddMonoidHom.id (WeilDivisor X) := by
  ext D x
  simp [pushforward, coeff]

lemma pushforward_comp (g : Y → Z) (f : X → Y) :
    pushforward (g ∘ f) = (pushforward g).comp (pushforward f) := by
  ext D z
  simp [pushforward, Function.comp_def]

lemma IsEffective.pushforward {D : WeilDivisor X} (hD : IsEffective D) (f : X → Y) :
    IsEffective (pushforward f D) := by
  classical
  intro y
  rw [coeff_pushforward]
  exact Finset.sum_nonneg fun x _ => hD x

lemma pushforward_mem_effectiveSubmonoid {D : WeilDivisor X} (hD : D ∈ effectiveSubmonoid X)
    (f : X → Y) : pushforward f D ∈ effectiveSubmonoid Y :=
  hD.pushforward f

/-- The unweighted degree of a Weil divisor, summing its coefficients.  On a curve over a
non-algebraically-closed field, use `weightedDegree` with residue-field degrees instead. -/
@[expose] noncomputable def degree : WeilDivisor X →+ ℤ :=
  Finsupp.degree

lemma degree_apply (D : WeilDivisor X) : degree D = ∑ x ∈ D.support, D x :=
  rfl

@[simp]
lemma degree_zero : degree (0 : WeilDivisor X) = 0 :=
  map_zero degree

@[simp]
lemma degree_add (D E : WeilDivisor X) : degree (D + E) = degree D + degree E :=
  map_add degree D E

@[simp]
lemma degree_neg (D : WeilDivisor X) : degree (-D) = -degree D :=
  map_neg degree D

@[simp]
lemma degree_sub (D E : WeilDivisor X) : degree (D - E) = degree D - degree E :=
  map_sub degree D E

@[simp]
lemma degree_ofPoint (x : X) : degree (ofPoint x) = 1 := by
  simp [degree, ofPoint, Finsupp.degree_single]

@[simp]
lemma degree_pushforward (f : X → Y) (D : WeilDivisor X) :
    degree (pushforward f D) = degree D := by
  simp [degree, pushforward, Finsupp.degree_mapDomain]

/-- On a nonempty point type the unweighted degree map is surjective: a single point has degree
`1`, so its integer multiples realise every degree. -/
lemma degree_surjective [Nonempty X] : Function.Surjective (degree : WeilDivisor X →+ ℤ) := by
  intro n
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨n • ofPoint x, by simp [map_zsmul, degree_ofPoint]⟩

/-- On a nonempty point type the unweighted degree map hits all of `ℤ`. -/
lemma degree_range_eq_top [Nonempty X] : (degree : WeilDivisor X →+ ℤ).range = ⊤ :=
  AddMonoidHom.range_eq_top.mpr degree_surjective

/-- The weighted degree of a Weil divisor against an integer-valued weight on points.

For a curve over `k`, the intended weight is `x ↦ [κ(x) : k]`. -/
noncomputable def weightedDegree (w : X → ℤ) : WeilDivisor X →+ ℤ :=
  (Finsupp.linearCombination ℤ w).toAddMonoidHom

lemma weightedDegree_apply (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w D = D.sum fun x n => n * w x := by
  simp [weightedDegree, Finsupp.linearCombination_apply]

@[simp]
lemma weightedDegree_zero (w : X → ℤ) : weightedDegree w (0 : WeilDivisor X) = 0 :=
  map_zero (weightedDegree w)

@[simp]
lemma weightedDegree_add (w : X → ℤ) (D E : WeilDivisor X) :
    weightedDegree w (D + E) = weightedDegree w D + weightedDegree w E :=
  map_add (weightedDegree w) D E

@[simp]
lemma weightedDegree_neg (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w (-D) = -weightedDegree w D :=
  map_neg (weightedDegree w) D

@[simp]
lemma weightedDegree_sub (w : X → ℤ) (D E : WeilDivisor X) :
    weightedDegree w (D - E) = weightedDegree w D - weightedDegree w E :=
  map_sub (weightedDegree w) D E

@[simp]
lemma weightedDegree_ofPoint (w : X → ℤ) (x : X) :
    weightedDegree w (ofPoint x) = w x := by
  simp [weightedDegree, ofPoint, Finsupp.linearCombination_single]

lemma weightedDegree_pushforward (wY : Y → ℤ) (f : X → Y) (D : WeilDivisor X) :
    weightedDegree wY (pushforward f D) = weightedDegree (wY ∘ f) D := by
  simp [weightedDegree, pushforward, Finsupp.linearCombination_mapDomain]

/-- The image of the weighted degree homomorphism is the subgroup of `ℤ` generated by the
weights. The point divisors generate the free abelian group of Weil divisors and
`weightedDegree w (ofPoint x) = w x`, so the image is `AddSubgroup.closure (Set.range w)`; being
a subgroup of `ℤ`, it is `d·ℤ` for a unique `d ≥ 0`, the index of the weights. -/
lemma weightedDegree_range (w : X → ℤ) :
    (weightedDegree w : WeilDivisor X →+ ℤ).range = AddSubgroup.closure (Set.range w) := by
  -- `weightedDegree` is the additive-monoid-hom wrapper around the linear-combination map, so
  -- its range is definitionally the additive subgroup underlying the linear map range.
  change (Finsupp.linearCombination ℤ w).range.toAddSubgroup =
    AddSubgroup.closure (Set.range w)
  rw [Finsupp.range_linearCombination, Submodule.span_int_eq_addSubgroupClosure]

/-- An effective divisor has nonnegative weighted degree when all weights are nonnegative. -/
lemma IsEffective.weightedDegree_nonneg {w : X → ℤ} (hw : ∀ x, 0 ≤ w x)
    {D : WeilDivisor X} (hD : IsEffective D) : 0 ≤ weightedDegree w D := by
  rw [weightedDegree_apply]
  exact Finsupp.sum_nonneg fun x _ => mul_nonneg (hD x) (hw x)

/-- With strictly positive weights on the support, an effective divisor has weighted degree
zero iff it is zero. -/
lemma IsEffective.weightedDegree_eq_zero_iff_of_pos_on_support {w : X → ℤ}
    {D : WeilDivisor X} (hD : IsEffective D) (hw : ∀ x ∈ D.support, 0 < w x) :
    weightedDegree w D = 0 ↔ D = 0 := by
  constructor
  · intro hdeg
    by_contra hD0
    obtain ⟨x, hxpos⟩ := hD.exists_pos_coeff_of_ne_zero hD0
    have hxs : x ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt hxpos)
    have hsum_pos : 0 < D.sum fun y n => n * w y := by
      exact Finsupp.sum_pos'
        (fun y hy => mul_nonneg ((isEffective_iff D).mp hD y) (le_of_lt (hw y hy)))
        ⟨x, hxs, mul_pos hxpos (hw x hxs)⟩
    rw [← weightedDegree_apply] at hsum_pos
    exact (ne_of_gt hsum_pos) hdeg
  · intro h
    simp [h]

/-- With strictly positive weights on the support, an effective divisor of weighted degree zero
is zero. -/
lemma IsEffective.eq_zero_of_weightedDegree_eq_zero_of_pos_on_support {w : X → ℤ}
    {D : WeilDivisor X} (hD : IsEffective D) (hw : ∀ x ∈ D.support, 0 < w x)
    (hdeg : weightedDegree w D = 0) : D = 0 :=
  (hD.weightedDegree_eq_zero_iff_of_pos_on_support hw).mp hdeg

/-- With strictly positive weights, an effective divisor has weighted degree zero iff it is
zero. -/
lemma IsEffective.weightedDegree_eq_zero_iff_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D : WeilDivisor X} (hD : IsEffective D) :
    weightedDegree w D = 0 ↔ D = 0 :=
  hD.weightedDegree_eq_zero_iff_of_pos_on_support fun x _ => hw x

/-- With strictly positive weights, an effective divisor of weighted degree zero is zero. -/
lemma IsEffective.eq_zero_of_weightedDegree_eq_zero_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D : WeilDivisor X} (hD : IsEffective D) (hdeg : weightedDegree w D = 0) : D = 0 :=
  hD.eq_zero_of_weightedDegree_eq_zero_of_pos_on_support (fun x _ => hw x) hdeg

/-- With strictly positive weights, a nonzero effective divisor has positive weighted degree. -/
lemma IsEffective.weightedDegree_pos_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D : WeilDivisor X} (hD : IsEffective D) (hD0 : D ≠ 0) :
    0 < weightedDegree w D := by
  exact lt_of_le_of_ne (hD.weightedDegree_nonneg fun x => le_of_lt (hw x)) fun h =>
    hD0 ((hD.weightedDegree_eq_zero_iff_of_pos hw).mp h.symm)

@[simp]
lemma weightedDegree_one_eq_degree (D : WeilDivisor X) :
    weightedDegree (fun _ : X => (1 : ℤ)) D = degree D := by
  rw [weightedDegree_apply, degree_apply]
  simp [Finsupp.sum]

/-- An effective divisor has nonnegative degree. -/
lemma IsEffective.degree_nonneg {D : WeilDivisor X} (hD : IsEffective D) :
    0 ≤ degree D := by
  simpa [weightedDegree_one_eq_degree D] using
    hD.weightedDegree_nonneg (w := fun _ : X => (1 : ℤ)) fun _ => zero_le_one

/-- An effective divisor has degree zero iff it is zero. -/
lemma IsEffective.degree_eq_zero_iff {D : WeilDivisor X} (hD : IsEffective D) :
    degree D = 0 ↔ D = 0 := by
  simpa [weightedDegree_one_eq_degree D] using
    hD.weightedDegree_eq_zero_iff_of_pos (w := fun _ : X => (1 : ℤ)) fun _ => zero_lt_one

/-- An effective divisor of degree zero is zero. -/
lemma IsEffective.eq_zero_of_degree_eq_zero {D : WeilDivisor X} (hD : IsEffective D)
    (hdeg : degree D = 0) : D = 0 :=
  (hD.degree_eq_zero_iff).mp hdeg

/-- A nonzero effective divisor has positive degree. -/
lemma IsEffective.degree_pos {D : WeilDivisor X} (hD : IsEffective D) (hD0 : D ≠ 0) :
    0 < degree D := by
  simpa [weightedDegree_one_eq_degree D] using
    hD.weightedDegree_pos_of_pos (w := fun _ : X => (1 : ℤ)) (fun _ => zero_lt_one) hD0

/-- The subgroup of divisors of unweighted degree zero.

For a smooth proper curve over an algebraically closed field this is the formal divisor group
whose quotient by principal divisors gives the abstract degree-zero Picard group. Over a
general field, use `weightedDegreeZeroSubgroup` with residue-field degrees as weights. -/
@[expose] noncomputable def degreeZeroSubgroup (X : Type*) : AddSubgroup (WeilDivisor X) :=
  (degree : WeilDivisor X →+ ℤ).ker

@[simp]
lemma mem_degreeZeroSubgroup (D : WeilDivisor X) :
    D ∈ degreeZeroSubgroup X ↔ degree D = 0 :=
  AddMonoidHom.mem_ker

@[simp]
lemma degree_coe_degreeZeroSubgroup (D : degreeZeroSubgroup X) :
    degree (D : WeilDivisor X) = 0 :=
  D.property

/-- An effective divisor lying in the unweighted degree-zero subgroup is zero. -/
lemma coe_degreeZeroSubgroup_eq_zero_of_isEffective {D : degreeZeroSubgroup X}
    (hD : IsEffective (D : WeilDivisor X)) : (D : WeilDivisor X) = 0 :=
  hD.eq_zero_of_degree_eq_zero (degree_coe_degreeZeroSubgroup D)

/-- The formal divisor `[x] - [y]`, a basic source of degree-zero divisors. -/
@[expose] noncomputable def pointDifference (x y : X) : WeilDivisor X :=
  ofPoint x - ofPoint y

@[simp]
lemma pointDifference_self (x : X) : pointDifference x x = 0 := by
  simp [pointDifference]

/-- Point differences telescope additively: `[x] - [y] + ([y] - [z]) = [x] - [z]`. -/
@[simp]
lemma pointDifference_add_pointDifference_cancel (x y z : X) :
    pointDifference x y + pointDifference y z = pointDifference x z := by
  simp [pointDifference, sub_eq_add_neg, add_assoc, add_left_comm]

/-- Reversing a point difference negates it. -/
lemma pointDifference_swap (x y : X) : pointDifference y x = -pointDifference x y := by
  simp [pointDifference, sub_eq_add_neg, add_comm]

@[simp]
lemma coeff_pointDifference_left (x y : X) :
    coeff (pointDifference x y) x = 1 - coeff (ofPoint y) x := by
  simp [pointDifference]

@[simp]
lemma coeff_pointDifference_right (x y : X) :
    coeff (pointDifference x y) y = coeff (ofPoint x) y - 1 := by
  simp [pointDifference]

@[simp]
lemma coeff_pointDifference [DecidableEq X] (x y z : X) :
    coeff (pointDifference x y) z =
      (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
  by_cases hx : z = x
  · by_cases hy : z = y
    · subst hx
      subst hy
      simp [pointDifference, ofPoint, coeff]
    · subst hx
      simp [pointDifference, ofPoint, coeff, hy]
  · by_cases hy : z = y
    · subst hy
      simp [pointDifference, ofPoint, coeff, hx]
    · simp [pointDifference, ofPoint, coeff, hx, hy]

lemma support_pointDifference_subset [DecidableEq X] (x y : X) :
    (pointDifference x y).support ⊆ {x, y} := by
  intro z hz
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra hzy
  push Not at hzy
  have hx : z ≠ x := hzy.1
  have hy : z ≠ y := hzy.2
  exact (Finsupp.mem_support_iff.mp hz)
    (by simp [pointDifference, ofPoint, Finsupp.single_eq_of_ne hx, Finsupp.single_eq_of_ne hy])

@[simp]
lemma degree_pointDifference (x y : X) : degree (pointDifference x y) = 0 := by
  simp [pointDifference]

@[simp]
lemma weightedDegree_pointDifference (w : X → ℤ) (x y : X) :
    weightedDegree w (pointDifference x y) = w x - w y := by
  simp [pointDifference]

lemma pointDifference_mem_degreeZeroSubgroup (x y : X) :
    pointDifference x y ∈ degreeZeroSubgroup X := by
  simp

@[simp]
lemma pushforward_pointDifference (f : X → Y) (x y : X) :
    pushforward f (pointDifference x y) = pointDifference (f x) (f y) := by
  rw [pointDifference, map_sub, pushforward_ofPoint, pushforward_ofPoint]
  rfl

/-- Pushforward as a homomorphism on unweighted degree-zero divisors. -/
@[expose] noncomputable def pushforwardDegreeZero (f : X → Y) :
    degreeZeroSubgroup X →+ degreeZeroSubgroup Y where
  toFun D :=
    ⟨pushforward f D, by
      rw [mem_degreeZeroSubgroup, degree_pushforward, degree_coe_degreeZeroSubgroup]⟩
  map_zero' := by
    apply Subtype.ext
    exact pushforward_zero f
  map_add' D E := by
    apply Subtype.ext
    exact pushforward_add f D E

@[simp]
lemma pushforwardDegreeZero_apply (f : X → Y) (D : degreeZeroSubgroup X) :
    (pushforwardDegreeZero f D : WeilDivisor Y) = pushforward f D :=
  rfl

@[simp]
lemma pushforwardDegreeZero_id :
    pushforwardDegreeZero (fun x : X => x) = AddMonoidHom.id (degreeZeroSubgroup X) := by
  ext D x
  simp

lemma pushforwardDegreeZero_comp (g : Y → Z) (f : X → Y) :
    pushforwardDegreeZero (g ∘ f) =
      (pushforwardDegreeZero g).comp (pushforwardDegreeZero f) := by
  ext D z
  simp [pushforward_comp]

/-- The subgroup of divisors of weighted degree zero for a weight function on points.

For a curve over a field `k`, the intended weight is `x ↦ [κ(x) : k]`, giving the formal
degree-zero divisor group before principal divisors are introduced. -/
@[expose] noncomputable def weightedDegreeZeroSubgroup (w : X → ℤ) : AddSubgroup (WeilDivisor X) :=
  (weightedDegree w).ker

@[simp]
lemma mem_weightedDegreeZeroSubgroup (w : X → ℤ) (D : WeilDivisor X) :
    D ∈ weightedDegreeZeroSubgroup w ↔ weightedDegree w D = 0 :=
  AddMonoidHom.mem_ker

@[simp]
lemma weightedDegree_coe_weightedDegreeZeroSubgroup (w : X → ℤ)
    (D : weightedDegreeZeroSubgroup w) : weightedDegree w (D : WeilDivisor X) = 0 :=
  D.property

/-- The degree-corrected representative of a divisor in the weighted degree-zero divisor group.

For a weight-one base point `x₀`, this is `D - weightedDegree(D) • [x₀]`, viewed as a
weighted-degree-zero divisor. -/
noncomputable def weightedAbelJacobiDegreeZeroDivisor (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) : weightedDegreeZeroSubgroup w :=
  ⟨D - weightedDegree w D • ofPoint x₀, by
    rw [mem_weightedDegreeZeroSubgroup, map_sub, map_zsmul, weightedDegree_ofPoint, hx₀]
    simp⟩

-- The degree-corrected representatives are intentionally not `@[expose]`, so downstream modules
-- cannot unfold them; each defining equality is unfolded once here in a `private` lemma and
-- re-exported through the public characterization lemma below.
private lemma coe_weightedAbelJacobiDegreeZeroDivisor_def (w : X → ℤ) {x₀ : X}
    (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (weightedAbelJacobiDegreeZeroDivisor w hx₀ D : WeilDivisor X) =
      D - weightedDegree w D • ofPoint x₀ :=
  rfl

@[simp]
lemma coe_weightedAbelJacobiDegreeZeroDivisor (w : X → ℤ) {x₀ : X}
    (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (weightedAbelJacobiDegreeZeroDivisor w hx₀ D : WeilDivisor X) =
      D - weightedDegree w D • ofPoint x₀ :=
  coe_weightedAbelJacobiDegreeZeroDivisor_def w hx₀ D

/-- For strictly positive weights, an effective divisor lying in the weighted degree-zero
subgroup is zero. -/
lemma coe_weightedDegreeZeroSubgroup_eq_zero_of_isEffective {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D : weightedDegreeZeroSubgroup w} (hD : IsEffective (D : WeilDivisor X)) :
    (D : WeilDivisor X) = 0 :=
  hD.eq_zero_of_weightedDegree_eq_zero_of_pos hw
    (weightedDegree_coe_weightedDegreeZeroSubgroup w D)

lemma pointDifference_mem_weightedDegreeZeroSubgroup {w : X → ℤ} {x y : X}
    (h : w x = w y) : pointDifference x y ∈ weightedDegreeZeroSubgroup w := by
  simp [h]

/-! ### Degree-corrected point divisors -/

/-- The divisor `[x] - w(x)[x₀]`.

For the geometric weight `w x = [κ(x) : k]` and a rational base point `x₀` with `w x₀ = 1`,
this is the degree-zero divisor underlying the Abel-Jacobi class of the closed point `x`.
In the algebraically closed/unweighted specialization, this recovers `pointDifference x x₀`. -/
noncomputable def weightedPointBaseDifference (w : X → ℤ) (x₀ x : X) : WeilDivisor X :=
  ofPoint x - w x • ofPoint x₀

private lemma weightedPointBaseDifference_def (w : X → ℤ) (x₀ x : X) :
    weightedPointBaseDifference w x₀ x = ofPoint x - w x • ofPoint x₀ :=
  rfl

/-- The degree-corrected point divisor is `[x]` minus `w x` copies of the base point `[x₀]`.
This exposes the definition as a public equation for use across modules. -/
lemma weightedPointBaseDifference_eq_ofPoint_sub_zsmul (w : X → ℤ) (x₀ x : X) :
    weightedPointBaseDifference w x₀ x = ofPoint x - w x • ofPoint x₀ :=
  weightedPointBaseDifference_def w x₀ x

/-- At the constant weight `1`, the degree-corrected point divisor is the usual point
difference. This lets unweighted API reuse the weighted construction. -/
lemma weightedPointBaseDifference_eq_pointDifference (x₀ x : X) :
    weightedPointBaseDifference (fun _ : X => (1 : ℤ)) x₀ x = pointDifference x x₀ := by
  simp [weightedPointBaseDifference, pointDifference]

/-- If the point has weight `1`, the degree-corrected point divisor is the usual point
difference. -/
@[simp]
lemma weightedPointBaseDifference_eq_pointDifference_of_weight_eq_one {w : X → ℤ} {x₀ x : X}
    (hx : w x = 1) : weightedPointBaseDifference w x₀ x = pointDifference x x₀ := by
  simp [weightedPointBaseDifference, pointDifference, hx]

/-- Coefficients of the degree-corrected point divisor, used as the pointwise simp form of
`weightedPointBaseDifference`. -/
@[simp]
lemma coeff_weightedPointBaseDifference [DecidableEq X] (w : X → ℤ) (x₀ x y : X) :
    coeff (weightedPointBaseDifference w x₀ x) y =
      (if y = x then 1 else 0) - if y = x₀ then w x else 0 := by
  by_cases hyx : y = x
  · subst y
    by_cases hx₀ : x = x₀ <;> simp [weightedPointBaseDifference, ofPoint, coeff, hx₀]
  · by_cases hy₀ : y = x₀
    · subst y
      have hx₀ : x₀ ≠ x := by simpa using hyx
      simp [weightedPointBaseDifference, ofPoint, coeff, hx₀]
    · simp [weightedPointBaseDifference, ofPoint, coeff, hyx, hy₀]

/-- The support of `[x] - w(x)[x₀]` is contained in `{x, x₀}`. -/
lemma support_weightedPointBaseDifference_subset [DecidableEq X] (w : X → ℤ) (x₀ x : X) :
    (weightedPointBaseDifference w x₀ x).support ⊆ {x, x₀} := by
  intro y hy
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra hyx
  push Not at hyx
  exact Finsupp.mem_support_iff.mp hy (by
    simp [weightedPointBaseDifference, ofPoint, hyx.1, hyx.2])

/-- If the base point has weight `1`, the divisor `[x₀] - w(x₀)[x₀]` is zero. -/
lemma weightedPointBaseDifference_self {w : X → ℤ} {x₀ : X} (hx₀ : w x₀ = 1) :
    weightedPointBaseDifference w x₀ x₀ = 0 := by
  simp [weightedPointBaseDifference, hx₀]

/-- The weighted degree of `[x] - w(x)[x₀]` is `w(x) * (1 - w(x₀))`. -/
@[simp]
lemma weightedDegree_weightedPointBaseDifference (w : X → ℤ) (x₀ x : X) :
    weightedDegree w (weightedPointBaseDifference w x₀ x) = w x * (1 - w x₀) := by
  simp [weightedPointBaseDifference]
  ring

/-- If the base point has weight `1`, then `[x] - w(x)[x₀]` has weighted degree zero. -/
lemma weightedPointBaseDifference_mem_weightedDegreeZeroSubgroup {w : X → ℤ} {x₀ : X}
    (hx₀ : w x₀ = 1) (x : X) :
    weightedPointBaseDifference w x₀ x ∈ weightedDegreeZeroSubgroup w := by
  simp [hx₀]

/-- Changing the base point in the weighted point-base divisor translates it by
`w(x) • ([x₀] - [y₀])`. -/
lemma weightedPointBaseDifference_change_base (w : X → ℤ) (x₀ y₀ x : X) :
    weightedPointBaseDifference w y₀ x =
      weightedPointBaseDifference w x₀ x + w x • pointDifference x₀ y₀ := by
  simp [weightedPointBaseDifference, pointDifference, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

/-- The difference between the weighted point-base divisors for two base points is
`w(x) • ([x₀] - [y₀])`. -/
lemma weightedPointBaseDifference_sub_change_base (w : X → ℤ) (x₀ y₀ x : X) :
    weightedPointBaseDifference w y₀ x - weightedPointBaseDifference w x₀ x =
      w x • pointDifference x₀ y₀ := by
  rw [weightedPointBaseDifference_change_base, add_sub_cancel_left]

/-- Subtracting two degree-corrected point divisors with the same base point cancels the base
term when the two points have equal weight. -/
lemma weightedPointBaseDifference_sub_same_base (w : X → ℤ) {x₀ x y : X} (hxy : w x = w y) :
    weightedPointBaseDifference w x₀ x - weightedPointBaseDifference w x₀ y =
      pointDifference x y := by
  simp [weightedPointBaseDifference, pointDifference, hxy, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

/-- Pushforward as a homomorphism on weighted degree-zero divisors, when the target weight
pulls back to the source weight. -/
@[expose] noncomputable def pushforwardWeightedDegreeZero (wX : X → ℤ) (wY : Y → ℤ) (f : X → Y)
    (hw : ∀ x, wY (f x) = wX x) :
    weightedDegreeZeroSubgroup wX →+ weightedDegreeZeroSubgroup wY where
  toFun D :=
    ⟨pushforward f D, by
      rw [mem_weightedDegreeZeroSubgroup, weightedDegree_pushforward]
      simp [Function.comp_def, hw]⟩
  map_zero' := by
    apply Subtype.ext
    exact pushforward_zero f
  map_add' D E := by
    apply Subtype.ext
    exact pushforward_add f D E

@[simp]
lemma pushforwardWeightedDegreeZero_apply (wX : X → ℤ) (wY : Y → ℤ) (f : X → Y)
    (hw : ∀ x, wY (f x) = wX x) (D : weightedDegreeZeroSubgroup wX) :
    (pushforwardWeightedDegreeZero wX wY f hw D : WeilDivisor Y) = pushforward f D :=
  rfl

@[simp]
lemma pushforwardWeightedDegreeZero_id (w : X → ℤ) :
    pushforwardWeightedDegreeZero w w (fun x : X => x) (fun _ => rfl) =
      AddMonoidHom.id (weightedDegreeZeroSubgroup w) := by
  ext D x
  simp

lemma pushforwardWeightedDegreeZero_comp (wX : X → ℤ) (wY : Y → ℤ) (wZ : Z → ℤ)
    (f : X → Y) (g : Y → Z) (hf : ∀ x, wY (f x) = wX x)
    (hg : ∀ y, wZ (g y) = wY y) :
    pushforwardWeightedDegreeZero wX wZ (g ∘ f) (fun x => by simp [hg (f x), hf x]) =
      (pushforwardWeightedDegreeZero wY wZ g hg).comp
        (pushforwardWeightedDegreeZero wX wY f hf) := by
  ext D z
  simp [pushforward_comp]

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
