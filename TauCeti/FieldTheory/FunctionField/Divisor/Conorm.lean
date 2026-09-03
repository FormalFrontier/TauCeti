/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.GeometricDegree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# The conorm of a divisor along an extension of function fields

Let `F' / k'` be a finite extension of the algebraic function field `F / k`.  Every place `P'` of
`F' / k'` restricts to a place `P'.restrict k F` of `F / k`, and a place of `F / k` has only
finitely many places above it.  The **conorm**

`Con(P) = ∑_{P' ∣ P} e(P' ∣ P) · P'`

therefore extends by additivity to a homomorphism `Con : Divisor k F →+ Divisor k' F'` of divisor
groups.  Equivalently — and this is the definition used here, because it makes the coefficient
formula definitional — the coefficient of `Con D` at `P'` is `e(P' ∣ P) · D(P)` for the place
`P = P'.restrict k F` below `P'`.

The conorm carries the divisor of a function `z` to the divisor of its image in `F'`, because on
`F` the order function at `P'` is `e(P' ∣ P)` times the order function at `P`.  Hence it descends
to a homomorphism of divisor class groups.

The degree identity `[k' : k] · deg (Con D) = [F' : F] · deg D` is proved here from the
fundamental identity `∑_{P' ∣ P} e(P' ∣ P) f(P' ∣ P) = [F' : F]`, so it carries that identity's
separability hypothesis on `F' / F`.  It is stated cross-multiplied, since the divisibility
`[k' : k] ∣ [F' : F]` that turns it into `deg (Con D) = n(F'/F) · deg D` needs `F` and `k'` to be
linearly disjoint over `k`; under that hypothesis the divided form is `degree_conorm`, with
`n(F'/F)` the geometric degree of the extension.

## Main definitions

* `TauCeti.Divisor.conorm`: the conorm homomorphism `Con : Divisor k F →+ Divisor k' F'`
  (Stichtenoth, Definition 3.1.8).
* `TauCeti.Divisor.conormClassGroup`: the induced homomorphism `Cl(F) →+ Cl(F')` of divisor class
  groups (Stichtenoth, Proposition 3.1.9).

## Main results

* `TauCeti.Divisor.coeff_conorm`: the defining coefficient formula.
* `TauCeti.Divisor.conorm_ofPoint`: the conorm of a place is `∑_{P' ∣ P} e(P' ∣ P) · P'`, the form
  in which Stichtenoth defines it.
* `TauCeti.Divisor.conorm_conorm`: the conorm is transitive in a tower of extensions
  (Stichtenoth, Definition 3.1.8).
* `TauCeti.Divisor.conorm_principal`: the conorm of `div z` is the divisor of the image of `z`
  (Stichtenoth, Proposition 3.1.9).
* `TauCeti.Divisor.conorm_injective`: the conorm is injective.
* `TauCeti.Divisor.finrank_mul_degree_conorm`: **the degree of a conorm**,
  `[k' : k] · deg (Con D) = [F' : F] · deg D` (Stichtenoth, Corollary 3.1.14).
* `TauCeti.Divisor.degree_conorm`: the same identity divided through by `[k' : k]`, for `F` and
  `k'` linearly disjoint over `k`: `deg (Con D) = n(F'/F) · deg D` (Stichtenoth,
  Corollary 3.6.4, here under the separability hypothesis on `F' / F` that the cross-multiplied
  form already carries).

## Implementation notes

The upper field `F' / k'` is an explicit argument of `conorm`, and the lower field `F / k` is
implicit, because a divisor of `F / k` determines the latter but not the former.  This is the
opposite convention to `TauCeti.Place.restrict`, and for the same reason: there the argument
determines the upper field and the lower one has to be supplied.

The conorm is built from its coefficients through `Finsupp.ofSupportFinite` rather than as the
formal sum `∑_P D(P) · Con(P)`.  The coefficient formula is then definitional and additivity is
immediate, whereas the sum form needs the fibres to be disjoint before either can be read off;
`TauCeti.Divisor.conorm_ofPoint` recovers the sum form at a single place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1 and III.6.  The conorm and its cross-multiplied degree identity are III.1
  (Definition 3.1.8, Proposition 3.1.9, Corollary 3.1.14); the quotient-valued degree identity
  `deg (Con A) = [F' : F·k'] · deg A` is Corollary 3.6.4.
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

section Extension

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

variable (k' F')

/-- The candidate coefficient family of the conorm is finitely supported: a place contributing to
it lies over a place in the support of `D`, and each of those has only finitely many places above
it. -/
private theorem finite_support_conormCoeff (D : Divisor k F) :
    (Function.support fun P' : Place k' F' ↦
      (Place.ramificationIdx F P' : ℤ) * D.coeff (P'.restrict k F)).Finite := by
  refine Set.Finite.subset (D.support.finite_toSet.biUnion
    fun P _ ↦ Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P) fun P' hP' ↦ ?_
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP'
  exact Set.mem_biUnion (Finset.mem_coe.mpr (WeilDivisor.mem_support_iff.mpr hP'.2)) rfl

/-- **The conorm of a divisor** along a finite extension `F' / k'` of `F / k` (Stichtenoth,
Definition 3.1.8): the divisor of `F' / k'` whose coefficient at a place `P'` is `e(P' ∣ P)` times
the coefficient of `D` at the place `P` that `P'` lies over.  On a single place it is the formal
sum `∑_{P' ∣ P} e(P' ∣ P) · P'`; see `TauCeti.Divisor.conorm_ofPoint`. -/
noncomputable def conorm : Divisor k F →+ Divisor k' F' where
  toFun D := Finsupp.ofSupportFinite
    (fun P' : Place k' F' ↦ (Place.ramificationIdx F P' : ℤ) * D.coeff (P'.restrict k F))
    (finite_support_conormCoeff k' F' D)
  map_zero' := by
    refine Finsupp.ext fun P' ↦ ?_
    rw [Finsupp.ofSupportFinite_coe]
    simp
  map_add' D E := by
    refine Finsupp.ext fun P' ↦ ?_
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_coe]
    simp [mul_add]

/-- **The defining coefficient formula of the conorm**: the coefficient of `Con D` at a place `P'`
of `F' / k'` is `e(P' ∣ P)` times the coefficient of `D` at the place `P` below it. -/
@[simp]
theorem coeff_conorm (D : Divisor k F) (P' : Place k' F') :
    (conorm k' F' D).coeff P' = Place.ramificationIdx F P' * D.coeff (P'.restrict k F) := (rfl)

/-- A place of `F' / k'` lies in the support of `Con D` exactly when the place below it lies in
the support of `D`: the ramification indices are positive, so nothing cancels. -/
theorem mem_support_conorm_iff {D : Divisor k F} {P' : Place k' F'} :
    P' ∈ (conorm k' F' D).support ↔ P'.restrict k F ∈ D.support := by
  have he : Place.ramificationIdx F P' ≠ 0 := (Place.ramificationIdx_pos F P').ne'
  rw [WeilDivisor.mem_support_iff, WeilDivisor.mem_support_iff, coeff_conorm, ne_eq,
    mul_eq_zero, not_or]
  simp [he]

/-- **The conorm of a place** (Stichtenoth, Definition 3.1.8): `Con P = ∑_{P' ∣ P} e(P' ∣ P) · P'`,
the divisor supported on the finitely many places of `F' / k'` lying over `P` with the
ramification indices as multiplicities.  Its expansion as a sum of point divisors is
`TauCeti.AlgebraicGeometry.WeilDivisor.ofFinsetWithMultiplicity_eq_sum`. -/
theorem conorm_ofPoint (P : Place k F) :
    conorm k' F' (WeilDivisor.ofPoint P) =
      WeilDivisor.ofFinsetWithMultiplicity
        (Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
        (Place.ramificationIdx F) := by
  classical
  refine WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_conorm, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  rcases eq_or_ne (Q.restrict k F) P with h | h
  · simp [h]
  · simp [h, WeilDivisor.coeff_ofPoint_of_ne h]

/-- The conorm is monotone: it multiplies coefficients by positive ramification indices. -/
theorem conorm_mono : Monotone (conorm k' F' : Divisor k F → Divisor k' F') := by
  intro D E h
  refine WeilDivisor.le_iff.mpr fun P' ↦ ?_
  rw [coeff_conorm, coeff_conorm]
  exact mul_le_mul_of_nonneg_left (WeilDivisor.coeff_le_coeff h _) (by positivity)

/-- The conorm of an effective divisor is effective. -/
theorem isEffective_conorm {D : Divisor k F} (hD : D.IsEffective) :
    (conorm k' F' D).IsEffective :=
  WeilDivisor.isEffective_iff_zero_le.mpr <| by
    simpa using conorm_mono k' F' (WeilDivisor.isEffective_iff_zero_le.mp hD)

/-- **The conorm is injective**: every place of `F / k` is the restriction of a place of `F' / k'`,
and the ramification indices are nonzero. -/
theorem conorm_injective [Algebra.IsIntegral k k'] (hF' : IsFunctionField k' F') :
    Function.Injective (conorm k' F' : Divisor k F → Divisor k' F') := by
  intro D E h
  refine WeilDivisor.ext fun P ↦ ?_
  obtain ⟨P', rfl⟩ := Place.restrict_surjective (k := k) (F := F) hF' P
  have hP' := congrArg (fun C ↦ C.coeff P') h
  simp only [coeff_conorm] at hP'
  have he : (Place.ramificationIdx F P' : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Place.ramificationIdx_pos F P').ne'
  exact mul_left_cancel₀ he hP'

/-! ### The degree of a conorm -/

section Degree

variable [Algebra.IsIntegral k k'] [Algebra.IsSeparable F F']

/-- The degree of the conorm of a place: `[k' : k] · deg (Con P) = [F' : F] · deg P`.  The
fundamental identity sums the products `e(P' ∣ P) · f(P' ∣ P)` over the fibre, and
`TauCeti.Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict` turns each residue degree
`f(P' ∣ P)` into the ratio of the degrees of `P'` and `P`.  This is the case from which the
general identity follows by additivity. -/
private theorem finrank_mul_degree_conorm_ofPoint (P : Place k F) :
    (Module.finrank k k' : ℤ) * degree (conorm k' F' (WeilDivisor.ofPoint P)) =
      (Module.finrank F F' : ℤ) * P.degree := by
  classical
  set s := (Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset with hsdef
  have hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P := fun _ ↦ Set.Finite.mem_toFinset _
  have hdeg : degree (conorm k' F' (WeilDivisor.ofPoint P)) =
      ∑ P' ∈ s, (Place.ramificationIdx F P' : ℤ) * P'.degree := by
    rw [conorm_ofPoint, ← hsdef, WeilDivisor.ofFinsetWithMultiplicity_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun P' _ ↦ by rw [degree_zsmul, degree_ofPoint]
  have hterm : ∀ P' ∈ s,
      (Module.finrank k k' : ℤ) * ((Place.ramificationIdx F P' : ℤ) * P'.degree) =
        ((Place.ramificationIdx F P' * Place.relativeDegree k F P' : ℕ) : ℤ) * P.degree := by
    intro P' hP'
    have hrel := Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P'
    rw [(hs P').mp hP'] at hrel
    have hrel' : (Module.finrank k k' : ℤ) * (P'.degree : ℤ) =
        (Place.relativeDegree k F P' : ℤ) * (P.degree : ℤ) := by exact_mod_cast hrel
    push_cast
    linear_combination (Place.ramificationIdx F P' : ℤ) * hrel'
  rw [hdeg, Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum,
    Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P hs]

/-- **The degree of a conorm, cross-multiplied** (Stichtenoth, Corollary 3.1.14):
`[k' : k] · deg (Con D) = [F' : F] · deg D`.  Nothing here is divided, so no divisibility is
presupposed; dividing through by `[k' : k]` needs
`TauCeti.finrank_dvd_finrank_of_finrank_constantCompositum_eq`, and the divided identity is
`TauCeti.Divisor.degree_conorm`.

The separability hypothesis is the one carried by
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`. -/
theorem finrank_mul_degree_conorm (D : Divisor k F) :
    (Module.finrank k k' : ℤ) * degree (conorm k' F' D) = (Module.finrank F F' : ℤ) * degree D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, mul_add, hD, hE]
  | single P n =>
    rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, degree_zsmul, degree_zsmul,
      degree_ofPoint]
    linear_combination (n : ℤ) * finrank_mul_degree_conorm_ofPoint k' F' P

/-- **The degree of a conorm, divided through**: when adjoining the constant field `k'` to `F`
costs exactly `[k' : k]` — the degree form of linear disjointness of `F` and `k'` over `k` — so
that `[k' : k]` divides `[F' : F]` with quotient the geometric degree `n(F'/F)`, the conorm
multiplies degrees by `n(F'/F)`.

This is Stichtenoth's Corollary 3.6.4, under the additional separability hypothesis on `F' / F`
inherited from the fundamental identity that the cross-multiplied form rests on; Stichtenoth states
3.6.4 without it.  The cross-multiplied `TauCeti.Divisor.finrank_mul_degree_conorm`
(Corollary 3.1.14) is the form that holds without linear disjointness, and this is that identity
divided through by `[k' : k]`.

The separability hypothesis is the one carried by
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`.

The hypothesis `h` is supplied by
`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable` whenever `k' / k` is finite
separable and `k` is the exact constant field of `F`, and by
`TauCeti.finrank_constantCompositum_eq_finrank_of_linearDisjoint` from Mathlib's
`IntermediateField.LinearDisjoint`.  Together with the section's `[FiniteDimensional F F']` it
forces `[k' : k]` to be finite and positive, which is what licenses the division; no separate
finiteness assumption on `k' / k` is needed. -/
theorem degree_conorm
    (h : Module.finrank F (constantCompositum F k' F') = Module.finrank k k') (D : Divisor k F) :
    degree (conorm k' F' D) = geometricDegree F k' F' * degree D := by
  have hne : (Module.finrank k k' : ℤ) ≠ 0 := by
    have : 0 < Module.finrank k k' := h ▸ Module.finrank_pos
    exact_mod_cast this.ne'
  refine mul_left_cancel₀ hne ?_
  rw [finrank_mul_degree_conorm k' F' D,
    finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq F k' F' h]
  push_cast
  ring

end Degree

/-! ### Principal divisors and divisor classes -/

/-- **The conorm of a principal divisor is principal** (Stichtenoth, Proposition 3.1.9): the conorm
of `div z` is the divisor of the image of `z` in `F'`. -/
theorem conorm_principal (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (z : Fˣ) :
    conorm k' F' (principal hF z) =
      principal hF' (Units.map (algebraMap F F' : F →* F') z) := by
  refine WeilDivisor.ext fun P' ↦ ?_
  have hz : ((Units.map (algebraMap F F' : F →* F') z : F'ˣ) : F') = algebraMap F F' (z : F) := by
    simp
  rw [coeff_conorm, coeff_principal, coeff_principal, hz,
    Place.ord_algebraMap_restrict k F P' (z : F)]

/-- The conorm carries principal divisors to principal divisors. -/
theorem conorm_mem_principalSubgroup (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    {D : Divisor k F} (hD : D ∈ (Place.orderSystem hF).principalSubgroup) :
    conorm k' F' D ∈ (Place.orderSystem hF').principalSubgroup := by
  obtain ⟨z, rfl⟩ := (mem_principalSubgroup_iff hF).mp hD
  exact (mem_principalSubgroup_iff hF').mpr
    ⟨Units.map (algebraMap F F' : F →* F') z, (conorm_principal k' F' hF hF' z).symm⟩

/-- **The conorm respects linear equivalence** (Stichtenoth, Proposition 3.1.9). -/
theorem linearlyEquivalent_conorm (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    {A B : Divisor k F} (h : (Place.orderSystem hF).LinearlyEquivalent A B) :
    (Place.orderSystem hF').LinearlyEquivalent (conorm k' F' A) (conorm k' F' B) := by
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff] at h ⊢
  rw [← map_sub]
  exact conorm_mem_principalSubgroup k' F' hF hF' h

/-- **The conorm on divisor classes** (Stichtenoth, Proposition 3.1.9): the conorm descends to a
homomorphism `Cl(F) →+ Cl(F')` of divisor class groups. -/
noncomputable def conormClassGroup (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') :
    (Place.orderSystem hF).ClassGroup →+ (Place.orderSystem hF').ClassGroup :=
  WeilDivisor.OrderSystem.ClassGroup.lift (Place.orderSystem hF)
    ((Place.orderSystem hF').divisorClass.comp (conorm k' F')) fun z ↦ by
      rw [AddMonoidHom.coe_comp, Function.comp_apply,
        WeilDivisor.OrderSystem.divisorClass_eq_zero_iff]
      exact conorm_mem_principalSubgroup k' F' hF hF'
        ((Place.orderSystem hF).principalDivisor_mem_principalSubgroup z)

@[simp]
theorem conormClassGroup_divisorClass (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (D : Divisor k F) :
    conormClassGroup k' F' hF hF' ((Place.orderSystem hF).divisorClass D) =
      (Place.orderSystem hF').divisorClass (conorm k' F' D) :=
  WeilDivisor.OrderSystem.ClassGroup.lift_divisorClass _ _ _ D

end Extension

section Tower

universe u₀ u₁ u₂ v₀ v₁ v₂

variable {k₀ : Type u₀} {k₁ : Type u₁} {k₂ : Type u₂}
variable {F₀ : Type v₀} {F₁ : Type v₁} {F₂ : Type v₂}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
variable [FiniteDimensional F₀ F₁] [FiniteDimensional F₁ F₂]

variable (k₁ F₁ k₂ F₂)

/-- **The conorm is transitive in a tower** (Stichtenoth, Definition 3.1.8): the conorm from
`F₀ / k₀` to `F₂ / k₂` factors through `F₁ / k₁`.  This is the divisor form of the
multiplicativity of the ramification indices in a tower.

The finiteness of `F₂ / F₀`, which the direct conorm needs, is supplied by `FiniteDimensional.trans`
rather than assumed: `FiniteDimensional.trans` is not an instance, so it has to be installed by hand
in the statement. -/
@[simp]
theorem conorm_conorm (D : Divisor k₀ F₀) :
    haveI : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
    conorm k₂ F₂ (conorm k₁ F₁ D) = conorm k₂ F₂ D := by
  have : FiniteDimensional F₀ F₂ := FiniteDimensional.trans F₀ F₁ F₂
  refine WeilDivisor.ext fun P ↦ ?_
  have hres : (P.restrict k₁ F₁).restrict k₀ F₀ = P.restrict k₀ F₀ := Place.restrict_restrict P
  rw [coeff_conorm, coeff_conorm, coeff_conorm, hres,
    Place.ramificationIdx_restrict_mul (k₁ := k₁) (F₀ := F₀) (F₁ := F₁) P]
  push_cast
  ring

end Tower

end Divisor

end TauCeti

end
