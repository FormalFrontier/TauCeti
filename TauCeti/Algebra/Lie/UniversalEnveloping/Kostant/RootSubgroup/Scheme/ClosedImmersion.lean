/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# A Kostant root subgroup is a closed copy of the additive group

Let a Kostant integral form act on a rational representation, preserving an integral lattice `M`
with finite basis `b`. A nilpotent root vector `eᵢ` then gives the scheme morphism
`xᵢ : 𝔾ₐ → GLₙ` of `RootSubgroup.Scheme.Basic`. A pinning of a Chevalley--Demazure group needs
more than this morphism: the root subgroup has to be a *closed* subgroup scheme, and it has to be
a faithful copy of `𝔾ₐ`, so that `xᵢ(t)` determines `t`.

Both follow from a single piece of data, available in every Chevalley basis: a *root step*, that
is a pair of basis indices `r`, `s` together with a unit `c : ℤ` such that

```text
ρ(eᵢ) (b s) = c • b r    and    ρ(eᵢ) (ρ(eᵢ) (b s)) = 0.
```

The second condition truncates the divided-power exponential in that matrix column, so the
`(r, s)` entry of `xᵢ(t)` is exactly `c t` rather than a polynomial of higher degree. Consequently
the coordinate Hopf-algebra morphism `O(GLₙ) → O(𝔾ₐ)` hits the polynomial generator, hence is
surjective, and `xᵢ` is a closed immersion.

A root step is not a normalization that could be arranged by rescaling the basis: it says that the
column of `eᵢ` at `b s` is a single basis vector with unit coefficient, which is what integrality
of the Chevalley structure constants supplies. In a simply laced type it holds for `s` the index of
a root vector `e_β` with `β + αᵢ` a root and `β + 2αᵢ` not a root.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.repr_kostantRootSubgroupPoints_baseChange`: the coordinates
  of a root-subgroup point on a base-changed basis vector.
* `TauCeti.UniversalEnvelopingAlgebra.repr_kostantRootSubgroupPoints_of_isRootStep`: a root step
  makes one coordinate equal to the parameter, scaled by the unit `c`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply_of_isRootStep`: the same
  statement read as a matrix entry.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_injective`: the root subgroup is
  faithfully parametrized by `𝔾ₐ`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap_surjective`: the coordinate
  Hopf-algebra morphism of the root subgroup is surjective.
* `TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroup`: the root subgroup
  `𝔾ₐ → GLₙ` is a closed immersion.
* `TauCeti.UniversalEnvelopingAlgebra.mono_kostantRootSubgroup`: it is a monomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupClosedSubgroup`: the resulting closed
  subgroup scheme of `GLₙ`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section RootStepAux

variable {V : Type v} [AddCommGroup V] {M : AddSubgroup V} {η : Type*} {c : ℤ}

/-- A unit integer scalar cancels: `±1` never annihilates a nonzero vector. -/
private theorem eq_zero_of_unit_zsmul_eq_zero (hc : IsUnit c) {y : V} (hy : c • y = 0) : y = 0 := by
  rcases Int.isUnit_iff.1 hc with rfl | rfl
  · simpa using hy
  · simpa using hy

/-- A basis vector of an integral lattice is nonzero in the ambient space. -/
private theorem coe_basis_ne_zero (b : Module.Basis η ℤ M) (j : η) : ((b j : M) : V) ≠ 0 :=
  fun hj => b.ne_zero j (Subtype.ext hj)

variable [Module ℚ V] {x : Module.End ℚ V} {b : Module.Basis η ℤ M} {r s : η}

/-- The zeroth restricted divided power leaves a lattice vector alone. -/
private theorem integralDividedPower_zero_apply
    (hmem : ∀ v ∈ M, Associative.dividedPower 0 x • v ∈ M) (v : M) :
    integralDividedPower x M 0 hmem v = v := by
  rw [integralDividedPower_zero]
  rfl

/-- The first restricted divided power is the operator itself, so a root step computes it. -/
private theorem integralDividedPower_one_apply_of_step
    (hmem : ∀ v ∈ M, Associative.dividedPower 1 x • v ∈ M) {v w : M}
    (hstep : x (v : V) = c • (w : V)) :
    integralDividedPower x M 1 hmem v = c • w := by
  refine Subtype.ext ?_
  rw [coe_integralDividedPower_apply, Associative.dividedPower_one, AddSubgroup.coe_zsmul]
  exact hstep

/-- Beyond the first divided power, the column of a root step vanishes. -/
private theorem integralDividedPower_apply_eq_zero_of_two_le {k : ℕ}
    (hmem : ∀ v ∈ M, Associative.dividedPower k x • v ∈ M) {v : M}
    (hsq : x (x (v : V)) = 0) (hk : 2 ≤ k) :
    integralDividedPower x M k hmem v = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  refine Subtype.ext ?_
  rw [coe_integralDividedPower_apply, Associative.dividedPower_def,
    ZeroMemClass.coe_zero, smul_assoc]
  have hpow : (x ^ (m + 2)) (v : V) = 0 := by
    rw [pow_add, Module.End.mul_apply, pow_two, Module.End.mul_apply, hsq, map_zero]
  rw [show (x ^ (m + 2)) • (v : V) = (x ^ (m + 2)) (v : V) from rfl, hpow, smul_zero]

/-- A root step forces the operator to have nilpotency class at least two, so the linear term of
its divided-power exponential is present. -/
private theorem two_le_nilpotencyClass_of_step (hx : IsNilpotent x) (hc : IsUnit c)
    (hstep : x (b s : V) = c • (b r : V)) :
    2 ≤ nilpotencyClass x := by
  by_contra hlt
  have hone : x ^ 1 = 0 := pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hx)
  rw [pow_one] at hone
  refine coe_basis_ne_zero b r (eq_zero_of_unit_zsmul_eq_zero hc ?_)
  rw [← hstep, hone]
  rfl

/-- A root step separates the two basis indices it names. -/
private theorem ne_of_step (hc : IsUnit c) (hstep : x (b s : V) = c • (b r : V))
    (hsq : x (x (b s : V)) = 0) : r ≠ s := by
  rintro rfl
  refine coe_basis_ne_zero b r
    (eq_zero_of_unit_zsmul_eq_zero hc (eq_zero_of_unit_zsmul_eq_zero hc ?_))
  rw [← mul_smul, mul_smul, ← hstep, ← map_zsmul, ← hstep]
  exact hsq

end RootStepAux

section Coordinates

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} (b : Module.Basis η ℤ M)

/-- The coordinates of a root-subgroup point on a base-changed basis vector: the `r`-th
coordinate of `xᵢ(t) (1 ⊗ b s)` is the divided-power polynomial in `t` whose coefficients are the
`r`-th coordinates of the integral divided powers of `b s`. -/
theorem repr_kostantRootSubgroupPoints_baseChange {A : Type*} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (r s : η) :
    (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val (b.baseChange A s)) r =
      ∑ k ∈ Finset.range
          (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
        b.repr (integralDividedPower
            (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
              e h ρ hM i k hv) (b s)) r •
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) ^ k := by
  rw [Module.Basis.baseChange_apply, kostantRootSubgroupPoints_tmul, map_sum,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.Basis.baseChange_repr_tmul, mul_one]

variable {r s : η} {c : ℤ}
variable (hc : IsUnit c)
variable (hstep : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) = c • (b r : V))
variable (hsq : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V)) = 0)

include hnil hc hstep hsq in
/-- **The pinning coordinate of a root subgroup.** At a root step, the `r`-th coordinate of
`xᵢ(t) (1 ⊗ b s)` is the parameter itself, scaled by the unit `c`. Every higher divided power
lands in other coordinates, so no higher power of the parameter appears. -/
theorem repr_kostantRootSubgroupPoints_of_isRootStep {A : Type*} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val (b.baseChange A s)) r =
      c • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) := by
  classical
  have hrs : ¬ (s = r) := Ne.symm (ne_of_step hc hstep hsq)
  rw [repr_kostantRootSubgroupPoints_baseChange,
    ← Finset.sum_subset
      (Finset.range_subset_range.2 (two_le_nilpotencyClass_of_step hnil hc hstep))]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, integralDividedPower_zero_apply,
      integralDividedPower_one_apply_of_step _ hstep]
    simp [hrs]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [integralDividedPower_apply_eq_zero_of_two_le _ hsq (by omega)]
    simp

include hnil hc hstep hsq in
/-- **The root subgroup is a faithful copy of `𝔾ₐ`.** Distinct parameters give distinct
automorphisms of the base-changed lattice. -/
theorem kostantRootSubgroupPoints_injective {A : Type*} [CommRing A] :
    Function.Injective (kostantRootSubgroupPoints e h ρ M hM i hnil (A := A)) := by
  intro f g hfg
  refine (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).injective
    (Multiplicative.toAdd.injective ?_)
  have hcoord : c • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) =
      c • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) := by
    rw [← repr_kostantRootSubgroupPoints_of_isRootStep e h ρ M hM i hnil b hc hstep hsq,
      ← repr_kostantRootSubgroupPoints_of_isRootStep e h ρ M hM i hnil b hc hstep hsq, hfg]
  rcases Int.isUnit_iff.1 hc with rfl | rfl
  · simpa using hcoord
  · simpa using hcoord

variable [Fintype η] [DecidableEq η]

include hnil hc hstep hsq in
/-- At a root step, the `(r, s)` entry of the root-subgroup matrix is the parameter, scaled by
the unit `c`. -/
theorem kostantRootSubgroupMatrix_apply_of_isRootStep {A : Type*} [CommRing A]
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b f r s =
      c • Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) := by
  rw [kostantRootSubgroupMatrix_apply,
    repr_kostantRootSubgroupPoints_of_isRootStep e h ρ M hM i hnil b hc hstep hsq]

end Coordinates

section Scheme

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (i : I)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable {r s : Fin n} {c : ℤ}
variable (hc : IsUnit c)
variable (hstep : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) = c • (b r : V))
variable (hsq : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V)) = 0)

include hc hstep hsq in
/-- At a root step, the coordinate morphism of the root subgroup sends the `(r, s)` generic matrix
coordinate to the polynomial generator, scaled by the unit `c`. -/
theorem kostantRootSubgroupCoordinateMap_X_of_isRootStep :
    (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s)))) =
      c • SymmetricAlgebra.ι ℤ ℤ 1 := by
  have key := pointsMulEquiv_kostantRootSubgroupCoordinateMap_apply e h ρ M hM i hnil b
    (SymmetricAlgebra ℤ ℤ) (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ))) r s
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply] at key
  -- The identity point composes trivially, so `key` already computes the coordinate morphism.
  have key' : (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
        (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s)))) =
      (b.baseChange (SymmetricAlgebra ℤ ℤ)).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil
          (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ)))).val
          (b.baseChange (SymmetricAlgebra ℤ ℤ) s)) r := key
  have hval := repr_kostantRootSubgroupPoints_of_isRootStep e h ρ M hM i hnil b hc hstep hsq
    (A := SymmetricAlgebra ℤ ℤ) (toConv (AlgHom.id ℤ (SymmetricAlgebra ℤ ℤ)))
  refine (key'.trans hval).trans ?_
  congr 1
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv, WithConv.ofConv_toConv]
  rfl

include hc hstep hsq in
/-- **The coordinate morphism of a root subgroup is surjective.** Its image is a subalgebra of
the polynomial coordinate algebra of `𝔾ₐ` containing the generator, hence everything. -/
theorem kostantRootSubgroupCoordinateMap_surjective :
    Function.Surjective (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom := by
  have hgen : SymmetricAlgebra.ι ℤ ℤ 1 ∈
      (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom.range := by
    obtain ⟨u, hu⟩ := id hc
    refine (AlgHom.mem_range _).2
      ⟨((u⁻¹ : ℤˣ) : ℤ) • GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
        (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s))), ?_⟩
    change (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom
        (((u⁻¹ : ℤˣ) : ℤ) • GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
          (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s)))) =
        SymmetricAlgebra.ι ℤ ℤ 1
    rw [map_zsmul,
      kostantRootSubgroupCoordinateMap_X_of_isRootStep e h ρ M hM i hnil b hc hstep hsq,
      smul_smul, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  intro y
  have hy : y ∈ (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom.range := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap z => exact Subalgebra.algebraMap_mem _ z
    | ι z =>
        have hz : SymmetricAlgebra.ι ℤ ℤ z = z • SymmetricAlgebra.ι ℤ ℤ 1 := by
          rw [← map_zsmul]
          congr 1
          simp
        rw [hz]
        exact zsmul_mem hgen z
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨z, hz⟩

include hc hstep hsq in
/-- **A Kostant root subgroup is a closed immersion.** The one-parameter subgroup
`xᵢ : 𝔾ₐ → GLₙ` identifies `𝔾ₐ` with a closed subscheme of `GLₙ` over `ℤ`. -/
theorem isClosedImmersion_kostantRootSubgroup :
    IsClosedImmersion (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom.left := by
  rw [kostantRootSubgroup_def,
    CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
      (AdditiveGroup.groupScheme_def ℤ) (GeneralLinear.groupScheme_def ℤ n)]
  exact kostantRootSubgroupCoordinateMap_surjective e h ρ M hM i hnil b hc hstep hsq

include hc hstep hsq in
/-- A root subgroup is a monomorphism of group schemes over `ℤ`. -/
theorem mono_kostantRootSubgroup : Mono (kostantRootSubgroup e h ρ M hM i hnil b) :=
  have := isClosedImmersion_kostantRootSubgroup e h ρ M hM i hnil b hc hstep hsq
  mono_of_isClosedImmersion_underlying (kostantRootSubgroup e h ρ M hM i hnil b)

/-- **The root subgroup as a closed subgroup scheme of `GLₙ`.** This is the subgroup `U_αᵢ` that a
pinning carries: a closed subgroup scheme which the root-subgroup morphism identifies with `𝔾ₐ`. -/
noncomputable def kostantRootSubgroupClosedSubgroup
    (hc : IsUnit c)
    (hstep : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) = c • (b r : V))
    (hsq : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V)) = 0) :
    ClosedSubgroupScheme (GeneralLinear.groupScheme ℤ n) :=
  haveI := isClosedImmersion_kostantRootSubgroup e h ρ M hM i hnil b hc hstep hsq
  ClosedSubgroupScheme.mk (kostantRootSubgroup e h ρ M hM i hnil b)

end Scheme

end TauCeti.UniversalEnvelopingAlgebra
