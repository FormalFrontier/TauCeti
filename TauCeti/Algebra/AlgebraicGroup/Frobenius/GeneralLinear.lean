/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.FixedPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints

/-!
# The Frobenius on the matrix points of a closed subgroup scheme of `GLₙ`

Let `A` be a commutative ring of exponential characteristic `p`. On the `A`-valued points of an
integral Hopf algebra the `p ^ k`-power Frobenius acts by
`TauCeti.Bialgebra.iterateFrobeniusPoints`, raising every value of a point to the `p ^ k`-th power.
This file reads that endomorphism in matrix coordinates, for the general linear group and for the
closed subgroup schemes of it cut out by a Hopf ideal over `ℤ`.

Three things are proved. Under the identification of the convolution points of
`TauCeti.GeneralLinear.coordinateHopfAlgebra` with `GLₙ(A)`, the Frobenius on points is the
entrywise `p ^ k`-power map. That map preserves the matrix subgroup
`TauCeti.GeneralLinear.hopfIdealPointsSubgroup` cut out by a Hopf ideal, so it restricts to a group
endomorphism of the points of the closed subgroup scheme, with the expected iteration laws. And the
points fixed by that restriction are exactly the points of the same subgroup scheme valued in the
Frobenius-fixed subring of `A`, both as an equality of subgroups of `GLₙ(A)` and as an isomorphism
of groups.

For `p` prime, `0 < k`, `A` an algebraic closure of `ZMod p` and `q = p ^ k`, the fixed subring is
the field of `q` elements inside `A`, so the last statement is `G(𝔽_q) ≃* G(A)^F` for a closed
subgroup scheme `G` of `GLₙ` defined over `ℤ`. Nothing here asserts that either side is finite, and
no algebraic closedness, field, or finite-type hypothesis is used.

## Main definitions

* `TauCeti.GeneralLinear.iterateFrobeniusHopfIdealPoints`: the `p ^ k`-power Frobenius as a group
  endomorphism of the matrix points cut out by a Hopf ideal.
* `TauCeti.GeneralLinear.frobeniusFixedHopfIdealInclusion`: the entrywise inclusion of the matrix
  points valued in the Frobenius-fixed subring.
* `TauCeti.GeneralLinear.frobeniusFixedHopfIdealPointsMulEquiv`: the resulting isomorphism onto the
  Frobenius-fixed points.

## Main results

* `TauCeti.GeneralLinear.pointToGeneralLinear_iterateFrobeniusPoints` and
  `TauCeti.GeneralLinear.pointsMulEquiv_iterateFrobeniusPoints`: the Frobenius on general-linear
  points is the entrywise Frobenius on matrices.
* `TauCeti.GeneralLinear.mem_fixedSubgroup_map_iterateFrobenius_iff`: an invertible matrix is fixed
  by the entrywise Frobenius exactly when all of its entries are.
* `TauCeti.GeneralLinear.fixedSubgroup_map_iterateFrobenius_le_of_dvd`: the entrywise-fixed
  subgroups grow along divisibility of the exponent.
* `TauCeti.GeneralLinear.map_fixedSubgroup_iterateFrobeniusPoints`: the point equivalence carries
  the Frobenius-fixed points onto the entrywise-fixed matrices.
* `TauCeti.GeneralLinear.map_subtype_fixedSubgroup_iterateFrobeniusHopfIdealPoints`: the fixed
  points of the restricted Frobenius, read in `GLₙ(A)`.
* `TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring` and
  `TauCeti.GeneralLinear.range_frobeniusFixedHopfIdealInclusion`: those fixed points are the points
  of the same subgroup scheme over the Frobenius-fixed subring.

## Roadmap

This is the matrix form of the target "points over an algebraically closed field as a group,
functorially in the field, so that a field endomorphism induces a group endomorphism of the points"
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, which names the `q`-power Frobenius as the
first case a consumer asks for; `TauCeti/Algebra/AlgebraicGroup/Frobenius/Points.lean` and
`TauCeti/Algebra/AlgebraicGroup/Frobenius/FixedPoints.lean` supply the coordinate-free half. The
consumer is milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`, whose untwisted Steinberg map
is `Frob_q` on the points of a pinned Chevalley--Demazure group, and milestone L3, which sets
`H_d = fixedSubgroup d.steinberg`. The Chevalley carrier those milestones use is the closed subgroup
scheme of `GLₙ` over `ℤ` built by
`TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme`, which is presented by a Hopf ideal, so
it is an instance of the subgroup schemes treated here.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.9 and II.1.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe w

/-- `RingHom.toIntAlgHom` is a section of `AlgHom.toRingHom`. Kept private: it is a wrapper
identity, used only because the value-algebra interface of the general-linear points consumes
`ℤ`-algebra homomorphisms while Mathlib's Frobenius and the inclusion of a subring are ring
homomorphisms. -/
private lemma toRingHom_toIntAlgHom {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) :
    φ.toIntAlgHom.toRingHom = φ :=
  RingHom.ext fun _ => rfl

variable (n p k : ℕ)

section Points

variable {A : Type w} [CommRing A] [ExpChar A p]

/-- Reading the `p ^ k`-power Frobenius of a point as an invertible matrix gives the entrywise
`p ^ k`-power map. -/
@[simp]
theorem pointToGeneralLinear_iterateFrobeniusPoints
    (f : WithConv (coordinateHopfAlgebra ℤ n →ₐ[ℤ] A)) :
    pointToGeneralLinear (R := ℤ) n (Bialgebra.iterateFrobeniusPoints p k f) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)
        (pointToGeneralLinear (R := ℤ) n f) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, pointToGeneralLinear_apply,
    pointToGeneralLinear_apply, Bialgebra.iterateFrobeniusPoints_apply_apply,
    iterateFrobenius_def]

/-- The `p ^ k`-power Frobenius on the points of the general linear coordinate Hopf algebra is the
entrywise `p ^ k`-power map on invertible matrices.

Not a `simp` lemma, matching `TauCeti.GeneralLinear.pointsMulEquiv_mapValue`: `pointsMulEquiv_apply`
already rewrites the group equivalence to `pointToGeneralLinear`, so the simp-normal form of this
statement is `pointToGeneralLinear_iterateFrobeniusPoints`. -/
theorem pointsMulEquiv_iterateFrobeniusPoints
    (f : WithConv (coordinateHopfAlgebra ℤ n →ₐ[ℤ] A)) :
    pointsMulEquiv (R := ℤ) n (Bialgebra.iterateFrobeniusPoints p k f) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) (pointsMulEquiv (R := ℤ) n f) := by
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply]
  exact pointToGeneralLinear_iterateFrobeniusPoints n p k f

/-- The point equivalence intertwines the Frobenius on points with the entrywise Frobenius. -/
theorem pointsMulEquiv_comp_iterateFrobeniusPoints :
    (pointsMulEquiv (R := ℤ) (A := A) n).toMonoidHom.comp
        (Bialgebra.iterateFrobeniusPoints p k) =
      (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)).comp
        (pointsMulEquiv (R := ℤ) (A := A) n).toMonoidHom :=
  MonoidHom.ext (pointsMulEquiv_iterateFrobeniusPoints n p k)

/-- An invertible matrix is fixed by the entrywise `p ^ k`-power Frobenius exactly when every one
of its entries lies in the Frobenius-fixed subring. -/
theorem mem_fixedSubgroup_map_iterateFrobenius_iff
    (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ fixedSubgroup (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)) ↔
      ∀ i j, (g : Matrix (Fin n) (Fin n) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [mem_fixedSubgroup]
  constructor
  · intro hg i j
    rw [mem_frobeniusFixedSubring, ← iterateFrobenius_def,
      ← Matrix.GeneralLinearGroup.map_apply, hg]
  · intro hg
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]
    exact mem_frobeniusFixedSubring.mp (hg i j)

/-- The zeroth Frobenius iterate fixes every invertible matrix.

Deliberately not `@[simp]`: `iterateFrobenius_zero` already rewrites the ring homomorphism to the
identity, after which `Matrix.GeneralLinearGroup.map_id` and `fixedSubgroup_eq_top_iff` close the
goal, so a `simp` attribute here would be redundant. -/
theorem fixedSubgroup_map_iterateFrobenius_zero :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := Fin n) (iterateFrobenius A p 0)) = ⊤ := by
  rw [iterateFrobenius_zero, Matrix.GeneralLinearGroup.map_id]
  exact fixedSubgroup_eq_top_iff.mpr rfl

/-- The subgroups of entrywise Frobenius-fixed matrices grow along divisibility of the exponent.
In the motivating case this is the inclusion `GLₙ(𝔽_{p ^ m}) ⊆ GLₙ(𝔽_{p ^ l})`. -/
theorem fixedSubgroup_map_iterateFrobenius_le_of_dvd {m l : ℕ} (hml : m ∣ l) :
    fixedSubgroup (Matrix.GeneralLinearGroup.map (n := Fin n) (iterateFrobenius A p m)) ≤
      fixedSubgroup (Matrix.GeneralLinearGroup.map (n := Fin n) (iterateFrobenius A p l)) :=
  fun g hg =>
  (mem_fixedSubgroup_map_iterateFrobenius_iff n p l g).mpr fun i j =>
    frobeniusFixedSubring_le_of_dvd hml
      ((mem_fixedSubgroup_map_iterateFrobenius_iff n p m g).mp hg i j)

/-- The point equivalence carries the Frobenius-fixed points of the general linear coordinate Hopf
algebra onto the invertible matrices fixed entrywise by the Frobenius. -/
theorem map_fixedSubgroup_iterateFrobeniusPoints :
    (fixedSubgroup (Bialgebra.iterateFrobeniusPoints p k
          (H := coordinateHopfAlgebra ℤ n) (A := A))).map
        (pointsMulEquiv (R := ℤ) n).toMonoidHom =
      fixedSubgroup (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)) :=
  map_fixedSubgroup_eq _ (pointsMulEquiv_comp_iterateFrobeniusPoints n p k)

end Points

section ClosedSubgroup

variable (I : HopfIdeal ℤ (coordinateHopfAlgebra ℤ n))
variable {A : Type w} [CommRing A] [ExpChar A p]

/-- The entrywise `p ^ k`-power Frobenius preserves the matrix points cut out by a Hopf ideal over
`ℤ`: a closed subgroup scheme of `GLₙ` defined over `ℤ` is stable under Frobenius. -/
theorem map_iterateFrobenius_mem_hopfIdealPointsSubgroup
    {g : Matrix.GeneralLinearGroup (Fin n) A} (hg : g ∈ hopfIdealPointsSubgroup n I A) :
    Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g ∈ hopfIdealPointsSubgroup n I A := by
  have h := map_mem_hopfIdealPointsSubgroup n I (iterateFrobenius A p k).toIntAlgHom hg
  rwa [toRingHom_toIntAlgHom] at h

variable (A) in
/-- The `p ^ k`-power Frobenius as a group endomorphism of the matrix points cut out by a Hopf
ideal over `ℤ`.

This is the untwisted Steinberg endomorphism of a Chevalley carrier presented as a closed subgroup
scheme of `GLₙ` over `ℤ`. Unlike `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup` along a general
value-algebra homomorphism, it is an *endomorphism*, so it has a fixed subgroup and an iteration
law. -/
noncomputable def iterateFrobeniusHopfIdealPoints :
    hopfIdealPointsSubgroup n I A →* hopfIdealPointsSubgroup n I A :=
  mapHopfIdealPointsSubgroup n I (iterateFrobenius A p k).toIntAlgHom

/-- The Frobenius endomorphism of the matrix points cut out by a Hopf ideal acts by the entrywise
Frobenius. -/
@[simp]
theorem coe_iterateFrobeniusHopfIdealPoints (g : hopfIdealPointsSubgroup n I A) :
    (iterateFrobeniusHopfIdealPoints n p k I A g : Matrix.GeneralLinearGroup (Fin n) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [iterateFrobeniusHopfIdealPoints, coe_mapHopfIdealPointsSubgroup, toRingHom_toIntAlgHom]

/-- Entrywise, the Frobenius endomorphism of the matrix points cut out by a Hopf ideal raises each
entry to the `p ^ k`-th power. -/
theorem coe_iterateFrobeniusHopfIdealPoints_apply
    (g : hopfIdealPointsSubgroup n I A) (i j : Fin n) :
    ((iterateFrobeniusHopfIdealPoints n p k I A g :
        Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) i j =
      ((g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) i j ^ p ^ k := by
  rw [coe_iterateFrobeniusHopfIdealPoints, Matrix.GeneralLinearGroup.map_apply,
    iterateFrobenius_def]

/-- The zeroth Frobenius iterate is the identity on the matrix points cut out by a Hopf ideal. -/
@[simp]
theorem iterateFrobeniusHopfIdealPoints_zero :
    iterateFrobeniusHopfIdealPoints n p 0 I A = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [coe_iterateFrobeniusHopfIdealPoints, iterateFrobenius_zero,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply, MonoidHom.id_apply]

/-- Frobenius iterates add under composition on the matrix points cut out by a Hopf ideal. -/
theorem iterateFrobeniusHopfIdealPoints_add (m : ℕ) :
    iterateFrobeniusHopfIdealPoints n p (k + m) I A =
      (iterateFrobeniusHopfIdealPoints n p k I A).comp
        (iterateFrobeniusHopfIdealPoints n p m I A) := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [coe_iterateFrobeniusHopfIdealPoints, MonoidHom.comp_apply,
    coe_iterateFrobeniusHopfIdealPoints, coe_iterateFrobeniusHopfIdealPoints,
    iterateFrobenius_add, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]

/-- The points of a closed subgroup scheme fixed by the Frobenius, read as a subgroup of `GLₙ(A)`,
are the points of that subgroup scheme that the entrywise Frobenius fixes. -/
theorem map_subtype_fixedSubgroup_iterateFrobeniusHopfIdealPoints :
    (fixedSubgroup (iterateFrobeniusHopfIdealPoints n p k I A)).map
        (hopfIdealPointsSubgroup n I A).subtype =
      hopfIdealPointsSubgroup n I A ⊓
        fixedSubgroup (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨g, hg⟩, hfix, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
    have h : (iterateFrobeniusHopfIdealPoints n p k I A ⟨g, hg⟩ :
        Matrix.GeneralLinearGroup (Fin n) A) = g := congrArg _ (mem_fixedSubgroup.mp hfix)
    rwa [coe_iterateFrobeniusHopfIdealPoints] at h
  · intro g hg
    obtain ⟨hgI, hgF⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgI⟩, mem_fixedSubgroup.mpr (Subtype.ext ?_), rfl⟩
    rw [coe_iterateFrobeniusHopfIdealPoints]
    exact mem_fixedSubgroup.mp hgF

end ClosedSubgroup

section RationalPoints

variable (I : HopfIdeal ℤ (coordinateHopfAlgebra ℤ n))
variable {A : Type w} [CommRing A] [ExpChar A p]

/-- The points of a closed subgroup scheme of `GLₙ` over `ℤ` valued in the Frobenius-fixed subring
of `A` are exactly the `A`-valued points of that subgroup scheme fixed by the entrywise
`p ^ k`-power Frobenius.

For `p` prime, `0 < k`, `A` an algebraic closure of `ZMod p` and `q = p ^ k` this is
`G(𝔽_q) = G(A)^F`, the description of the rational points of a group of Lie type as the fixed
points of a Frobenius endomorphism. -/
theorem map_hopfIdealPointsSubgroup_frobeniusFixedSubring :
    (hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k)).map
        (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) =
      hopfIdealPointsSubgroup n I A ⊓
        fixedSubgroup (Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := map_mem_hopfIdealPointsSubgroup n I
        (frobeniusFixedSubring A p k).subtype.toIntAlgHom hg
      rwa [toRingHom_toIntAlgHom] at h
    · refine (mem_fixedSubgroup_map_iterateFrobenius_iff n p k _).mpr fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, Subring.coe_subtype]
      exact SetLike.coe_mem _
  · intro g hg
    obtain ⟨hgI, hgF⟩ := Subgroup.mem_inf.mp hg
    -- Read the matrix as a point. It is Frobenius-fixed, hence valued in the fixed subring, and
    -- the point over that subring still kills the Hopf ideal, because the inclusion is injective.
    have hfix : (pointsMulEquiv (R := ℤ) n).symm g ∈
        fixedSubgroup (Bialgebra.iterateFrobeniusPoints p k
          (H := coordinateHopfAlgebra ℤ n) (A := A)) := by
      refine mem_fixedSubgroup.mpr ((pointsMulEquiv (R := ℤ) n).injective ?_)
      rw [pointsMulEquiv_iterateFrobeniusPoints, MulEquiv.apply_symm_apply]
      exact mem_fixedSubgroup.mp hgF
    rw [← Bialgebra.range_frobeniusFixedInclusion p k] at hfix
    obtain ⟨f, hf⟩ := hfix
    refine ⟨pointsMulEquiv (R := ℤ) n f, ?_, ?_⟩
    · refine (mem_hopfIdealPointsSubgroup_iff n I _ _).mpr fun x hx => ?_
      rw [MulEquiv.symm_apply_apply]
      have h0 : ((pointsMulEquiv (R := ℤ) n).symm g).ofConv x = 0 :=
        (mem_hopfIdealPointsSubgroup_iff n I A g).mp hgI x hx
      rw [← hf, Bialgebra.frobeniusFixedInclusion_apply_apply] at h0
      exact Subtype.ext h0
    · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, pointsMulEquiv_apply, pointToGeneralLinear_apply,
        Subring.coe_subtype, ← Bialgebra.frobeniusFixedInclusion_apply_apply, hf,
        ← pointToGeneralLinear_apply, ← pointsMulEquiv_apply, MulEquiv.apply_symm_apply]

variable (A) in
/-- The entrywise inclusion of the matrix points of a closed subgroup scheme valued in the
Frobenius-fixed subring of `A` into its `A`-valued matrix points. In the motivating case this is
`G(𝔽_q) → G(A)`. -/
noncomputable def frobeniusFixedHopfIdealInclusion :
    hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k) →*
      hopfIdealPointsSubgroup n I A :=
  mapHopfIdealPointsSubgroup n I (frobeniusFixedSubring A p k).subtype.toIntAlgHom

/-- The inclusion of the rational points reads each entry of a matrix over the Frobenius-fixed
subring as an element of `A`. -/
@[simp]
theorem coe_frobeniusFixedHopfIdealInclusion
    (g : hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k)) :
    (frobeniusFixedHopfIdealInclusion n p k I A g : Matrix.GeneralLinearGroup (Fin n) A) =
      Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype g := by
  rw [frobeniusFixedHopfIdealInclusion, coe_mapHopfIdealPointsSubgroup, toRingHom_toIntAlgHom]

/-- Reading a matrix point over the Frobenius-fixed subring as one over `A` loses no
information. -/
theorem frobeniusFixedHopfIdealInclusion_injective :
    Function.Injective (frobeniusFixedHopfIdealInclusion n p k I A) := by
  intro g g' hgg'
  have h := congrArg
    (fun x : hopfIdealPointsSubgroup n I A => (x : Matrix.GeneralLinearGroup (Fin n) A)) hgg'
  rw [coe_frobeniusFixedHopfIdealInclusion, coe_frobeniusFixedHopfIdealInclusion] at h
  refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => Subtype.ext ?_)
  have hij := congrFun (congrFun (congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) A =>
    (x : Matrix (Fin n) (Fin n) A)) h) i) j
  rwa [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply] at hij

/-- The rational points of a closed subgroup scheme are exactly the points fixed by its Frobenius
endomorphism. This is `TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring`
read inside the point group of the subgroup scheme rather than inside `GLₙ(A)`. -/
theorem range_frobeniusFixedHopfIdealInclusion :
    (frobeniusFixedHopfIdealInclusion n p k I A).range =
      fixedSubgroup (iterateFrobeniusHopfIdealPoints n p k I A) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
    rw [coe_iterateFrobeniusHopfIdealPoints]
    refine (mem_fixedSubgroup_map_iterateFrobenius_iff n p k _).mpr fun i j => ?_
    rw [coe_frobeniusFixedHopfIdealInclusion, Matrix.GeneralLinearGroup.map_apply,
      Subring.coe_subtype]
    exact SetLike.coe_mem _
  · intro x hx
    have hmem : (x : Matrix.GeneralLinearGroup (Fin n) A) ∈
        Subgroup.map (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype)
          (hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k)) := by
      rw [map_hopfIdealPointsSubgroup_frobeniusFixedSubring n p k I,
        ← map_subtype_fixedSubgroup_iterateFrobeniusHopfIdealPoints n p k I]
      exact ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hgx⟩ := hmem
    exact ⟨⟨g, hg⟩, Subtype.ext (by rw [coe_frobeniusFixedHopfIdealInclusion]; exact hgx)⟩

variable (A) in
/-- **The rational points of a closed subgroup scheme of `GLₙ` are the Frobenius-fixed points.**
For `p` prime, `0 < k`, `A` an algebraic closure of `ZMod p` and `q = p ^ k` this is the
isomorphism `G(𝔽_q) ≃* G(A)^F` identifying the rational points of a group of Lie type with the
fixed points of its Frobenius. -/
noncomputable def frobeniusFixedHopfIdealPointsMulEquiv :
    hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k) ≃*
      fixedSubgroup (iterateFrobeniusHopfIdealPoints n p k I A) :=
  (MonoidHom.ofInjective (frobeniusFixedHopfIdealInclusion_injective n p k I)).trans
    (MulEquiv.subgroupCongr (range_frobeniusFixedHopfIdealInclusion n p k I))

/-- The isomorphism onto the Frobenius-fixed points is the inclusion of the rational points. -/
@[simp]
theorem coe_frobeniusFixedHopfIdealPointsMulEquiv
    (g : hopfIdealPointsSubgroup n I ↥(frobeniusFixedSubring A p k)) :
    (frobeniusFixedHopfIdealPointsMulEquiv n p k I A g : hopfIdealPointsSubgroup n I A) =
      frobeniusFixedHopfIdealInclusion n p k I A g := by
  rw [frobeniusFixedHopfIdealPointsMulEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- The inverse of the isomorphism reads a Frobenius-fixed matrix point as a point over the
Frobenius-fixed subring: including it back into the `A`-valued points returns the point one started
from. -/
@[simp]
theorem frobeniusFixedHopfIdealInclusion_frobeniusFixedHopfIdealPointsMulEquiv_symm_apply
    (x : fixedSubgroup (iterateFrobeniusHopfIdealPoints n p k I A)) :
    frobeniusFixedHopfIdealInclusion n p k I A
        ((frobeniusFixedHopfIdealPointsMulEquiv n p k I A).symm x) =
      (x : hopfIdealPointsSubgroup n I A) := by
  rw [← coe_frobeniusFixedHopfIdealPointsMulEquiv, MulEquiv.apply_symm_apply]

end RationalPoints

end TauCeti.GeneralLinear
