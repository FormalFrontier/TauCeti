/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import TauCeti.Algebra.Homology.DG.Algebra.Defs

/-!
# The cohomology algebra of a differential graded algebra

Let `d` be a differential on an internally `ℤ`-graded `R`-algebra `𝒜` on a carrier `A`, in the
sense of `TauCeti.IsDGAlgebra`.  Its **cycles** are the kernel of `d` and its **boundaries** are the
image of `d`.  This file shows that the cycles form a subalgebra of `A`, that the boundaries form a
two-sided ideal of that subalgebra, and that the resulting quotient `R`-algebra -- the **cohomology
algebra** `H(A)` -- inherits a `ℤ`-grading whose degree-`p` piece is the module of classes of
homogeneous cycles of degree `p`.

Two features of the graded Leibniz rule drive everything.  First, its sign depends only on the
degree of the left factor, so a product with a cycle on the right is differentiated without any
sign; this makes the cycles closed under multiplication and makes a boundary times a cycle a
boundary.  Second, the differential is homogeneous, so it commutes with the projections of the
grading up to a shift of one.  Consequently the degree-`p` component of a boundary `d a` is
`d (a_{p-1})`, again a boundary, which is exactly the statement that the boundaries are a
homogeneous ideal -- the input to the independence half of the decomposition of `H(A)`.

Because `A` is not assumed commutative, the boundaries are recorded as a `TwoSidedIdeal` of the
cycles and the cohomology algebra is the associated `RingCon` quotient.

## Main definitions

* `TauCeti.IsDGAlgebra.cycles`: the kernel of the differential, as a subalgebra.
* `TauCeti.IsDGAlgebra.cyclesDeg`: the homogeneous cycles of a fixed degree.
* `TauCeti.IsDGAlgebra.boundaries`: the image of the differential, as a two-sided ideal of the
  cycles.
* `TauCeti.IsDGAlgebra.cohomology` and `TauCeti.IsDGAlgebra.toCohomology`: the cohomology algebra
  and the map taking a cycle to its class.
* `TauCeti.IsDGAlgebra.cohomologyGrading`: the grading of the cohomology algebra by the classes of
  homogeneous cycles.
* `TauCeti.algEquivCohomologyOfZero`: a graded algebra with zero differential is its own
  cohomology.

## Main results

* `TauCeti.IsDGAlgebra.iSup_cyclesDeg` and `TauCeti.IsDGAlgebra.iSup_cohomologyGrading`: every
  cycle, and every cohomology class, is a sum of homogeneous ones.
* `TauCeti.IsDGAlgebra.iSupIndep_cohomologyGrading`: homogeneous cohomology classes of distinct
  degrees are independent.
* `TauCeti.IsDGAlgebra.instGradedAlgebraCohomologyGrading`: **the cohomology of a differential
  graded algebra is a graded algebra.**
* `TauCeti.map_algEquivCohomologyOfZero`: the identification of a graded algebra carrying the zero
  differential with its own cohomology matches the two gradings degreewise.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 1, item "DG algebras, categories,
modules, and bimodules", specifically its first request for "cycles, boundaries, and the induced
graded cohomology algebra".  No formalization is vendored: the graded decomposition, the two-sided
ideal interface and the ring-congruence quotient are Mathlib's.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace IsDGAlgebra

/-- The **cycles** of a differential graded algebra: the kernel of the differential.  It is a
subalgebra because the differential annihilates the image of the ground ring and, by the Leibniz
rule applied componentwise, a product of cycles is a cycle. -/
def cycles (h : IsDGAlgebra 𝒜 d) : Subalgebra R A where
  carrier := {a | d a = 0}
  mul_mem' ha hb := h.map_mul_eq_zero ha hb
  one_mem' := h.map_one
  add_mem' {a b} ha hb := by
    have ha' : d a = 0 := ha
    have hb' : d b = 0 := hb
    simp only [Set.mem_ofPred_eq, map_add, ha', hb', add_zero]
  zero_mem' := map_zero d
  algebraMap_mem' := h.map_algebraMap

@[simp]
lemma mem_cycles (h : IsDGAlgebra 𝒜 d) {a : A} : a ∈ h.cycles ↔ d a = 0 := Iff.rfl

/-- The degree-`p` homogeneous cycles, as a submodule of the algebra of cycles. -/
def cyclesDeg (h : IsDGAlgebra 𝒜 d) (p : ℤ) : Submodule R h.cycles :=
  (𝒜 p).comap h.cycles.val.toLinearMap

@[simp]
lemma mem_cyclesDeg (h : IsDGAlgebra 𝒜 d) {p : ℤ} {z : h.cycles} :
    z ∈ h.cyclesDeg p ↔ (z : A) ∈ 𝒜 p := Iff.rfl

/-- Every cycle is a sum of homogeneous cycles: the homogeneous components of a cycle are cycles,
and they add up to it. -/
theorem iSup_cyclesDeg (h : IsDGAlgebra 𝒜 d) : ⨆ p : ℤ, h.cyclesDeg p = ⊤ := by
  classical
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : d (z : A) = 0 := z.2
  set s := (decompose 𝒜 (z : A)).support
  have hmem : ∀ p : ℤ, d (decompose 𝒜 (z : A) p : A) = 0 := fun p => h.map_decompose_eq_zero hz p
  have hsum : z = ∑ p ∈ s, (⟨(decompose 𝒜 (z : A) p : A), hmem p⟩ : h.cycles) := by
    refine Subtype.ext ?_
    simpa [AddSubmonoidClass.coe_finsetSum] using
      (DirectSum.sum_support_decompose 𝒜 (z : A)).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.mem_iSup_of_mem p (SetLike.coe_mem (decompose 𝒜 (z : A) p))

/-- The **boundaries** of a differential graded algebra: the image of the differential, viewed
inside the cycles.  It is a two-sided ideal there: a cycle times a boundary is a boundary by the
Leibniz rule read backwards, and a boundary times a cycle is the differential of the same
product. -/
def boundaries (h : IsDGAlgebra 𝒜 d) : TwoSidedIdeal h.cycles := by
  have zero_mem : ((0 : h.cycles) : A) ∈ LinearMap.range d := by
    simpa only [Subalgebra.coe_zero] using Submodule.zero_mem (LinearMap.range d)
  have add_mem {x y : h.cycles} (hx : (x : A) ∈ LinearMap.range d)
      (hy : (y : A) ∈ LinearMap.range d) : ((x + y : h.cycles) : A) ∈ LinearMap.range d := by
    simpa only [Subalgebra.coe_add] using Submodule.add_mem (LinearMap.range d) hx hy
  have neg_mem {x : h.cycles} (hx : (x : A) ∈ LinearMap.range d) :
      ((-x : h.cycles) : A) ∈ LinearMap.range d := by
    simpa only [Subalgebra.coe_neg] using Submodule.neg_mem (LinearMap.range d) hx
  have mul_left_mem {x y : h.cycles} (hy : (y : A) ∈ LinearMap.range d) :
      ((x * y : h.cycles) : A) ∈ LinearMap.range d := by
    obtain ⟨b, hb⟩ := hy
    simpa only [Subalgebra.coe_mul, ← hb] using h.mul_mem_range_of_map_left_eq_zero x.2 b
  have mul_right_mem {x y : h.cycles} (hx : (x : A) ∈ LinearMap.range d) :
      ((x * y : h.cycles) : A) ∈ LinearMap.range d := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨a * (y : A), by
      rw [h.map_mul_of_map_right_eq_zero a y.2, ha, Subalgebra.coe_mul]⟩
  exact TwoSidedIdeal.mk' {z : h.cycles | (z : A) ∈ LinearMap.range d}
    zero_mem add_mem neg_mem mul_left_mem mul_right_mem

@[simp]
lemma mem_boundaries (h : IsDGAlgebra 𝒜 d) {z : h.cycles} :
    z ∈ h.boundaries ↔ (z : A) ∈ LinearMap.range d := by
  rw [boundaries]
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

/-- The **cohomology algebra** `H(A)` of a differential graded algebra: the cycles modulo the
boundaries. -/
abbrev cohomology (h : IsDGAlgebra 𝒜 d) : Type _ := h.boundaries.ringCon.Quotient

/-- The passage from a cycle to its cohomology class. -/
def toCohomology (h : IsDGAlgebra 𝒜 d) : h.cycles →ₐ[R] h.cohomology :=
  RingCon.mkₐ R h.boundaries.ringCon

lemma toCohomology_surjective (h : IsDGAlgebra 𝒜 d) : Function.Surjective h.toCohomology :=
  RingCon.mkₐ_surjective _

@[simp]
lemma toCohomology_eq_zero_iff (h : IsDGAlgebra 𝒜 d) {z : h.cycles} :
    h.toCohomology z = 0 ↔ z ∈ h.boundaries := by
  have hzero : (0 : h.cohomology) = h.toCohomology 0 := (map_zero h.toCohomology).symm
  rw [hzero]
  exact (RingCon.eq _).trans (by rw [TwoSidedIdeal.rel_iff, sub_zero])

/-- The homogeneous projections annihilate everything supported in the other degrees. -/
private theorem proj_eq_zero_of_mem_biSup {p : ℤ} {x : A}
    (hx : x ∈ ⨆ (q : ℤ) (_ : q ≠ p), 𝒜 q) : GradedRing.proj 𝒜 p x = 0 := by
  refine Submodule.iSup_induction (motive := fun y => GradedRing.proj 𝒜 p y = 0) _ hx
    (fun q y hy => ?_) (map_zero _) (fun y y' hy hy' => by rw [map_add, hy, hy', add_zero])
  by_cases hq : q = p
  · subst hq
    rw [iSup_neg (fun hne => hne rfl), Submodule.mem_bot] at hy
    rw [hy, map_zero]
  · rw [iSup_pos hq] at hy
    exact DirectSum.decompose_of_mem_ne 𝒜 hy hq

/-- The grading of the cohomology algebra: the degree-`p` piece consists of the classes of the
homogeneous cycles of degree `p`. -/
def cohomologyGrading (h : IsDGAlgebra 𝒜 d) (p : ℤ) : Submodule R h.cohomology :=
  (h.cyclesDeg p).map h.toCohomology.toLinearMap

lemma mem_cohomologyGrading (h : IsDGAlgebra 𝒜 d) {p : ℤ} {x : h.cohomology} :
    x ∈ h.cohomologyGrading p ↔ ∃ z : h.cycles, (z : A) ∈ 𝒜 p ∧ h.toCohomology z = x :=
  Submodule.mem_map

instance instGradedMonoidCohomologyGrading (h : IsDGAlgebra 𝒜 d) :
    SetLike.GradedMonoid h.cohomologyGrading where
  one_mem := h.mem_cohomologyGrading.mpr
    ⟨1, by simpa only [Subalgebra.coe_one] using SetLike.one_mem_graded 𝒜,
      _root_.map_one h.toCohomology⟩
  mul_mem := by
    rintro i j x y hx hy
    obtain ⟨z, hz, rfl⟩ := h.mem_cohomologyGrading.mp hx
    obtain ⟨w, hw, rfl⟩ := h.mem_cohomologyGrading.mp hy
    refine h.mem_cohomologyGrading.mpr ⟨z * w, ?_, map_mul _ _ _⟩
    simpa only [Subalgebra.coe_mul] using SetLike.mul_mem_graded hz hw

/-- Every cohomology class is a sum of homogeneous classes. -/
theorem iSup_cohomologyGrading (h : IsDGAlgebra 𝒜 d) : ⨆ p : ℤ, h.cohomologyGrading p = ⊤ := by
  have hgrading : (⨆ p : ℤ, h.cohomologyGrading p) =
      Submodule.map h.toCohomology.toLinearMap (⨆ p : ℤ, h.cyclesDeg p) :=
    (Submodule.map_iSup _ _).symm
  rw [hgrading, h.iSup_cyclesDeg, Submodule.map_top, LinearMap.range_eq_top]
  exact h.toCohomology_surjective

/-- The homogeneous cohomology classes of distinct degrees are independent: a homogeneous cycle
whose class is a sum of classes of cycles of other degrees is itself a boundary, because taking
the degree-`p` component of a boundary again gives a boundary. -/
theorem iSupIndep_cohomologyGrading (h : IsDGAlgebra 𝒜 d) : iSupIndep h.cohomologyGrading := by
  intro p
  rw [Submodule.disjoint_def]
  rintro x hx hx'
  obtain ⟨z, hz, rfl⟩ := h.mem_cohomologyGrading.mp hx
  have hother : (⨆ (q : ℤ) (_ : q ≠ p), h.cohomologyGrading q) =
      Submodule.map h.toCohomology.toLinearMap
        (⨆ (q : ℤ) (_ : q ≠ p), h.cyclesDeg q) := by
    simp only [cohomologyGrading, Submodule.map_iSup]
  rw [hother] at hx'
  obtain ⟨w, hw, hwz⟩ := hx'
  have hle : Submodule.map h.cycles.val.toLinearMap (⨆ (q : ℤ) (_ : q ≠ p), h.cyclesDeg q)
      ≤ ⨆ (q : ℤ) (_ : q ≠ p), 𝒜 q := by
    rw [Submodule.map_iSup]
    refine iSup_le fun q => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hq => le_iSup_of_le q (le_iSup_of_le hq (Submodule.map_comap_le _ _))
  have hwp : GradedRing.proj 𝒜 p (w : A) = 0 :=
    proj_eq_zero_of_mem_biSup (hle (Submodule.mem_map_of_mem hw))
  have hzw : ((z - w : h.cycles) : A) ∈ LinearMap.range d :=
    h.mem_boundaries.mp (h.toCohomology_eq_zero_iff.mp
      (by rw [map_sub]; exact sub_eq_zero_of_eq hwz.symm))
  have hzz : GradedRing.proj 𝒜 p (z : A) = (z : A) := by
    rw [GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_same 𝒜 hz
  have hz_boundary : (z : A) ∈ LinearMap.range d := by
    simpa only [Subalgebra.coe_sub, map_sub, hwp, sub_zero, hzz] using h.proj_mem_range hzw p
  exact h.toCohomology_eq_zero_iff.mpr (h.mem_boundaries.mpr hz_boundary)

/-- **The cohomology of a differential graded algebra is a graded algebra.**  Its degree-`p` piece
is the module of degree-`p` cohomology classes. -/
noncomputable instance instGradedAlgebraCohomologyGrading (h : IsDGAlgebra 𝒜 d) :
    GradedAlgebra h.cohomologyGrading :=
  { h.instGradedMonoidCohomologyGrading,
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      h.iSupIndep_cohomologyGrading h.iSup_cohomologyGrading).chooseDecomposition with }

end IsDGAlgebra

section ZeroDifferential

variable (𝒜)

/-- With the zero differential every element is a cycle. -/
@[simp]
theorem cycles_isDGAlgebra_zero : (isDGAlgebra_zero 𝒜).cycles = ⊤ :=
  eq_top_iff.mpr fun _ _ => (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl

/-- With the zero differential the only boundary is zero. -/
@[simp]
theorem boundaries_isDGAlgebra_zero : (isDGAlgebra_zero 𝒜).boundaries = ⊥ :=
  TwoSidedIdeal.ext fun z => by
    rw [IsDGAlgebra.mem_boundaries, TwoSidedIdeal.mem_bot, LinearMap.range_zero,
      Submodule.mem_bot]
    exact ⟨fun hz => Subtype.ext (by simpa using hz), fun hz => by simp [hz]⟩

theorem toCohomology_isDGAlgebra_zero_bijective :
    Function.Bijective (isDGAlgebra_zero 𝒜).toCohomology := by
  refine ⟨fun z w hzw => ?_, (isDGAlgebra_zero 𝒜).toCohomology_surjective⟩
  have hb : z - w ∈ (isDGAlgebra_zero 𝒜).boundaries :=
    (isDGAlgebra_zero 𝒜).toCohomology_eq_zero_iff.mp (by rw [map_sub, hzw, sub_self])
  rwa [boundaries_isDGAlgebra_zero, TwoSidedIdeal.mem_bot, sub_eq_zero] at hb

/-- **A graded algebra with zero differential is its own cohomology.**  Every element is a cycle by
`TauCeti.cycles_isDGAlgebra_zero` and the only boundary is zero, so passing to cohomology changes
nothing.  That this identification is one of *graded* algebras is
`TauCeti.map_algEquivCohomologyOfZero`. -/
noncomputable def algEquivCohomologyOfZero : A ≃ₐ[R] (isDGAlgebra_zero 𝒜).cohomology :=
  (Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (cycles_isDGAlgebra_zero 𝒜).symm)).trans
    (AlgEquiv.ofBijective _ (toCohomology_isDGAlgebra_zero_bijective 𝒜))

@[simp]
theorem algEquivCohomologyOfZero_apply (a : A) :
    algEquivCohomologyOfZero 𝒜 a =
      (isDGAlgebra_zero 𝒜).toCohomology ⟨a, (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl⟩ :=
  (rfl)

/-- The identification of a graded algebra with zero differential with its own cohomology respects
the gradings: it carries the degree-`p` piece of `𝒜` onto the degree-`p` piece of the cohomology. -/
theorem map_algEquivCohomologyOfZero (p : ℤ) :
    (𝒜 p).map (algEquivCohomologyOfZero 𝒜).toLinearMap =
      (isDGAlgebra_zero 𝒜).cohomologyGrading p := by
  ext x
  rw [Submodule.mem_map, IsDGAlgebra.mem_cohomologyGrading]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl⟩, ha, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(z : A), hz, rfl⟩

end ZeroDifferential

end TauCeti
