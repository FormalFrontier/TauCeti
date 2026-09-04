/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient

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
cycles; its underlying ideal is two-sided, so the cohomology algebra uses Mathlib's
`Ideal.Quotient`.

## Main definitions

* `TauCeti.IsDGAlgebra.cycles`: the kernel of the differential, as a subalgebra.
* `TauCeti.IsDGAlgebra.cyclesDeg`: the homogeneous cycles of a fixed degree.
* `TauCeti.IsDGAlgebra.boundaries`: the image of the differential, as a two-sided ideal of the
  cycles.
* `TauCeti.IsDGAlgebra.Cohomology`: the cohomology algebra, implemented by Mathlib's quotient of
  the cycles by the underlying ideal of boundaries.
* `TauCeti.IsDGAlgebra.cohomologyGrading`: the grading of the cohomology algebra by the classes of
  homogeneous cycles.
* `TauCeti.algEquivCohomologyOfZero`: a graded algebra with zero differential is its own
  cohomology.

## Main results

* `TauCeti.IsDGAlgebra.iSup_cyclesDeg_eq_top`: every cycle is a sum of homogeneous ones.
* `TauCeti.IsDGAlgebra.instGradedAlgebraCohomologyGrading`: **the cohomology of a differential
  graded algebra is a graded algebra.**
* `TauCeti.map_algEquivCohomologyOfZero_eq_cohomologyGrading`: the identification of a graded
  algebra carrying the zero differential with its own cohomology matches the two gradings
  degreewise.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 1, item "DG algebras, categories,
modules, and bimodules", specifically its first request for "cycles, boundaries, and the induced
graded cohomology algebra".  The induced grading reuses
`TauCeti.GradedAlgebra.gradedAlgebraGradeQuot` from
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient`, whose construction follows Mathlib PR
[#36501](https://github.com/leanprover-community/mathlib4/pull/36501) by Antoine Chambert-Loir.

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
def cycles (h : IsDGAlgebra 𝒜 d) : Subalgebra R A :=
  (LinearMap.ker d).toSubalgebra h.map_one_eq_zero
    fun _ _ ha hb => h.map_mul_eq_zero_of_map_eq_zero ha hb

@[simp]
lemma mem_cycles (h : IsDGAlgebra 𝒜 d) {a : A} : a ∈ h.cycles ↔ d a = 0 := Iff.rfl

/-- The differential of every element is a cycle, by the square-zero axiom. -/
theorem map_mem_cycles (h : IsDGAlgebra 𝒜 d) (a : A) : d a ∈ h.cycles :=
  h.sq_zero a

/-- The degree-`p` homogeneous cycles, as a submodule of the algebra of cycles. -/
def cyclesDeg (h : IsDGAlgebra 𝒜 d) (p : ℤ) : Submodule R h.cycles :=
  (𝒜 p).comap h.cycles.val.toLinearMap

@[simp]
lemma mem_cyclesDeg (h : IsDGAlgebra 𝒜 d) {p : ℤ} {z : h.cycles} :
    z ∈ h.cyclesDeg p ↔ (z : A) ∈ 𝒜 p := Iff.rfl

/-- Every cycle is a sum of homogeneous cycles: the homogeneous components of a cycle are cycles,
and they add up to it. -/
theorem iSup_cyclesDeg_eq_top (h : IsDGAlgebra 𝒜 d) : ⨆ p : ℤ, h.cyclesDeg p = ⊤ := by
  classical
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : d (z : A) = 0 := h.mem_cycles.mp z.2
  set s := (decompose 𝒜 (z : A)).support
  have hmem : ∀ p : ℤ, (decompose 𝒜 (z : A) p : A) ∈ h.cycles :=
    fun p => h.mem_cycles.mpr (h.map_proj_eq_zero hz p)
  have hsum : z = ∑ p ∈ s, (⟨(decompose 𝒜 (z : A) p : A), hmem p⟩ : h.cycles) := by
    refine Subtype.ext ?_
    simpa [AddSubmonoidClass.coe_finsetSum] using
      (DirectSum.sum_support_decompose 𝒜 (z : A)).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.mem_iSup_of_mem p (SetLike.coe_mem (decompose 𝒜 (z : A) p))

/-- The homogeneous cycle spaces are independent, as subspaces of the independent grading of the
ambient algebra. -/
theorem iSupIndep_cyclesDeg (h : IsDGAlgebra 𝒜 d) : iSupIndep h.cyclesDeg := by
  intro p
  rw [Submodule.disjoint_def]
  rintro z hz hz'
  have hle : Submodule.map h.cycles.val.toLinearMap
      (⨆ (q : ℤ) (_ : q ≠ p), h.cyclesDeg q) ≤ ⨆ (q : ℤ) (_ : q ≠ p), 𝒜 q := by
    rw [Submodule.map_iSup]
    refine iSup_le fun q => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hq => le_iSup_of_le q (le_iSup_of_le hq (Submodule.map_comap_le _ _))
  have hz'prop : (z : A) ∈ ⨆ (q : ℤ) (_ : q ≠ p), 𝒜 q :=
    hle (Submodule.mem_map_of_mem hz')
  have hambient := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep p
  rw [Submodule.disjoint_def] at hambient
  have hzprop : (z : A) ∈ 𝒜 p := h.mem_cyclesDeg.mp hz
  have hz0 : (z : A) ∈ (⊥ : Submodule R A) := hambient (z : A) hzprop hz'prop
  apply Subtype.ext
  simpa only [Subalgebra.coe_zero, Submodule.mem_bot] using hz0

/-- The homogeneous cycle spaces form an internal direct sum. -/
theorem isInternal_cyclesDeg (h : IsDGAlgebra 𝒜 d) : DirectSum.IsInternal h.cyclesDeg :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h.iSupIndep_cyclesDeg
    h.iSup_cyclesDeg_eq_top

/-- The cycles inherit the grading of the ambient differential graded algebra. -/
noncomputable instance instGradedAlgebraCyclesDeg (h : IsDGAlgebra 𝒜 d) :
    GradedAlgebra h.cyclesDeg :=
  { h.isInternal_cyclesDeg.chooseDecomposition with
    one_mem := by
      simpa only [mem_cyclesDeg, Subalgebra.coe_one] using SetLike.one_mem_graded 𝒜
    mul_mem := fun _ _ _ _ hx hy => by
      rw [h.mem_cyclesDeg] at hx hy ⊢
      simpa only [Subalgebra.coe_mul] using SetLike.mul_mem_graded hx hy }

/-- The **boundaries** of a differential graded algebra: the image of the differential, viewed
inside the cycles.  It is a two-sided ideal there: a cycle times a boundary is a boundary by the
Leibniz rule read backwards, and a boundary times a cycle is the differential of the same
product. -/
def boundaries (h : IsDGAlgebra 𝒜 d) : TwoSidedIdeal h.cycles :=
  TwoSidedIdeal.mk' {z : h.cycles | (z : A) ∈ LinearMap.range d}
    (by
      simpa only [Set.mem_ofPred_eq, Subalgebra.coe_zero] using
        Submodule.zero_mem (LinearMap.range d))
    (fun {x y} hx hy => by
      simpa only [Set.mem_ofPred_eq, Subalgebra.coe_add] using
        Submodule.add_mem (LinearMap.range d) hx hy)
    (fun {x} hx => by
      simpa only [Set.mem_ofPred_eq, Subalgebra.coe_neg] using
        Submodule.neg_mem (LinearMap.range d) hx)
    (fun {x y} hy => by
      obtain ⟨b, hb⟩ := hy
      simpa only [Set.mem_ofPred_eq, Subalgebra.coe_mul, ← hb] using
        h.mul_map_mem_range_of_map_left_eq_zero (h.mem_cycles.mp x.2) b)
    (fun {x y} hx => by
      obtain ⟨a, ha⟩ := hx
      simp only [Set.mem_ofPred_eq, Subalgebra.coe_mul]
      exact ⟨a * (y : A), by
        rw [h.leibniz_of_map_right_eq_zero a (h.mem_cycles.mp y.2), ha]⟩)

@[simp]
lemma mem_boundaries (h : IsDGAlgebra 𝒜 d) {z : h.cycles} :
    z ∈ h.boundaries ↔ (z : A) ∈ LinearMap.range d :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

/-- The cycle represented by a differential is a boundary. -/
theorem map_mem_boundaries (h : IsDGAlgebra 𝒜 d) (a : A) :
    (⟨d a, h.map_mem_cycles a⟩ : h.cycles) ∈ h.boundaries :=
  h.mem_boundaries.mpr ⟨a, rfl⟩

/-- The **cohomology algebra** `H(A)` of a differential graded algebra: the cycles modulo the
underlying ideal of boundaries. -/
abbrev Cohomology (h : IsDGAlgebra 𝒜 d) := h.cycles ⧸ h.boundaries.asIdeal

/-- Under the inherited grading of the cycles, homogeneous projection agrees with homogeneous
projection in the ambient algebra. -/
@[simp]
theorem coe_decompose_cyclesDeg (h : IsDGAlgebra 𝒜 d) (p : ℤ) (z : h.cycles) :
    ((decompose h.cyclesDeg z p : h.cycles) : A) = GradedRing.proj 𝒜 p (z : A) := by
  induction z using DirectSum.Decomposition.inductionOn h.cyclesDeg with
  | zero => simp [GradedRing.proj_apply]
  | @homogeneous q z =>
    have hz : (z : h.cycles) ∈ h.cyclesDeg q := z.2
    have hzA : ((z : h.cycles) : A) ∈ 𝒜 q := h.mem_cyclesDeg.mp hz
    by_cases hpq : p = q
    · subst hpq
      rw [DirectSum.decompose_of_mem_same h.cyclesDeg hz, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜 hzA]
    · rw [DirectSum.decompose_of_mem_ne h.cyclesDeg hz (Ne.symm hpq),
        ZeroMemClass.coe_zero, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hzA (Ne.symm hpq)]
  | add x y hx hy => simp [hx, hy]

/-- The boundary ideal is homogeneous in the inherited grading of the cycles. -/
theorem isHomogeneous_boundaries (h : IsDGAlgebra 𝒜 d) :
    h.boundaries.asIdeal.IsHomogeneous h.cyclesDeg := by
  intro p z hz
  rw [TwoSidedIdeal.mem_asIdeal, h.mem_boundaries] at hz ⊢
  rw [h.coe_decompose_cyclesDeg]
  exact h.proj_mem_range hz p

/-- The grading of the cohomology algebra: the degree-`p` piece consists of the classes of the
homogeneous cycles of degree `p`. -/
noncomputable abbrev cohomologyGrading (h : IsDGAlgebra 𝒜 d) (p : ℤ) :
    Submodule R h.Cohomology :=
  GradedAlgebra.gradeQuot h.cyclesDeg h.boundaries.asIdeal p

@[simp]
lemma mem_cohomologyGrading (h : IsDGAlgebra 𝒜 d) {p : ℤ} {x : h.Cohomology} :
    x ∈ h.cohomologyGrading p ↔
      ∃ z : h.cycles, (z : A) ∈ 𝒜 p ∧ Ideal.Quotient.mk h.boundaries.asIdeal z = x :=
  (GradedAlgebra.mem_gradeQuot_iff h.cyclesDeg h.boundaries.asIdeal).trans (by
    simp only [h.mem_cyclesDeg])

/-- A cohomology class vanishes exactly when the cycle representing it is a boundary: the kernel
of the quotient map onto the cohomology algebra is the ideal of boundaries. -/
theorem quotientMk_eq_zero_iff (h : IsDGAlgebra 𝒜 d) {z : h.cycles} :
    Ideal.Quotient.mk h.boundaries.asIdeal z = 0 ↔ z ∈ h.boundaries :=
  Ideal.Quotient.eq_zero_iff_mem.trans TwoSidedIdeal.mem_asIdeal

/-- The class of a differential vanishes in cohomology. -/
@[simp]
theorem quotientMk_map_eq_zero (h : IsDGAlgebra 𝒜 d) (a : A) :
    Ideal.Quotient.mk h.boundaries.asIdeal
        (⟨d a, h.map_mem_cycles a⟩ : h.cycles) = 0 :=
  h.quotientMk_eq_zero_iff.mpr (h.map_mem_boundaries a)

/-- **The cohomology of a differential graded algebra is a graded algebra.**  This is the generic
grading on a quotient by a homogeneous ideal. -/
noncomputable instance instGradedAlgebraCohomologyGrading (h : IsDGAlgebra 𝒜 d) :
    GradedAlgebra h.cohomologyGrading :=
  GradedAlgebra.gradedAlgebraGradeQuot h.cyclesDeg h.boundaries.asIdeal
    h.isHomogeneous_boundaries

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

/-- **A graded algebra with zero differential is its own cohomology.**  Every element is a cycle by
`TauCeti.cycles_isDGAlgebra_zero` and the only boundary is zero, so passing to cohomology changes
nothing.  That this identification is one of *graded* algebras is
`TauCeti.map_algEquivCohomologyOfZero_eq_cohomologyGrading`. -/
noncomputable def algEquivCohomologyOfZero : A ≃ₐ[R] (isDGAlgebra_zero 𝒜).Cohomology :=
  (Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (cycles_isDGAlgebra_zero 𝒜).symm)).trans
    ((AlgEquiv.quotientBot R _).symm.trans
      (Ideal.quotientEquivAlgOfEq R (by
        rw [boundaries_isDGAlgebra_zero, TwoSidedIdeal.bot_asIdeal])))

@[simp]
theorem algEquivCohomologyOfZero_apply (a : A) :
    algEquivCohomologyOfZero 𝒜 a =
      Ideal.Quotient.mk (isDGAlgebra_zero 𝒜).boundaries.asIdeal
        ⟨a, (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl⟩ := by
  let z : (isDGAlgebra_zero 𝒜).cycles :=
    ⟨a, (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl⟩
  have htop : Subalgebra.topEquiv.symm a = (⟨a, trivial⟩ : (⊤ : Subalgebra R A)) := by
    apply Subtype.ext
    simpa only [Subalgebra.topEquiv_apply] using Subalgebra.topEquiv.apply_symm_apply a
  have hcycle :
      (Subalgebra.topEquiv.symm.trans
          (Subalgebra.equivOfEq _ _ (cycles_isDGAlgebra_zero 𝒜).symm)) a = z := by
    rw [AlgEquiv.trans_apply, htop, Subalgebra.equivOfEq_apply]
  have hbot :
      (AlgEquiv.quotientBot R (isDGAlgebra_zero 𝒜).cycles).symm z =
        Ideal.Quotient.mk ⊥ z :=
    RingEquiv.quotientBot_symm_mk z
  rw [algEquivCohomologyOfZero, AlgEquiv.trans_apply, hcycle, AlgEquiv.trans_apply,
    hbot, Ideal.quotientEquivAlgOfEq_mk]

/-- The identification of a graded algebra with zero differential with its own cohomology respects
the gradings: it carries the degree-`p` piece of `𝒜` onto the degree-`p` piece of the cohomology. -/
theorem map_algEquivCohomologyOfZero_eq_cohomologyGrading (p : ℤ) :
    (𝒜 p).map (algEquivCohomologyOfZero 𝒜).toLinearMap =
      (isDGAlgebra_zero 𝒜).cohomologyGrading p := by
  ext x
  rw [Submodule.mem_map, IsDGAlgebra.mem_cohomologyGrading]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, (isDGAlgebra_zero 𝒜).mem_cycles.mpr rfl⟩, ha, ?_⟩
    rw [AlgEquiv.toLinearMap_apply, algEquivCohomologyOfZero_apply]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : A), hz, ?_⟩
    rw [AlgEquiv.toLinearMap_apply, algEquivCohomologyOfZero_apply]

end ZeroDifferential

end TauCeti
