/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.LinearAlgebra.UnitaryGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Topology.Circle.Basic

/-!
# `SU(2)` and its maximal torus

`SU(2)` is `Matrix.specialUnitaryGroup (Fin 2) ℂ`, the compact group that grounds the compact-group
representation theory of the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
Its compactness and topological group structure come from
`TauCeti/Topology/Algebra/UnitaryGroup.lean`, where they are proved for every special unitary
matrix group; Hausdorffness is inherited from the ambient matrix topology, `SU(2)` carrying the
subtype topology.

This file builds the **maximal torus** `T ⊂ SU(2)`, the diagonal circle subgroup

`T = { diag (z, z⁻¹) : |z| = 1 }`,

and identifies it with Mathlib's `Circle` as a topological group. Three facts pin it down:

* `TauCeti.SU2.mem_torus_iff`: an element of `SU(2)` lies in `T` exactly when it is diagonal, so
  `T` really is *the* diagonal subgroup and not merely some circle inside `SU(2)`;
* `TauCeti.SU2.centralizer_torus`: `T` is its own centralizer, whence
  `TauCeti.SU2.eq_torus_of_isMulCommutative`: `T` is a maximal abelian subgroup, which is what earns
  it the name "maximal torus";
* `TauCeti.SU2.mem_torus_iff_exists_torusExp`: every element of `T` is `diag (e^{iθ}, e^{-iθ})`,
  the parametrisation the Weyl integration and character formulas for `SU(2)` are stated in.

The centralizer computation is run at a *single* well-chosen torus element: already
`TauCeti.SU2.centralizer_torusHom` says that `diag (z, z⁻¹)` with `z² ≠ 1` has centralizer exactly
`T`. Together with `TauCeti.SU2.eq_or_eq_inv_of_conj_torusHom`, which says that conjugating a torus
element back into `T` can only return it or its inverse, this is the rigidity that the Weyl group
of `SU(2)` is computed from in `TauCeti/RepresentationTheory/SU2/Weyl/Basic.lean`.

It also records the structural identity `TauCeti.SU2.coe_add_star`: an element of `SU(2)` and its
conjugate transpose add up to `(tr g) • 1`, so the Hermitian part of an element of `SU(2)` is a
scalar matrix; tracing it shows the trace is real (`TauCeti.SU2.isSelfAdjoint_trace`). Conjugate
elements have the same trace (`TauCeti.SU2.trace_eq_of_isConj`). On the torus the trace is
`TauCeti.SU2.trace_torusMatrix`: `tr (diag (z, z⁻¹)) = z + z⁻¹`, in the angle parametrisation
`TauCeti.SU2.trace_torusExp`: `tr (diag (e^{iθ}, e^{-iθ})) = 2 cos θ`, and
`TauCeti.SU2.eq_or_eq_inv_of_trace_torusMatrix_eq` says that this value determines `z` up to
inversion. That the trace is a *complete* conjugacy invariant is proved in
`TauCeti/RepresentationTheory/SU2/ConjugacyClasses.lean`.

## Main definitions

* `TauCeti.SU2`: the group `SU(2)`.
* `TauCeti.SU2.torusHom`: the circle parametrisation `z ↦ diag (z, z⁻¹)` of the maximal torus.
* `TauCeti.SU2.torus`: the maximal torus of `SU(2)`, the range of `torusHom`.
* `TauCeti.SU2.torusContinuousMulEquiv`: the isomorphism of topological groups `Circle ≃ₜ* T`.
* `TauCeti.SU2.torusExp`: the torus element `diag (e^{iθ}, e^{-iθ})`.
-/

public section

namespace TauCeti

/-- `SU(2)`, the special unitary group of `2 × 2` complex matrices. It is a compact Hausdorff
topological group: the compactness and topological group instances come from
`TauCeti/Topology/Algebra/UnitaryGroup.lean`, and Hausdorffness from the ambient matrix
topology. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

namespace SU2

/-- An element of `SU(2)` and its conjugate transpose add up to `(tr g) • 1`: the conjugate
transpose of `g` is its adjugate, and a `2 × 2` matrix plus its adjugate is the trace times the
identity. Equivalently, the Hermitian part of `g` is a scalar matrix. -/
theorem coe_add_star (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) + star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) • 1 := by
  rw [Matrix.specialUnitaryGroup.star_eq_adjugate, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- **The trace of an element of `SU(2)` is real.** Taking traces in
`TauCeti.SU2.coe_add_star`, `g + g* = (tr g) • 1`, gives `tr g + conj (tr g)` on the left and
`2 tr g` on the right. -/
theorem isSelfAdjoint_trace (g : SU2) :
    IsSelfAdjoint (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h := congrArg Matrix.trace (coe_add_star g)
  simp only [Matrix.trace_add, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat] at h
  rw [isSelfAdjoint_iff]
  linear_combination h

/-- Conjugate elements of `SU(2)` have the same trace. -/
theorem trace_eq_of_isConj {g h : SU2} (hgh : IsConj g h) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨u, rfl⟩ := isConj_iff.mp hgh
  -- `u` maps to a unit of the matrix ring, so this is `Matrix.trace_units_conj`.
  simpa using
    (Matrix.trace_units_conj (Units.map (Submonoid.subtype _) (toUnits u))
      (g : Matrix (Fin 2) (Fin 2) ℂ)).symm

/-! ### The diagonal matrices `diag (z, z⁻¹)` -/

/-- The diagonal matrix `diag (z, z⁻¹)` attached to a point `z` of the unit circle. -/
noncomputable def torusMatrix (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(z : ℂ), ((z : ℂ))⁻¹]

@[simp]
theorem torusMatrix_apply_zero_zero (z : Circle) : torusMatrix z 0 0 = (z : ℂ) := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_one_one (z : Circle) : torusMatrix z 1 1 = ((z : ℂ))⁻¹ := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_zero_one (z : Circle) : torusMatrix z 0 1 = 0 := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_one_zero (z : Circle) : torusMatrix z 1 0 = 0 := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_one : torusMatrix 1 = 1 := by
  rw [torusMatrix, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[simp]
theorem torusMatrix_mul (z w : Circle) :
    torusMatrix (z * w) = torusMatrix z * torusMatrix w := by
  rw [torusMatrix, torusMatrix, torusMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

@[simp]
theorem star_torusMatrix (z : Circle) : star (torusMatrix z) = torusMatrix z⁻¹ := by
  have hz : star (z : ℂ) = ((z : ℂ))⁻¹ := by simpa using (Circle.coe_inv_eq_conj z).symm
  rw [Matrix.star_eq_conjTranspose, torusMatrix, torusMatrix, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  fin_cases i <;> simp [hz]

/-- The trace of the torus matrix `diag (z, z⁻¹)` is `z + z⁻¹`. -/
@[simp]
theorem trace_torusMatrix (z : Circle) :
    (torusMatrix z).trace = (z : ℂ) + ((z : ℂ))⁻¹ := by
  rw [Matrix.trace_fin_two, torusMatrix_apply_zero_zero, torusMatrix_apply_one_one]

@[simp]
theorem det_torusMatrix (z : Circle) : (torusMatrix z).det = 1 := by
  rw [torusMatrix, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem torusMatrix_mem (z : Circle) :
    torusMatrix z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, det_torusMatrix z⟩
  rw [Matrix.mem_unitaryGroup_iff, star_torusMatrix, ← torusMatrix_mul, mul_inv_cancel,
    torusMatrix_one]

theorem continuous_torusMatrix : Continuous torusMatrix := by
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  have hinv : Continuous fun z : Circle => ((z : ℂ))⁻¹ := hcoe.inv₀ fun z => z.coe_ne_zero
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · exact hcoe
  · exact hinv

/-! ### The maximal torus -/

/-- The circle parametrisation `z ↦ diag (z, z⁻¹)` of the maximal torus of `SU(2)`. -/
noncomputable def torusHom : Circle →* SU2 where
  toFun z := ⟨torusMatrix z, torusMatrix_mem z⟩
  map_one' := Subtype.ext torusMatrix_one
  map_mul' z w := Subtype.ext (torusMatrix_mul z w)

-- `(rfl)`, not `rfl`: the parenthesised form proves the accessor without requiring `torusHom` to
-- be `@[expose]`d, so the definition stays opaque downstream. Likewise below.
@[simp]
theorem coe_torusHom (z : Circle) : (torusHom z : Matrix (Fin 2) (Fin 2) ℂ) = torusMatrix z := (rfl)

theorem continuous_torusHom : Continuous torusHom :=
  continuous_induced_rng.mpr continuous_torusMatrix

/-- The **maximal torus** of `SU(2)`: the diagonal circle subgroup. -/
noncomputable def torus : Subgroup SU2 := torusHom.range

theorem torusHom_mem_torus (z : Circle) : torusHom z ∈ torus := ⟨z, rfl⟩

/-- An element of `SU(2)` lies in the maximal torus exactly when it is `diag (z, z⁻¹)` for a point
`z` of the unit circle. This is the definition of `TauCeti.SU2.torus` as a range, restated as the
membership lemma that puts a hand on the circle parameter of a torus element. -/
theorem mem_torus_iff_exists_torusHom {g : SU2} : g ∈ torus ↔ ∃ z : Circle, torusHom z = g :=
  torusHom.mem_range

/-- An element of `SU(2)` lies in the maximal torus exactly when it is a diagonal matrix: unitarity
makes the `(0, 0)` entry a point of the unit circle, and the determinant condition then forces the
`(1, 1)` entry to be its inverse. -/
@[simp]
theorem mem_torus_iff {g : SU2} :
    g ∈ torus ↔ Matrix.IsDiag (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [coe_torusHom, torusMatrix]
    exact Matrix.isDiag_diagonal _
  · intro hdiag
    have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := hdiag (by decide)
    have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := hdiag (by decide)
    have hunit : (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
        = 1 := by
      have h := congrFun (congrFun hunit 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two] at h
      simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
        h01] using h
    have hnorm : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
      have h := congrArg norm hmul
      rw [norm_mul, norm_star, norm_one] at h
      nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)]
    have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
      rw [Matrix.det_fin_two, h01] at h
      simpa using h
    have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    obtain ⟨z, hz⟩ : ∃ z : Circle, (z : ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
      ⟨⟨_, mem_sphere_zero_iff_norm.mpr hnorm⟩, rfl⟩
    refine ⟨z, Subtype.ext ?_⟩
    rw [coe_torusHom, torusMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, h01, h10, h11]

theorem torusHom_injective : Function.Injective torusHom := fun z w h => by
  have h00 := congrArg (fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  exact Circle.ext (by simpa using h00)

/-- The maximal torus of `SU(2)` *is* the circle group, as a topological group. -/
noncomputable def torusContinuousMulEquiv : Circle ≃ₜ* torus where
  __ := MonoidHom.ofInjective torusHom_injective
  continuous_toFun := continuous_torusHom.subtype_mk _
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2
      (f := (MonoidHom.ofInjective torusHom_injective).toEquiv)
      (continuous_torusHom.subtype_mk _)).continuous_invFun

@[simp]
theorem torusContinuousMulEquiv_apply (z : Circle) :
    (torusContinuousMulEquiv z : SU2) = torusHom z := (rfl)

/-- The inverse of `torusContinuousMulEquiv` reads off the circle parameter of an element of the
maximal torus: it is the point of `Circle` that `torusHom` sends back to that element. -/
@[simp]
theorem torusHom_torusContinuousMulEquiv_symm (g : torus) :
    torusHom (torusContinuousMulEquiv.symm g) = (g : SU2) :=
  (torusContinuousMulEquiv_apply _).symm.trans
    (congrArg Subtype.val (torusContinuousMulEquiv.apply_symm_apply g))

instance : IsMulCommutative torus :=
  .of_setLike_mul_comm <| by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

/-! ### Maximality -/

/-- The imaginary unit as a point of the unit circle. The torus element it names,
`diag (i, -i)`, is the one the centralizer of the maximal torus is computed at: it is the
simplest `z` with `z² ≠ 1`, which is exactly what `TauCeti.SU2.centralizer_torusHom` asks for. It
is a proof witness, not `SU(2)` API, so it stays local to this file. -/
private def circleI : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩

private theorem coe_circleI : (circleI : ℂ) = Complex.I := (rfl)

private theorem circleI_sq_ne_one : (circleI : ℂ) ^ 2 ≠ 1 := by
  rw [coe_circleI, Complex.I_sq]
  norm_num

/-- **An element of `SU(2)` commuting with a single torus element `diag (z, z⁻¹)` with `z² ≠ 1`
already lies in the maximal torus.** Reading off the off-diagonal entries of
`diag (z, z⁻¹) g = g diag (z, z⁻¹)` gives `g₀₁ (z - z⁻¹) = 0` and `g₁₀ (z⁻¹ - z) = 0`, and
`z² ≠ 1` gives `z ≠ z⁻¹` (`TauCeti.circle_sub_inv_ne_zero`). -/
theorem mem_torus_of_commute_torusHom {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) {g : SU2}
    (h : torusHom z * g = g * torusHom z) : g ∈ torus := by
  have hsub : (z : ℂ) - ((z : ℂ))⁻¹ ≠ 0 := circle_sub_inv_ne_zero hz
  have hmat : torusMatrix z * (g : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * torusMatrix z := by
    have hval := congrArg Subtype.val h
    simpa only [Submonoid.coe_mul, coe_torusHom] using hval
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    have hentry := congrFun (congrFun hmat 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, torusMatrix_apply_zero_zero,
      torusMatrix_apply_zero_one, torusMatrix_apply_one_one, zero_mul, mul_zero, add_zero,
      zero_add] at hentry
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * ((z : ℂ) - ((z : ℂ))⁻¹) = 0 := by
      linear_combination hentry
    exact (mul_eq_zero.mp hmul).resolve_right hsub
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    have hentry := congrFun (congrFun hmat 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, torusMatrix_apply_zero_zero,
      torusMatrix_apply_one_one, torusMatrix_apply_one_zero, zero_mul, mul_zero, add_zero,
      zero_add] at hentry
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * ((z : ℂ) - ((z : ℂ))⁻¹) = 0 := by
      linear_combination -hentry
    exact (mul_eq_zero.mp hmul).resolve_right hsub
  refine mem_torus_iff.mpr fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp_all

/-- **A single torus element `diag (z, z⁻¹)` with `z² ≠ 1` already has centralizer the maximal
torus.** This sharpens `TauCeti.SU2.centralizer_torus`, which centralizes the whole of `T` rather
than one well-chosen element of it. -/
theorem centralizer_torusHom {z : Circle} (hz : (z : ℂ) ^ 2 ≠ 1) :
    Subgroup.centralizer ({torusHom z} : Set SU2) = torus := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · exact mem_torus_of_commute_torusHom hz (Subgroup.mem_centralizer_iff.mp hg _ rfl)
  · obtain ⟨u, rfl⟩ := hg
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    rw [← map_mul, ← map_mul, mul_comm]

/-- **The maximal torus contains a regular element**: some single element `diag (z, z⁻¹)` of `T`
has centralizer exactly `T`. This is `TauCeti.SU2.centralizer_torusHom` at a point of the circle
satisfying its rigidity hypothesis `z² ≠ 1`; the particular witness, `z = i`, is a proof detail of
this file, and a downstream computation that must detect `T` by a single element needs only the
existence. -/
theorem exists_centralizer_torusHom_eq_torus :
    ∃ z : Circle, Subgroup.centralizer ({torusHom z} : Set SU2) = torus :=
  ⟨circleI, centralizer_torusHom circleI_sq_ne_one⟩

/-- The maximal torus is its own centralizer in `SU(2)`. -/
theorem centralizer_torus : Subgroup.centralizer (torus : Set SU2) = torus := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · -- `g` commutes with `diag (i, -i)`, whose centralizer is already the torus.
    exact mem_torus_of_commute_torusHom circleI_sq_ne_one
      (Subgroup.mem_centralizer_iff.mp hg (torusHom circleI) (torusHom_mem_torus circleI))
  · rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := hg
    rw [← map_mul, ← map_mul, mul_comm]

/-- The maximal torus is a maximal abelian subgroup of `SU(2)`: a commutative subgroup containing
it is equal to it. -/
theorem eq_torus_of_isMulCommutative {H : Subgroup SU2} [IsMulCommutative H] (hH : torus ≤ H) :
    H = torus := by
  refine le_antisymm (fun g hg => ?_) hH
  rw [← centralizer_torus, Subgroup.mem_centralizer_iff]
  intro h hh
  exact setLike_mul_comm (hH hh) hg

/-! ### Conjugating a torus element back into the torus -/

/-- **The trace separates the torus elements up to inversion:** `z` and `z⁻¹` are the only two
points of the circle at which `diag (z, z⁻¹)` has a given trace, being the two roots of
`X² - (z + z⁻¹) X + 1`. -/
theorem eq_or_eq_inv_of_trace_torusMatrix_eq {z w : Circle}
    (h : (torusMatrix w).trace = (torusMatrix z).trace) : w = z ∨ w = z⁻¹ := by
  rw [trace_torusMatrix, trace_torusMatrix] at h
  have hfac : ((w : ℂ) - (z : ℂ)) * ((w : ℂ) - ((z : ℂ))⁻¹) = 0 := by
    have hw : (w : ℂ) * ((w : ℂ))⁻¹ = 1 := mul_inv_cancel₀ w.coe_ne_zero
    have hzz : (z : ℂ) * ((z : ℂ))⁻¹ = 1 := mul_inv_cancel₀ z.coe_ne_zero
    linear_combination (w : ℂ) * h - hw + hzz
  rcases mul_eq_zero.mp hfac with hc | hc
  · exact Or.inl (Circle.ext (sub_eq_zero.mp hc))
  · exact Or.inr (Circle.ext (by rw [Circle.coe_inv]; exact sub_eq_zero.mp hc))

/-- **Conjugating a torus element back into the maximal torus returns it or its inverse.**
Conjugation preserves the trace (`TauCeti.SU2.trace_eq_of_isConj`), and the trace separates torus
elements up to inversion (`TauCeti.SU2.eq_or_eq_inv_of_trace_torusMatrix_eq`). -/
theorem eq_or_eq_inv_of_conj_torusHom {z w : Circle} {g : SU2}
    (h : g * torusHom z * g⁻¹ = torusHom w) : w = z ∨ w = z⁻¹ :=
  eq_or_eq_inv_of_trace_torusMatrix_eq
    (by simpa only [coe_torusHom] using (trace_eq_of_isConj (isConj_iff.mpr ⟨g, h⟩)).symm)

/-! ### The angle parametrisation -/

/-- The torus element `diag (e^{iθ}, e^{-iθ})` of `SU(2)`. -/
noncomputable def torusExp (θ : ℝ) : SU2 := torusHom (Circle.exp θ)

/-- Unfolding lemma for `TauCeti.SU2.torusExp`: it is `torusHom (Circle.exp θ)`. Since `torusExp`
is not `@[expose]`d, this is how lemmas about `torusHom` are brought to bear on it. -/
theorem torusExp_def (θ : ℝ) : torusExp θ = torusHom (Circle.exp θ) := (rfl)

@[simp]
theorem coe_torusExp (θ : ℝ) :
    (torusExp θ : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal ![Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))] := by
  rw [torusExp, coe_torusHom, torusMatrix]
  congr 1
  ext i
  fin_cases i <;> simp [← Complex.exp_neg]

/-- The trace of the torus element `diag (e^{iθ}, e^{-iθ})` is `2 cos θ`. This is not a `simp`
lemma: `TauCeti.SU2.coe_torusExp` already rewrites the underlying matrix to a diagonal one, so its
left-hand side is not in simp-normal form. -/
theorem trace_torusExp (θ : ℝ) :
    Matrix.trace ((torusExp θ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 2 * (Real.cos θ : ℂ) := by
  -- `TauCeti.SU2.coe_torusExp` reduces the trace to `e^{iθ} + e^{-iθ}`, which is `Complex.two_cos`.
  simp [Complex.two_cos]

theorem torusExp_mem_torus (θ : ℝ) : torusExp θ ∈ torus := torusHom_mem_torus _

@[simp]
theorem torusExp_add (θ φ : ℝ) : torusExp (θ + φ) = torusExp θ * torusExp φ := by
  rw [torusExp, torusExp, torusExp, Circle.exp_add, map_mul]

@[simp]
theorem torusExp_zero : torusExp 0 = 1 := by rw [torusExp, Circle.exp_zero, map_one]

@[simp]
theorem torusExp_neg (θ : ℝ) : torusExp (-θ) = (torusExp θ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← torusExp_add, neg_add_cancel, torusExp_zero])

theorem continuous_torusExp : Continuous torusExp :=
  (continuous_torusHom.comp Circle.exp.continuous).congr fun θ => by
    rw [Function.comp_apply, torusExp]

/-- Every element of the maximal torus is `diag (e^{iθ}, e^{-iθ})` for some angle `θ`. -/
theorem mem_torus_iff_exists_torusExp {g : SU2} : g ∈ torus ↔ ∃ θ : ℝ, g = torusExp θ := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact torusExp_mem_torus θ

end SU2

end TauCeti
