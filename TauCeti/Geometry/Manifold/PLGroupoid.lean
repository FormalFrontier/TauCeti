/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Topology.PL.Map

/-!
# The PL structure groupoid

Mathlib builds a manifold out of a `StructureGroupoid` on the model space: `contDiffGroupoid n I`
for smooth manifolds, `continuousGroupoid H` for topological ones. Between the two sits the
piecewise-linear structure, and Mathlib has nothing for it. This file supplies it, in the same
shape as `contDiffGroupoid`: a `Pregroupoid` whose property is "PL when read in the model through
`I`", and the `StructureGroupoid` it generates.

Given a model with corners `I : ModelWithCorners ℝ E H`, a map `f : H → H` is declared PL on
`s : Set H` when `I ∘ f ∘ I.symm` is piecewise linear (`TauCeti.IsPLOn`) on
`I.symm ⁻¹' s ∩ range I`. Reading the property in the model this way — exactly as
`contDiffPregroupoid` does — is what makes the definition apply verbatim to the half-space and
quadrant models, so PL manifolds with boundary and with corners come out of the same definition as
boundaryless ones, with no separate half-space predicate.

A *PL manifold* is then a charted space `M` over `H` with `HasGroupoid M (plGroupoid I)`. No new
structure is introduced for it, matching Mathlib's treatment of `IsManifold`.

## Main definitions

* `TauCeti.plPregroupoid`: the pregroupoid of maps of `H` that are PL read in the model.
* `TauCeti.plGroupoid`: the structure groupoid of PL open partial homeomorphisms of `H`.

## Main results

* `TauCeti.plGroupoid_le_contDiffGroupoid_zero`: the forgetful inclusion "PL implies Top". Its
  mathematical content is that a PL map is continuous (`TauCeti.IsPLOn.continuousOn`).
* `TauCeti.ofSet_mem_plGroupoid` and the `ClosedUnderRestriction (plGroupoid I)` instance: the
  identity of an open set is PL, so the groupoid is closed under restriction, as every structure
  groupoid used to define manifolds must be.

There is deliberately no inclusion in the other direction against `contDiffGroupoid`: a smooth
transition map is not literally piecewise affine, and the comparison between the smooth and the PL
structures is the Whitehead smoothing theory, not a containment of groupoids.

This is the structure-group track of layer 1 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`).
-/

public section

open Set

open scoped Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)

/-- Reading a map of `H` in the model through `I` turns it into a map between subsets of `E`;
the identity `I ∘ I.symm` read this way is the identity of `range I`, and is therefore PL. This is
the workhorse behind both the identity axiom of `TauCeti.plPregroupoid` and the fact that
`TauCeti.plGroupoid` is closed under restriction. -/
theorem isPLOn_comp_symm (s : Set H) : IsPLOn (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) :=
  (isPLOn_id _).congr fun _ hx => I.right_inv hx.2

/-- Given a model with corners `(E, H)`, the pregroupoid of PL transformations of `H`: those maps
that are piecewise linear when read in `E` through `I`. -/
def plPregroupoid : Pregroupoid H where
  property f s := IsPLOn (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have hcomp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [hcomp]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ => ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, -⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := isPLOn_comp_symm I univ
  locality {f u} _ hloc := by
    apply isPLOn_of_locally
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx⟩ := mem_range.1 hy2
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    obtain ⟨v, v_open, xv, hv⟩ := hloc x hy1
    have hset : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc]
      congr 1
      rw [inter_comm]
    rw [hset] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx⟩ := mem_range.1 hy2
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

/-- Given a model with corners `(E, H)`, the groupoid of invertible PL transformations of `H`:
the open partial homeomorphisms that are PL, with PL inverse, when read in `E` through `I`. -/
def plGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (plPregroupoid I)

/-- Membership in `TauCeti.plGroupoid`, unfolded: both the map and its inverse are PL when read in
the model. -/
theorem mem_plGroupoid_iff {e : OpenPartialHomeomorph H H} :
    e ∈ plGroupoid I ↔ IsPLOn (I ∘ e ∘ I.symm) (I.symm ⁻¹' e.source ∩ range I) ∧
      IsPLOn (I ∘ e.symm ∘ I.symm) (I.symm ⁻¹' e.target ∩ range I) :=
  mem_groupoid_of_pregroupoid

/-- A PL map is continuous, so a PL structure refines a topological one. This is the honest form
of the "PL implies Top" inclusion: `contDiffGroupoid 0 I` *is* the groupoid of continuous
transition maps, and the content of the statement is `TauCeti.IsPLOn.continuousOn`. -/
theorem plGroupoid_le_contDiffGroupoid_zero : plGroupoid I ≤ contDiffGroupoid 0 I := by
  rw [plGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact contDiffOn_zero.2 hfs.continuousOn

/-- The identity of an open set belongs to the PL groupoid. -/
theorem ofSet_mem_plGroupoid {s : Set H} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ plGroupoid I := by
  rw [plGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : IsPLOn (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, plPregroupoid]
  exact isPLOn_comp_symm I s

/-- The PL groupoid is closed under restriction, so it can be used to define manifolds. -/
instance : ClosedUnderRestriction (plGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      exact (plGroupoid I).mem_of_eqOnSource' _ _ (ofSet_mem_plGroupoid I hs) hes)

/-! ### A non-affine element of the PL groupoid

The PL groupoid of the trivial model on `ℝ` contains a homeomorphism that agrees with no affine
map. So `TauCeti.plGroupoid` is strictly larger than the groupoid of affine transition maps, and
the definition above is not a roundabout way of asking for affineness. -/

/-- The piecewise-linear homeomorphism of `ℝ` that is the identity on the non-positive half-line
and multiplication by `2` on the non-negative one. -/
@[expose] noncomputable def doubleRight : ℝ ≃ₜ ℝ where
  toFun x := if x ≤ 0 then x else 2 * x
  invFun y := if y ≤ 0 then y else y / 2
  left_inv x := by
    by_cases hx : x ≤ 0
    · simp [hx]
    · have h2 : ¬(2 * x ≤ 0) := by rw [not_le] at hx ⊢; linarith
      simp [hx, h2]
  right_inv y := by
    by_cases hy : y ≤ 0
    · simp [hy]
    · have h2 : ¬(y / 2 ≤ 0) := by rw [not_le] at hy ⊢; linarith
      simp only [hy, h2, ite_false]
      ring
  continuous_toFun := Continuous.if_le continuous_id (continuous_const.mul continuous_id)
    continuous_id continuous_const fun x hx => by rw [hx]; ring
  continuous_invFun := Continuous.if_le continuous_id (continuous_id.div_const 2)
    continuous_id continuous_const fun x hx => by simp [hx]

@[simp]
theorem doubleRight_apply (x : ℝ) : doubleRight x = if x ≤ 0 then x else 2 * x := rfl

@[simp]
theorem doubleRight_symm_apply (y : ℝ) :
    doubleRight.symm y = if y ≤ 0 then y else y / 2 := rfl

/-- `TauCeti.doubleRight` is an element of the PL groupoid of the trivial model on `ℝ`. -/
theorem doubleRight_mem_plGroupoid :
    doubleRight.toOpenPartialHomeomorph ∈ plGroupoid 𝓘(ℝ, ℝ) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ →ᴬ[ℝ] ℝ, ∀ x : ℝ, B x = 2 * x :=
    ⟨((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap, fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ →ᴬ[ℝ] ℝ, ∀ x : ℝ, C x = x / 2 :=
    ⟨((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap, fun x => by
      simp [div_eq_inv_mul]⟩
  rw [mem_plGroupoid_iff]
  constructor
  · refine isPLOn_of_eqOn_Iic_of_eqOn_Ici (A := ContinuousAffineMap.id ℝ ℝ) (B := B)
      (fun x hx => ?_) (fun x hx => ?_) _
    · simp [mem_Iic.1 hx]
    · rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
      · simp [hB, ← h]
      · simp [hB, not_le.2 h]
  · refine isPLOn_of_eqOn_Iic_of_eqOn_Ici (A := ContinuousAffineMap.id ℝ ℝ) (B := C)
      (fun x hx => ?_) (fun x hx => ?_) _
    · simp [mem_Iic.1 hx]
    · rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
      · simp [hC, ← h]
      · simp [hC, not_le.2 h]

/-- `TauCeti.doubleRight` agrees with no continuous affine map: it fails to send the midpoint of
`-1` and `1` to the midpoint of their images. -/
theorem not_exists_continuousAffineMap_eq_doubleRight :
    ¬∃ A : ℝ →ᴬ[ℝ] ℝ, ∀ x : ℝ, doubleRight x = A x :=
  not_exists_continuousAffineMap_eq (x := 1) (y := -1) (by norm_num)

end TauCeti
