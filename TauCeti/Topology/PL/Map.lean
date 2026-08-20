/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.LocallyFinite
public import TauCeti.Analysis.Convex.Polyhedron

/-!
# Piecewise-linear maps between real topological vector spaces

A map is *piecewise linear* — PL, and piecewise *affine* would be the more honest word — when it
is affine on each cell of a polyhedral decomposition of its domain. This file builds that
predicate in the shape the PL structure groupoid needs, and proves the closure properties which
make it a `Pregroupoid` property: restriction to a subset, locality, invariance under changing the
map on nothing, and closure under composition.

## The shape of the definition

Two predicates are defined, one on top of the other.

* `TauCeti.IsPiecewiseAffineOn f V` says that `V` is covered by *finitely many* convex polyhedra
  (`TauCeti.IsConvexPolyhedron`) on each of which `f` agrees with a continuous affine map. This is
  the concrete, cell-by-cell notion.
* `TauCeti.IsPLOn f s` says that every point of `s` has a neighbourhood *in* `s` on which `f` is
  piecewise affine in the previous sense. This is the predicate the groupoid uses.

Both weakenings of the textbook notion of a polyhedral *subdivision* are deliberate, and are what
make the predicate usable as a `Pregroupoid` property on open subsets of a model space.

The cells are asked only to *cover* the set, not to be contained in it. An open subset of a model
space is not a union of polyhedra, so a subdivision *of* the set would not exist for the sets the
groupoid quantifies over, and the covering form restricts to subsets for free
(`TauCeti.IsPiecewiseAffineOn.mono`).

Finiteness is asked for only near each point. A piecewise-linear map may genuinely have infinitely
many pieces — a breakpoint at every integer, say — so a globally finite decomposition is not a
local condition, and `Pregroupoid.locality` demands one. Local finiteness is the textbook remedy,
and it implies the present predicate: a locally finite family is, by definition, finite on a small
enough neighbourhood of each point. `TauCeti.isPLOn_of_locallyFinite` records that implication, and
it is the bridge from a triangulation, which supplies exactly a locally finite family of affine
pieces.

## Main definitions

* `TauCeti.IsPiecewiseAffineOn`: a finite polyhedral decomposition on whose cells the map is
  affine.
* `TauCeti.IsPLOn`: the localisation of the previous predicate, the piecewise-linear property.

## Main results

* `TauCeti.isPiecewiseAffineOn_of_finite` and `TauCeti.isPLOn_of_locallyFinite`: the two
  constructors, from a cover indexed by an arbitrary finite type and from a locally finite one.
* `TauCeti.IsPLOn.continuousOn`: a piecewise-linear map is continuous. This is the "PL implies
  Top" content; the cells are closed and locally finite in number, so continuity is a pasting
  argument.
* `TauCeti.IsPLOn.mono`, `TauCeti.IsPLOn.congr`, `TauCeti.isPLOn_of_locally`,
  `TauCeti.IsPLOn.comp`: the four closure properties a `Pregroupoid` property must have.
* `TauCeti.isPLOn_abs` and `TauCeti.not_exists_continuousAffineMap_eq_abs`: the absolute value is
  piecewise linear and is not affine, so the predicate is strictly weaker than affineness.

This is part of the structure-group track of layer 1 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`); the groupoid built from it lives in
`TauCeti/Geometry/Manifold/PLGroupoid.lean`.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {f f' : E → F} {g : F → G} {s t V W : Set E}

/-- `IsPiecewiseAffineOn f V` says that the set `V` is covered by finitely many convex polyhedra
on each of which the map `f` agrees with a continuous affine map. -/
def IsPiecewiseAffineOn (f : E → F) (V : Set E) : Prop :=
  ∃ (n : ℕ) (C : Fin n → Set E) (A : Fin n → (E →ᴬ[ℝ] F)),
    (∀ i, IsConvexPolyhedron (C i)) ∧ V ⊆ ⋃ i, C i ∧ ∀ i, EqOn f (A i) (V ∩ C i)

/-- The constructor of `TauCeti.IsPiecewiseAffineOn` for a cover indexed by an arbitrary finite
type, rather than by `Fin n`. -/
theorem isPiecewiseAffineOn_of_finite {ι : Type*} [Finite ι] {C : ι → Set E}
    {A : ι → (E →ᴬ[ℝ] F)} (hC : ∀ i, IsConvexPolyhedron (C i)) (hcov : V ⊆ ⋃ i, C i)
    (heq : ∀ i, EqOn f (A i) (V ∩ C i)) : IsPiecewiseAffineOn f V := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨n, fun k => C (e.symm k), fun k => A (e.symm k), fun k => hC _, ?_, fun k => heq _⟩
  rwa [e.symm.surjective.iUnion_comp fun i => C i]

/-- A continuous affine map is piecewise affine on every set, with the whole space as its single
cell. -/
theorem isPiecewiseAffineOn_continuousAffineMap (A : E →ᴬ[ℝ] F) (V : Set E) :
    IsPiecewiseAffineOn (⇑A) V :=
  ⟨1, fun _ => univ, fun _ => A, fun _ => isConvexPolyhedron_univ,
    fun y _ => mem_iUnion.2 ⟨0, mem_univ y⟩, fun _ _ _ => rfl⟩

/-- Piecewise affineness passes to subsets: the same cells and affine pieces work. -/
theorem IsPiecewiseAffineOn.mono (h : IsPiecewiseAffineOn f V) (hWV : W ⊆ V) :
    IsPiecewiseAffineOn f W := by
  obtain ⟨n, C, A, hC, hcov, heq⟩ := h
  exact ⟨n, C, A, hC, hWV.trans hcov, fun i => (heq i).mono (inter_subset_inter_left _ hWV)⟩

/-- Piecewise affineness only depends on the values of the map on the set. -/
theorem IsPiecewiseAffineOn.congr (h : IsPiecewiseAffineOn f V) (hf' : EqOn f' f V) :
    IsPiecewiseAffineOn f' V := by
  obtain ⟨n, C, A, hC, hcov, heq⟩ := h
  exact ⟨n, C, A, hC, hcov, fun i => (hf'.mono inter_subset_left).trans (heq i)⟩

/-- A piecewise affine map is continuous on the set carrying the decomposition.

The cells are closed and finite in number, so this is a pasting argument: the neighbourhood filter
of a point within the set is the supremum of its neighbourhood filters within the cells, the
filters attached to cells missing the point are trivial because the cells are closed, and on the
remaining cells the map agrees with a continuous affine map. -/
theorem IsPiecewiseAffineOn.continuousOn (h : IsPiecewiseAffineOn f V) : ContinuousOn f V := by
  obtain ⟨n, C, A, hC, hcov, heq⟩ := h
  intro x hx
  have hVeq : V = ⋃ i, V ∩ C i := by
    rw [← inter_iUnion]
    exact (inter_eq_self_of_subset_left hcov).symm
  have hfilter : 𝓝[V] x = ⨆ i, 𝓝[V ∩ C i] x := by
    conv_lhs => rw [hVeq]
    exact nhdsWithin_iUnion _ _
  rw [ContinuousWithinAt, hfilter, tendsto_iSup]
  intro i
  by_cases hxi : x ∈ C i
  · exact ((A i).continuous.continuousWithinAt).congr (heq i) (heq i ⟨hx, hxi⟩)
  · have hcl : x ∉ closure (V ∩ C i) := fun hmem =>
      hxi ((hC i).isClosed.closure_subset (closure_mono inter_subset_right hmem))
    rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hcl
    rw [hcl]
    exact tendsto_bot

/-- Piecewise affine maps compose: refine the cells of the source decomposition by pulling the
cells of the target decomposition back along the affine pieces.

No continuity is needed here, because the refined cover is honest: the affine piece of `f` on a
source cell agrees with `f` there, so it lands in the same target cell that `f` does. -/
theorem IsPiecewiseAffineOn.comp {W : Set F} (hg : IsPiecewiseAffineOn g W)
    (hf : IsPiecewiseAffineOn f V) (hmap : MapsTo f V W) : IsPiecewiseAffineOn (g ∘ f) V := by
  obtain ⟨n, C, A, hC, hcov, heq⟩ := hf
  obtain ⟨m, D, B, hD, hDcov, hDeq⟩ := hg
  refine isPiecewiseAffineOn_of_finite (ι := Fin n × Fin m)
    (C := fun p => C p.1 ∩ (A p.1) ⁻¹' D p.2) (A := fun p => (B p.2).comp (A p.1))
    (fun p => (hC p.1).inter ((hD p.2).preimage (A p.1))) ?_ ?_
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hy)
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hDcov (hmap hy))
    have hfy : f y = A i y := heq i ⟨hy, hi⟩
    exact mem_iUnion.2 ⟨(i, j), hi, by rwa [mem_preimage, ← hfy]⟩
  · rintro ⟨i, j⟩ y ⟨hy, hyC, hyD⟩
    have hfy : f y = A i y := heq i ⟨hy, hyC⟩
    have hmem : A i y ∈ W ∩ D j := ⟨hfy ▸ hmap hy, hyD⟩
    rw [Function.comp_apply, hfy, ContinuousAffineMap.comp_apply]
    exact hDeq j hmem

/-- `IsPLOn f s` says that the map `f` is *piecewise linear* on the set `s`: every point of `s`
has a neighbourhood in `s` covered by finitely many convex polyhedra on each of which `f` agrees
with a continuous affine map. -/
def IsPLOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, IsPiecewiseAffineOn f V

/-- A piecewise affine map is piecewise linear on the set carrying its decomposition. -/
theorem IsPiecewiseAffineOn.isPLOn (h : IsPiecewiseAffineOn f V) : IsPLOn f V :=
  fun _ _ => ⟨V, self_mem_nhdsWithin, h⟩

/-- A continuous affine map is piecewise linear on every set. -/
theorem isPLOn_continuousAffineMap (A : E →ᴬ[ℝ] F) (s : Set E) : IsPLOn (⇑A) s :=
  (isPiecewiseAffineOn_continuousAffineMap A s).isPLOn

/-- The identity is piecewise linear on every set. -/
theorem isPLOn_id (s : Set E) : IsPLOn (id : E → E) s :=
  isPLOn_continuousAffineMap (ContinuousAffineMap.id ℝ E) s

/-- The piecewise-linear property passes to subsets. -/
theorem IsPLOn.mono (h : IsPLOn f s) (hts : t ⊆ s) : IsPLOn f t := fun x hx => by
  obtain ⟨V, hV, hPA⟩ := h x (hts hx)
  exact ⟨V, nhdsWithin_mono x hts hV, hPA⟩

/-- The piecewise-linear property only depends on the values of the map on the set. -/
theorem IsPLOn.congr (h : IsPLOn f s) (hf' : EqOn f' f s) : IsPLOn f' s := fun x hx => by
  obtain ⟨V, hV, hPA⟩ := h x hx
  exact ⟨V ∩ s, inter_mem hV self_mem_nhdsWithin,
    (hPA.mono inter_subset_left).congr (hf'.mono inter_subset_right)⟩

/-- A piecewise-linear map is continuous. -/
theorem IsPLOn.continuousOn (h : IsPLOn f s) : ContinuousOn f s := fun x hx => by
  obtain ⟨V, hV, hPA⟩ := h x hx
  rw [← continuousWithinAt_inter' hV]
  exact (hPA.continuousOn x (mem_of_mem_nhdsWithin hx hV)).mono inter_subset_right

/-- The piecewise-linear property is local: it suffices to have it on a neighbourhood in `s` of
each point of `s`. -/
theorem isPLOn_of_forall_mem_nhdsWithin (h : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, IsPLOn f (s ∩ V)) :
    IsPLOn f s := fun x hx => by
  obtain ⟨V, hV, hPL⟩ := h x hx
  obtain ⟨W, hW, hPA⟩ := hPL x ⟨hx, mem_of_mem_nhdsWithin hx hV⟩
  rw [nhdsWithin_inter_of_mem' hV] at hW
  exact ⟨W, hW, hPA⟩

/-- The piecewise-linear property is local, in the form the `Pregroupoid` locality axiom asks
for: it suffices to have it on the trace of an open neighbourhood of each point of `s`. -/
theorem isPLOn_of_locally (h : ∀ x ∈ s, ∃ V, IsOpen V ∧ x ∈ V ∧ IsPLOn f (s ∩ V)) : IsPLOn f s :=
  isPLOn_of_forall_mem_nhdsWithin fun x hx => by
    obtain ⟨V, hVo, hxV, hPL⟩ := h x hx
    exact ⟨V, nhdsWithin_le_nhds (hVo.mem_nhds hxV), hPL⟩

/-- Piecewise-linear maps compose.

Continuity of `f` (`TauCeti.IsPLOn.continuousOn`) enters here, and only here: it is what shrinks
the neighbourhood of `x` on which `f` is piecewise affine to one that `f` carries into the
neighbourhood of `f x` on which `g` is piecewise affine. -/
theorem IsPLOn.comp {t : Set F} (hg : IsPLOn g t) (hf : IsPLOn f s) (hst : s ⊆ f ⁻¹' t) :
    IsPLOn (g ∘ f) s := fun x hx => by
  obtain ⟨V, hV, hPAf⟩ := hf x hx
  obtain ⟨W, hW, hPAg⟩ := hg (f x) (hst hx)
  have hpre : f ⁻¹' W ∈ 𝓝[s] x := (hf.continuousOn x hx).tendsto_nhdsWithin hst hW
  exact ⟨V ∩ (s ∩ f ⁻¹' W), inter_mem hV (inter_mem self_mem_nhdsWithin hpre),
    hPAg.comp (hPAf.mono inter_subset_left) fun _ hy => hy.2.2⟩

/-- A *locally finite* polyhedral cover of `s` on whose cells `f` is affine makes `f` piecewise
linear on `s`. This is the bridge from a triangulation, which supplies exactly such a cover, and
it is why the local finite formulation of `TauCeti.IsPLOn` loses nothing. -/
theorem isPLOn_of_locallyFinite {ι : Type*} {C : ι → Set E} {A : ι → (E →ᴬ[ℝ] F)}
    (hlf : LocallyFinite C) (hC : ∀ i, IsConvexPolyhedron (C i)) (hcov : s ⊆ ⋃ i, C i)
    (heq : ∀ i, EqOn f (A i) (s ∩ C i)) : IsPLOn f s := fun x _ => by
  obtain ⟨U, hU, hfin⟩ := hlf x
  have : Finite {i // (C i ∩ U).Nonempty} := hfin.to_subtype
  refine ⟨s ∩ U, inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hU),
    isPiecewiseAffineOn_of_finite (ι := {i // (C i ∩ U).Nonempty}) (C := fun i => C i.1)
      (A := fun i => A i.1) (fun i => hC _) ?_
      (fun i => (heq i.1).mono (inter_subset_inter_left _ inter_subset_left))⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hy.1)
  exact mem_iUnion.2 ⟨⟨i, ⟨y, hi, hy.2⟩⟩, hi⟩

/-! ### Piecewise-linear maps of the line

The two-piece criterion on `ℝ`, and the absolute value as a piecewise-linear map that is not
affine. The criterion is what the concrete examples of the PL groupoid are built from, and the
absolute value pins down that `TauCeti.IsPLOn` is strictly weaker than affineness rather than a
roundabout way of saying it. -/

/-- The identity of `ℝ`, as a continuous affine map. -/
theorem exists_continuousAffineMap_real_id : ∃ A : ℝ →ᴬ[ℝ] ℝ, ∀ x : ℝ, A x = x :=
  ⟨(ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap, fun _ => rfl⟩

/-- A map of `ℝ` that agrees with a continuous affine map on each of the two closed half-lines is
piecewise linear. -/
theorem isPLOn_of_eqOn_Iic_of_eqOn_Ici {h : ℝ → ℝ} {A B : ℝ →ᴬ[ℝ] ℝ} (hA : EqOn h A (Iic 0))
    (hB : EqOn h B (Ici 0)) (s : Set ℝ) : IsPLOn h s := by
  obtain ⟨N, hN⟩ := exists_continuousAffineMap_real_id
  have hIic : IsConvexPolyhedron (Iic (0 : ℝ)) := by
    have hset : Iic (0 : ℝ) = {x : ℝ | N x ≤ 0} := by ext x; simp [hN]
    rw [hset]
    exact isConvexPolyhedron_setOf_le N
  have hIci : IsConvexPolyhedron (Ici (0 : ℝ)) := by
    have hset : Ici (0 : ℝ) = {x : ℝ | (-N) x ≤ 0} := by ext x; simp [hN]
    rw [hset]
    exact isConvexPolyhedron_setOf_le (-N)
  refine (isPiecewiseAffineOn_of_finite (ι := Bool) (f := h) (V := univ)
    (C := fun b => cond b (Iic (0 : ℝ)) (Ici (0 : ℝ))) (A := fun b => cond b A B)
    ?_ ?_ ?_).isPLOn.mono (subset_univ s)
  · rintro (_ | _)
    · exact hIci
    · exact hIic
  · intro x _
    rcases le_total x 0 with hx | hx
    · exact mem_iUnion.2 ⟨true, hx⟩
    · exact mem_iUnion.2 ⟨false, hx⟩
  · rintro (_ | _) x ⟨-, hx⟩
    · exact hB hx
    · exact hA hx

/-- A map that fails to send a midpoint to the corresponding midpoint agrees with no continuous
affine map. This is the certificate used below to show that a piecewise-linear map need not be
affine. -/
theorem not_exists_continuousAffineMap_eq {h : E → F} {x y : E}
    (hne : h ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • y) ≠ (2⁻¹ : ℝ) • h x + (2⁻¹ : ℝ) • h y) :
    ¬∃ A : E →ᴬ[ℝ] F, ∀ z : E, h z = A z := by
  rintro ⟨A, hA⟩
  refine hne ?_
  rw [hA, hA, hA]
  exact Convex.combo_affine_apply (f := (A : E →ᵃ[ℝ] F)) (by norm_num)

/-- The absolute value on `ℝ` is piecewise linear: the two half-lines are its cells. -/
theorem isPLOn_abs (s : Set ℝ) : IsPLOn (fun x : ℝ => |x|) s := by
  obtain ⟨A, hA⟩ := exists_continuousAffineMap_real_id
  exact isPLOn_of_eqOn_Iic_of_eqOn_Ici (A := -A) (B := A)
    (fun x hx => by simp [hA, abs_of_nonpos (mem_Iic.1 hx)])
    (fun x hx => by simp [hA, abs_of_nonneg (mem_Ici.1 hx)]) s

/-- The absolute value on `ℝ` is not affine, so the piecewise-linear maps are strictly more than
the affine ones. -/
theorem not_exists_continuousAffineMap_eq_abs : ¬∃ A : ℝ →ᴬ[ℝ] ℝ, ∀ x : ℝ, |x| = A x :=
  not_exists_continuousAffineMap_eq (x := 1) (y := -1) (by norm_num)

end TauCeti
