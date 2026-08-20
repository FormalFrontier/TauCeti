/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Convex polyhedra

A *convex polyhedron* in a real topological vector space is the solution set of finitely many
non-strict affine inequalities `g i x ≤ 0`, the `g i` being continuous affine functionals. This
file introduces that predicate and the three closure properties a piecewise-linear calculus needs:
a convex polyhedron is closed and convex, a finite intersection of convex polyhedra is one, and
the preimage of one under a continuous affine map is one.

Those last two are exactly what makes the cells of a piecewise-affine decomposition composable:
composing two piecewise-affine maps refines the source decomposition by pulling the target cells
back along the affine pieces, and both operations must stay inside the class of cells.

The name is deliberately *not* `IsPolyhedron`. In piecewise-linear topology a polyhedron is a
much weaker notion — a subset that is locally a cone, so a locally finite union of simplices,
which need not be convex. The convex sets defined here are the *cells* out of which such a
polyhedron is assembled.

## Main definitions

* `TauCeti.IsConvexPolyhedron`: the solution set of finitely many non-strict affine inequalities.

## Main results

* `TauCeti.isConvexPolyhedron_iInter`: the defining form, with the inequalities indexed by an
  arbitrary finite type rather than by `Fin n`.
* `TauCeti.IsConvexPolyhedron.isClosed` and `TauCeti.IsConvexPolyhedron.convex`: a convex
  polyhedron is closed and convex, which is what its name claims.
* `TauCeti.IsConvexPolyhedron.inter`: an intersection of two convex polyhedra is one.
* `TauCeti.IsConvexPolyhedron.preimage`: the preimage of a convex polyhedron under a continuous
  affine map is one.
-/

public section

open Set

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {s t : Set E}

/-- A *convex polyhedron* is the solution set of finitely many non-strict affine inequalities,
the inequalities being given by continuous affine functionals. -/
def IsConvexPolyhedron (s : Set E) : Prop :=
  ∃ (n : ℕ) (g : Fin n → (E →ᴬ[ℝ] ℝ)), s = {x | ∀ i, g i x ≤ 0}

/-- The solution set of a finite family of non-strict affine inequalities, indexed by an arbitrary
finite type, is a convex polyhedron. This is the form in which the definition is used: the
constructions below produce their inequalities indexed by sums and products of index types. -/
theorem isConvexPolyhedron_iInter {ι : Type*} [Finite ι] (g : ι → (E →ᴬ[ℝ] ℝ)) :
    IsConvexPolyhedron {x : E | ∀ i, g i x ≤ 0} := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨n, fun k => g (e.symm k), ?_⟩
  ext x
  exact ⟨fun h k => h _, fun h i => by simpa using h (e i)⟩

/-- A single non-strict affine inequality cuts out a convex polyhedron. -/
theorem isConvexPolyhedron_setOf_le (g : E →ᴬ[ℝ] ℝ) : IsConvexPolyhedron {x : E | g x ≤ 0} :=
  ⟨1, fun _ => g, by ext x; simp⟩

/-- The whole space is a convex polyhedron: it is cut out by the empty family of inequalities. -/
theorem isConvexPolyhedron_univ : IsConvexPolyhedron (univ : Set E) :=
  ⟨0, Fin.elim0, by ext x; simp⟩

/-- A convex polyhedron is closed, being an intersection of preimages of `Set.Iic 0` under
continuous maps. -/
theorem IsConvexPolyhedron.isClosed (h : IsConvexPolyhedron s) : IsClosed s := by
  obtain ⟨n, g, rfl⟩ := h
  have : {x : E | ∀ i, g i x ≤ 0} = ⋂ i, (g i) ⁻¹' Iic 0 := by ext x; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_Iic.preimage (g i).continuous

/-- A convex polyhedron is convex: each defining inequality is preserved by affine combinations
because the functional cutting it out is affine. -/
theorem IsConvexPolyhedron.convex (h : IsConvexPolyhedron s) : Convex ℝ s := by
  obtain ⟨n, g, rfl⟩ := h
  intro x hx y hy a b ha hb hab i
  have hcombo : (g i) (a • x + b • y) = a • (g i) x + b • (g i) y :=
    Convex.combo_affine_apply (f := ((g i : E →ᵃ[ℝ] ℝ))) hab
  rw [hcombo, smul_eq_mul, smul_eq_mul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx i))
    (mul_nonpos_of_nonneg_of_nonpos hb (hy i))

/-- An intersection of two convex polyhedra is a convex polyhedron: concatenate the two families
of defining inequalities. -/
theorem IsConvexPolyhedron.inter (hs : IsConvexPolyhedron s) (ht : IsConvexPolyhedron t) :
    IsConvexPolyhedron (s ∩ t) := by
  obtain ⟨n, g, rfl⟩ := hs
  obtain ⟨m, h, rfl⟩ := ht
  have hsum : {x : E | ∀ i, g i x ≤ 0} ∩ {x : E | ∀ j, h j x ≤ 0}
      = {x : E | ∀ k : Fin n ⊕ Fin m, Sum.elim g h k x ≤ 0} := by
    ext x
    simp [Sum.forall]
  rw [hsum]
  exact isConvexPolyhedron_iInter _

/-- The preimage of a convex polyhedron under a continuous affine map is a convex polyhedron:
precompose each defining inequality with the map. -/
theorem IsConvexPolyhedron.preimage {u : Set F} (hu : IsConvexPolyhedron u) (A : E →ᴬ[ℝ] F) :
    IsConvexPolyhedron (A ⁻¹' u) := by
  obtain ⟨n, g, rfl⟩ := hu
  exact ⟨n, fun i => (g i).comp A, by ext x; simp⟩

end TauCeti
