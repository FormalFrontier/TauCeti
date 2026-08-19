/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.OneLoop

/-!
# The loop quiver has infinite representation type

A representation of the quiver `•↺` with one vertex and one loop is a vector space together with an
endomorphism of it. The one-dimensional such representations are the scalars: for `c` in the base
field, `TauCeti.oneLoopRep k c` is the line `k` with the loop acting by multiplication by `c`. Each
is indecomposable, being a line, and two of them are isomorphic only when the scalars agree, an
isomorphism intertwining the two multiplications on a vector where it does not vanish. Over an
infinite field this is already an infinite supply of pairwise non-isomorphic finite-dimensional
indecomposables, so the loop quiver has infinite representation type.

This is the boundary case that delimits where the theory of quiver representations needs
acyclicity: `•↺` is the smallest non-acyclic quiver, its path algebra is the infinite-dimensional
`k[X]` (`TauCeti.PathAlgebra.oneLoopAlgEquiv`), and the classification of its indecomposables is the
Jordan normal form rather than anything finite.

## Main declarations

* `TauCeti.oneLoopRep`: the line on which the loop of `•↺` acts by a given scalar.
* `TauCeti.oneLoopRepScalar`: the scalar by which a morphism between two of them acts.

## Main results

* `TauCeti.indecomposable_oneLoopRep`: the scalar representations are indecomposable.
* `TauCeti.nonempty_oneLoopRep_iso_iff`: two of them are isomorphic exactly when the scalars agree.
* `TauCeti.not_isFiniteRepType_oneLoop`: over an infinite field the loop quiver has infinite
  representation type.

## Implementation notes

Everything runs through `TauCeti.oneLoopRepScalar`, the value at `1` of the single component of a
morphism: `•↺` has one vertex, so a natural transformation is one linear map, and that linear map
is an endomorphism of the line `k`, hence multiplication by a scalar. Composition multiplies these
scalars (in the opposite order), so the morphisms between scalar representations behave like the
field itself, and the three facts needed below -- an idempotent endomorphism is `0` or the
identity, an isomorphism has an invertible scalar, and naturality along the loop reads
`s · c = d · s` -- are all statements about `k`.

Indecomposability is therefore proved from `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`
rather than from the brick criterion; computing the endomorphism algebra in full would prove the
same thing with more work.

`TauCeti.oneLoopRep` carries `@[expose]` because the vertex space of the representation has to
reduce to the base field for the statements below to elaborate: a functor built by
`CategoryTheory.Paths.lift` reveals its value on objects only through its definition.

Over a *finite* field the loop quiver still has infinite representation type, witnessed instead by
the Jordan blocks `k[X]/(Xⁿ)`, whose indecomposability is not the one-line argument used here; that
case is not proved here.

## References

This proves the `¬ IsFiniteRepType` half of the loop-quiver worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose other half -- that the
path algebra is `k[X]` and is infinite-dimensional -- is `TauCeti.PathAlgebra.oneLoopAlgEquiv`
together with `TauCeti.not_finiteDimensional_pathAlgebra_oneLoop`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type u) [Field k]

/-- **The line on which the loop acts by the scalar `c`**: the one-dimensional representation of
the quiver `•↺` given by the base field at its only vertex, with the loop acting by multiplication
by `c`. -/
@[expose]
def oneLoopRep (c : k) : QuiverRep.{u, 0, w, u} k Quiver.OneLoop :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k k
      map := fun _ ↦ ModuleCat.ofHom (c • LinearMap.id) }

variable {k}

/-- The vertex space of `TauCeti.oneLoopRep` is the base field. -/
@[simp]
theorem oneLoopRep_obj (c : k) (v : Paths Quiver.OneLoop) :
    (oneLoopRep.{u, w} k c).obj v = ModuleCat.of k k :=
  rfl

-- Not `@[simp]`: `TauCeti.dimVector_apply` together with `TauCeti.oneLoopRep_obj` already reduces
-- the left-hand side, so tagging this is a simp-normal-form violation (`simpNF`).
/-- `TauCeti.oneLoopRep k c` is a line: its dimension vector is `1`. -/
theorem dimVector_oneLoopRep (c : k) (v : Quiver.OneLoop) :
    dimVector (oneLoopRep.{u, w} k c) v = 1 := by
  rw [dimVector_apply, oneLoopRep_obj]
  exact Module.finrank_self k

/-- The loop of `•↺` acts on `TauCeti.oneLoopRep k c` by multiplication by `c`. -/
theorem oneLoopRep_map_loop (c : k) :
    (oneLoopRep.{u, w} k c).map (Quiver.Hom.toPath Quiver.OneLoop.loop) =
      ModuleCat.ofHom (c • LinearMap.id) :=
  Paths.lift_toPath _ _

/-- The action of the loop, read on an element of the vertex space. -/
theorem oneLoopRep_map_loop_apply (c : k) (x : k) :
    ((oneLoopRep.{u, w} k c).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x = c * x := by
  rw [oneLoopRep_map_loop]
  rfl

/-- **The scalar of a morphism of scalar representations of `•↺`**: its single component is an
endomorphism of the line `k`, hence multiplication by this value at `1`. -/
def oneLoopRepScalar {c d : k} (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) : k :=
  (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom (1 : k)

/-- A morphism of scalar representations acts by multiplication by its scalar. -/
theorem oneLoopRepScalar_apply {c d : k} (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d)
    (x : k) :
    (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom x = oneLoopRepScalar f * x := by
  have hx : (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom (x • (1 : k))
      = x • oneLoopRepScalar f := map_smul _ x (1 : k)
  rw [smul_eq_mul, mul_one] at hx
  rw [hx, smul_eq_mul, mul_comm]

/-- Composition multiplies the scalars, in the order opposite to composition. -/
@[simp]
theorem oneLoopRepScalar_comp {c d e : k} (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d)
    (g : oneLoopRep.{u, w} k d ⟶ oneLoopRep.{u, w} k e) :
    oneLoopRepScalar (f ≫ g) = oneLoopRepScalar g * oneLoopRepScalar f := by
  change (g.app _).hom ((f.app _).hom (1 : k)) = _
  rw [oneLoopRepScalar_apply f, mul_one, oneLoopRepScalar_apply g]

/-- The identity has scalar `1`. -/
@[simp]
theorem oneLoopRepScalar_id (c : k) : oneLoopRepScalar (𝟙 (oneLoopRep.{u, w} k c)) = 1 := (rfl)

/-- The zero morphism has scalar `0`. -/
@[simp]
theorem oneLoopRepScalar_zero (c d : k) :
    oneLoopRepScalar (0 : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) = 0 := (rfl)

/-- **A morphism of scalar representations is determined by its scalar.** The quiver has one
vertex, so a natural transformation is its single component, and that component is multiplication
by the scalar. -/
theorem oneLoopRep_hom_ext {c d : k} {f g : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d}
    (h : oneLoopRepScalar f = oneLoopRepScalar g) : f = g := by
  apply NatTrans.ext
  funext v
  cases v
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

/-- **A morphism intertwines the two loop actions**: naturality along the loop says that its scalar
`s` satisfies `s * c = d * s`. Over a field this forces `c = d` as soon as `s` is nonzero. -/
theorem oneLoopRepScalar_intertwine {c d : k}
    (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) :
    oneLoopRepScalar f * c = d * oneLoopRepScalar f := by
  have hnat : (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom
        (((oneLoopRep.{u, w} k c).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom (1 : k))
      = ((oneLoopRep.{u, w} k d).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom
        ((f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom (1 : k)) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) (1 : k))
      (f.naturality (Quiver.Hom.toPath Quiver.OneLoop.loop))
  rw [oneLoopRep_map_loop_apply c (1 : k), mul_one, oneLoopRepScalar_apply f c,
    oneLoopRepScalar_apply f (1 : k), mul_one,
    oneLoopRep_map_loop_apply d (oneLoopRepScalar f)] at hnat
  exact hnat

/-- `TauCeti.oneLoopRep k c` is finite-dimensional: it is a line. -/
theorem isFinDim_oneLoopRep (c : k) : IsFinDim k Quiver.OneLoop (oneLoopRep.{u, w} k c) :=
  isFinDim_iff.mpr fun _ ↦ inferInstanceAs (FiniteDimensional k k)

/-- `TauCeti.oneLoopRep k c` is nonzero: the vector space at its vertex is the base field, which is
not the zero module. -/
theorem not_isZero_oneLoopRep (c : k) : ¬ IsZero (oneLoopRep.{u, w} k c) := by
  intro h
  have : Subsingleton k :=
    ModuleCat.subsingleton_of_isZero (h.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
  exact one_ne_zero (α := k) (Subsingleton.elim _ _)

/-- **`TauCeti.oneLoopRep k c` is indecomposable.** Its only vertex carries a line, so an idempotent
endomorphism has an idempotent scalar, hence is `0` or the identity. -/
theorem indecomposable_oneLoopRep (c : k) : Indecomposable (oneLoopRep.{u, w} k c) := by
  refine indecomposable_of_idempotent_eq_zero_or_id (not_isZero_oneLoopRep c) fun e he ↦ ?_
  have hidem : IsIdempotentElem (oneLoopRepScalar e) := by
    have h := congrArg oneLoopRepScalar he
    rwa [oneLoopRepScalar_comp] at h
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h0 | h1
  · exact Or.inl (oneLoopRep_hom_ext (by rw [h0, oneLoopRepScalar_zero]))
  · exact Or.inr (oneLoopRep_hom_ext (by rw [h1, oneLoopRepScalar_id]))

/-- **Two scalar representations of `•↺` are isomorphic only if their scalars agree.** The scalar of
an isomorphism is invertible, because the scalars of the two composites multiply to `1`, and
intertwining then equates the two loop actions. -/
theorem eq_of_nonempty_oneLoopRep_iso {c d : k}
    (h : Nonempty (oneLoopRep.{u, w} k c ≅ oneLoopRep.{u, w} k d)) : c = d := by
  obtain ⟨e⟩ := h
  have hne : oneLoopRepScalar e.hom ≠ 0 := by
    intro h0
    have h1 := congrArg oneLoopRepScalar e.hom_inv_id
    rw [oneLoopRepScalar_comp, oneLoopRepScalar_id, h0, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (by rw [oneLoopRepScalar_intertwine e.hom, mul_comm])

/-- Two scalar representations of `•↺` are isomorphic exactly when their scalars agree. -/
theorem nonempty_oneLoopRep_iso_iff {c d : k} :
    Nonempty (oneLoopRep.{u, w} k c ≅ oneLoopRep.{u, w} k d) ↔ c = d :=
  ⟨eq_of_nonempty_oneLoopRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **The loop quiver has infinite representation type over an infinite field.** The scalar
representations `TauCeti.oneLoopRep k c` are finite-dimensional, indecomposable, and pairwise
non-isomorphic, so the base field itself indexes an infinite family of them. -/
theorem not_isFiniteRepType_oneLoop (k : Type u) [Field k] [Infinite k] :
    ¬ IsFiniteRepType.{u, 0, w, u} k Quiver.OneLoop :=
  not_isFiniteRepType_of_infinite (M := oneLoopRep.{u, w} k) isFinDim_oneLoopRep
    indecomposable_oneLoopRep fun _ _ hne h ↦ hne (eq_of_nonempty_oneLoopRep_iso h)

end TauCeti
