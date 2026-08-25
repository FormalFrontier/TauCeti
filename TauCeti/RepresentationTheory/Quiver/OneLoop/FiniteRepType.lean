/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.OneLoop.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.LocalRing.Basic
public import TauCeti.RingTheory.Polynomial.Truncated
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The loop quiver has infinite representation type

A representation of the quiver `•↺` with one vertex and one loop is a vector space together with an
endomorphism of it. Two families of them are built here. The one-dimensional ones are the scalars:
for `c` in the base field, `TauCeti.oneLoopRep k c` is the line `k` with the loop acting by
multiplication by `c`; each is indecomposable, being a line, and two of them are isomorphic only
when the scalars agree, an isomorphism intertwining the two multiplications on a vector where it
does not vanish. The nilpotent Jordan blocks `TauCeti.oneLoopNilpotentRep k n` are the truncated
polynomial algebras `k[X]/(Xⁿ⁺¹)` with the loop acting by multiplication by `X`; they have
dimension `n + 1`, so they are pairwise non-isomorphic, and each is indecomposable because its
endomorphisms are the multiplications by its own elements and `k[X]/(Xⁿ⁺¹)` has no idempotent but
`0` and `1`. They exist over *every* field, so the loop quiver has infinite representation type
over every field; the scalar family would only settle the case of an infinite base field.

This is the boundary case that delimits where the theory of quiver representations needs
acyclicity: `•↺` is the smallest non-acyclic quiver, its path algebra is the infinite-dimensional
`k[X]` (`TauCeti.PathAlgebra.oneLoopAlgEquiv`), and its finite-dimensional indecomposables are the
cyclic torsion `k[X]`-modules `k[X]/(pⁿ)` for `p` irreducible -- the Jordan blocks when `k` is
algebraically closed -- rather than anything finite.

## Main declarations

* `TauCeti.oneLoopRep`: the line on which the loop of `•↺` acts by a given scalar.
* `TauCeti.oneLoopRepScalar`: the scalar by which a morphism between two of them acts.
* `TauCeti.oneLoopRepHom`: conversely, the morphism attached to an intertwining scalar.
* `TauCeti.oneLoopNilpotentRep`: the nilpotent Jordan block `k[X]/(Xⁿ⁺¹)`.

## Main results

* `TauCeti.indecomposable_oneLoopRep`: the scalar representations are indecomposable.
* `TauCeti.nonempty_oneLoopRep_iso_iff`: two of them are isomorphic exactly when the scalars agree.
* `TauCeti.indecomposable_oneLoopNilpotentRep`: the nilpotent Jordan blocks are indecomposable.
* `TauCeti.nonempty_oneLoopNilpotentRep_iso_iff`: two of them are isomorphic exactly when their
  sizes agree.
* `TauCeti.not_isFiniteRepType_oneLoop`: over any field the loop quiver has infinite representation
  type.

## Implementation notes

The scalar family runs through `TauCeti.oneLoopRepScalar`, the value at `1` of the single component
of a morphism: `•↺` has one vertex, so a natural transformation is one linear map, and that linear
map is an endomorphism of the line `k`, hence multiplication by a scalar. Composition multiplies
these scalars (in the opposite order), so the morphisms between scalar representations are exactly
the scalars `s` with `s * c = d * s`: `TauCeti.oneLoopRepHom` builds the morphism from such a
scalar, `TauCeti.oneLoopRepScalar_oneLoopRepHom` and `TauCeti.oneLoopRep_hom_ext` make the two
constructions inverse to each other.

Indecomposability is proved throughout from `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`
rather than from the brick criterion: for the Jordan blocks the endomorphism algebra is
`k[X]/(Xⁿ⁺¹)`, which is not a field, so the brick criterion does not apply, and an endomorphism is
pinned down instead by its value at `1` (`AdjoinRoot.eq_mulRight_of_root_mul`, from
`TauCeti.RingTheory.AdjoinRoot`). That the value is then `0` or `1` is locality of the truncated
polynomial algebra, `TauCeti.isLocalRing_adjoinRoot_X_pow` from
`TauCeti.RingTheory.Polynomial.Truncated`.

The quiver `•↺` itself -- `TauCeti.Quiver.OneLoop`, with its `Quiver` instance and its loop
`TauCeti.Quiver.OneLoop.loop` -- is defined in
`TauCeti.RepresentationTheory.Quiver.OneLoop.Basic`, which carries the vertex and arrow data alone;
the path-algebra results cited under "References" are not imported here.

`TauCeti.oneLoopRep` and `TauCeti.oneLoopNilpotentRep` carry `@[expose]` because the vertex space of
the representation has to reduce to `k`, resp. to `k[X]/(Xⁿ⁺¹)`, for the statements below to
elaborate at all: a functor built by `CategoryTheory.Paths.lift` reveals its value on objects only
through its definition, and without it even `TauCeti.oneLoopRep_map_loop_apply` fails to typecheck.

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
@[simp]
theorem oneLoopRep_map_loop_apply (c : k) (x : k) :
    ((oneLoopRep.{u, w} k c).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x = c * x := by
  rw [oneLoopRep_map_loop]
  rfl

/-- **The scalar of a morphism of scalar representations of `•↺`**: its single component is an
endomorphism of the line `k`, hence multiplication by this value at `1`. -/
def oneLoopRepScalar {c d : k} (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) : k :=
  (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom (1 : k)

/-- A morphism of scalar representations acts by multiplication by its scalar. -/
@[simp]
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
  -- The single component of a composite of natural transformations is the composite of the
  -- components, so the scalar of `f ≫ g` is `g` evaluated at the value of `f` at `1`.
  have h : oneLoopRepScalar (f ≫ g) = (g.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom
      ((f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom (1 : k)) :=
    ModuleCat.comp_apply _ _ _
  rw [h, oneLoopRepScalar_apply f, mul_one, oneLoopRepScalar_apply g]

/-- The identity has scalar `1`. -/
@[simp]
theorem oneLoopRepScalar_id (c : k) : oneLoopRepScalar (𝟙 (oneLoopRep.{u, w} k c)) = 1 := (rfl)

/-- The zero morphism has scalar `0`. -/
@[simp]
theorem oneLoopRepScalar_zero (c d : k) :
    oneLoopRepScalar (0 : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) = 0 := (rfl)

/-- **The morphism of scalar representations attached to an intertwining scalar**: multiplication
by `s` at the only vertex, which is natural along the loop exactly when `s * c = d * s`. -/
def oneLoopRepHom {c d : k} (s : k) (hs : s * c = d * s) :
    oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d :=
  Paths.liftNatTrans (fun _ ↦ ModuleCat.ofHom (s • LinearMap.id)) fun {a b} f ↦ by
    cases a
    cases b
    rw [Subsingleton.elim f Quiver.OneLoop.loop, oneLoopRep_map_loop, oneLoopRep_map_loop]
    -- Both composites are multiplication by a product of two scalars, in the two orders; the
    -- intertwining hypothesis is exactly the equality of those products. A linear map out of the
    -- line is determined by its value at `1`.
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    have hl : (ModuleCat.Hom.hom (ModuleCat.ofHom (c • (LinearMap.id : k →ₗ[k] k)) ≫
        ModuleCat.ofHom (s • (LinearMap.id : k →ₗ[k] k)))) (1 : k) = s * (c * 1) := (rfl)
    have hr : (ModuleCat.Hom.hom (ModuleCat.ofHom (s • (LinearMap.id : k →ₗ[k] k)) ≫
        ModuleCat.ofHom (d • (LinearMap.id : k →ₗ[k] k)))) (1 : k) = d * (s * 1) := (rfl)
    have hcomm : s * (c * 1) = d * (s * 1) := by rw [mul_one, mul_one, hs]
    exact hl.trans (hcomm.trans hr.symm)

/-- The scalar of `TauCeti.oneLoopRepHom s hs` is `s`. -/
@[simp]
theorem oneLoopRepScalar_oneLoopRepHom {c d : k} (s : k) (hs : s * c = d * s) :
    oneLoopRepScalar (oneLoopRepHom.{u, w} (c := c) (d := d) s hs) = s := by
  have h : oneLoopRepScalar (oneLoopRepHom.{u, w} (c := c) (d := d) s hs) = s * 1 := (rfl)
  rw [h, mul_one]

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

/-- **Every morphism of scalar representations is the one attached to its scalar**, so
`TauCeti.oneLoopRepHom` and `TauCeti.oneLoopRepScalar` identify the morphisms `oneLoopRep k c ⟶
oneLoopRep k d` with the scalars `s` satisfying `s * c = d * s`. -/
@[simp]
theorem oneLoopRepHom_oneLoopRepScalar {c d : k}
    (f : oneLoopRep.{u, w} k c ⟶ oneLoopRep.{u, w} k d) :
    oneLoopRepHom (oneLoopRepScalar f) (oneLoopRepScalar_intertwine f) = f :=
  oneLoopRep_hom_ext (oneLoopRepScalar_oneLoopRepHom _ _)

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
@[simp]
theorem nonempty_oneLoopRep_iso_iff {c d : k} :
    Nonempty (oneLoopRep.{u, w} k c ≅ oneLoopRep.{u, w} k d) ↔ c = d :=
  ⟨eq_of_nonempty_oneLoopRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

section Nilpotent

open Polynomial

variable (k)

/-- **The nilpotent Jordan block of size `n + 1`**: the truncated polynomial algebra `k[X]/(Xⁿ⁺¹)`
at the only vertex of `•↺`, with the loop acting by multiplication by `X`. -/
@[expose]
noncomputable def oneLoopNilpotentRep (n : ℕ) : QuiverRep.{u, 0, w, u} k Quiver.OneLoop :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))
      map := fun _ ↦
        ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1)))) }

variable {k}

/-- The vertex space of `TauCeti.oneLoopNilpotentRep` is `k[X]/(Xⁿ⁺¹)`. -/
@[simp]
theorem oneLoopNilpotentRep_obj (n : ℕ) (v : Paths Quiver.OneLoop) :
    (oneLoopNilpotentRep.{u, w} k n).obj v = ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

/-- The loop of `•↺` acts on `TauCeti.oneLoopNilpotentRep k n` by multiplication by the root. -/
theorem oneLoopNilpotentRep_map_loop (n : ℕ) :
    (oneLoopNilpotentRep.{u, w} k n).map (Quiver.Hom.toPath Quiver.OneLoop.loop) =
      ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1)))) :=
  Paths.lift_toPath _ _

/-- The action of the loop, read on an element of the vertex space. -/
@[simp]
theorem oneLoopNilpotentRep_map_loop_apply (n : ℕ) (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((oneLoopNilpotentRep.{u, w} k n).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x := by
  rw [oneLoopNilpotentRep_map_loop]
  rfl

/-- `TauCeti.oneLoopNilpotentRep k n` is finite-dimensional: its vertex space is `k[X]/(Xⁿ⁺¹)`. -/
theorem isFinDim_oneLoopNilpotentRep (n : ℕ) :
    IsFinDim k Quiver.OneLoop (oneLoopNilpotentRep.{u, w} k n) :=
  isFinDim_iff.mpr fun _ ↦ (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot

/-- The dimension vector of `TauCeti.oneLoopNilpotentRep k n` is `n + 1`. -/
theorem dimVector_oneLoopNilpotentRep (n : ℕ) (v : Quiver.OneLoop) :
    dimVector (oneLoopNilpotentRep.{u, w} k n) v = n + 1 := by
  rw [dimVector_apply, oneLoopNilpotentRep_obj]
  -- `AdjoinRoot f` *is* `k[X] ⧸ (f)`, so Mathlib's dimension formula for such a quotient applies.
  exact finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (n + 1))

/-- `TauCeti.oneLoopNilpotentRep k n` is nonzero: its vertex space is the nontrivial ring
`k[X]/(Xⁿ⁺¹)`. -/
theorem not_isZero_oneLoopNilpotentRep (n : ℕ) :
    ¬ IsZero (oneLoopNilpotentRep.{u, w} k n) := by
  intro h
  have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
    ModuleCat.subsingleton_of_isZero (h.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop))
  exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1)))

/-- The single component of an endomorphism of a nilpotent Jordan block, as a linear map on
`k[X]/(Xⁿ⁺¹)`. The quiver has one vertex, so a natural transformation is this one linear map. -/
private noncomputable def oneLoopNilpotentRepApp {n : ℕ}
    (f : oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n) :
    AdjoinRoot ((X : k[X]) ^ (n + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (n + 1)) :=
  (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom

/-- An endomorphism of a nilpotent Jordan block is determined by its single component. -/
private theorem oneLoopNilpotentRep_hom_ext {n : ℕ}
    {f g : oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n}
    (h : oneLoopNilpotentRepApp f = oneLoopNilpotentRepApp g) : f = g := by
  apply NatTrans.ext
  funext v
  cases v
  exact ModuleCat.hom_ext h

private theorem oneLoopNilpotentRepApp_zero {n : ℕ} :
    oneLoopNilpotentRepApp (0 : oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n)
      = 0 := (rfl)

private theorem oneLoopNilpotentRepApp_id {n : ℕ} :
    oneLoopNilpotentRepApp (𝟙 (oneLoopNilpotentRep.{u, w} k n)) = LinearMap.id := (rfl)

private theorem oneLoopNilpotentRepApp_comp {n : ℕ}
    (f g : oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n) :
    oneLoopNilpotentRepApp (f ≫ g) =
      (oneLoopNilpotentRepApp g).comp (oneLoopNilpotentRepApp f) := (rfl)

/-- Naturality along the loop: the component of an endomorphism commutes with multiplication by
the root. -/
private theorem oneLoopNilpotentRepApp_root_mul {n : ℕ}
    (f : oneLoopNilpotentRep.{u, w} k n ⟶ oneLoopNilpotentRep.{u, w} k n)
    (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    oneLoopNilpotentRepApp f (AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x) =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * oneLoopNilpotentRepApp f x := by
  -- Reading the naturality square at the element `x`; the two composites evaluate to the two
  -- nested applications below.
  have h : (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom
        (((oneLoopNilpotentRep.{u, w} k n).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom x) =
      ((oneLoopNilpotentRep.{u, w} k n).map (Quiver.Hom.toPath Quiver.OneLoop.loop)).hom
        ((f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x)
      (f.naturality (Quiver.Hom.toPath Quiver.OneLoop.loop))
  rw [oneLoopNilpotentRep_map_loop_apply] at h
  exact h.trans (oneLoopNilpotentRep_map_loop_apply.{u, w} n
    ((f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom x))

/-- **`TauCeti.oneLoopNilpotentRep k n` is indecomposable.** An endomorphism commutes with
multiplication by the root, hence is multiplication by its value at `1`
(`TauCeti.AdjoinRoot.eq_mulRight_of_root_mul`); if it is idempotent so is that value, and
`k[X]/(Xⁿ⁺¹)` is a
local ring (`TauCeti.isLocalRing_adjoinRoot_X_pow`), so its only idempotents are `0` and `1`. -/
theorem indecomposable_oneLoopNilpotentRep (n : ℕ) :
    Indecomposable (oneLoopNilpotentRep.{u, w} k n) := by
  refine indecomposable_of_idempotent_eq_zero_or_id (not_isZero_oneLoopNilpotentRep n) fun e he ↦ ?_
  have hmul : oneLoopNilpotentRepApp e = LinearMap.mulRight k (oneLoopNilpotentRepApp e 1) :=
    AdjoinRoot.eq_mulRight_of_root_mul (monic_X_pow (R := k) (n + 1))
      (oneLoopNilpotentRepApp_root_mul e)
  have hmul_apply : ∀ x, oneLoopNilpotentRepApp e x = x * oneLoopNilpotentRepApp e 1 := by
    intro x
    rw [hmul]
    simp
  have hidem : IsIdempotentElem (oneLoopNilpotentRepApp e 1) := by
    have h := congrArg (fun t ↦ oneLoopNilpotentRepApp t 1) he
    simp only [oneLoopNilpotentRepApp_comp, LinearMap.comp_apply] at h
    rw [hmul_apply (oneLoopNilpotentRepApp e 1)] at h
    exact h
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · refine Or.inl (oneLoopNilpotentRep_hom_ext ?_)
    rw [hmul, h0, oneLoopNilpotentRepApp_zero]
    exact LinearMap.ext fun x ↦ by simp
  · refine Or.inr (oneLoopNilpotentRep_hom_ext ?_)
    rw [hmul, h1, oneLoopNilpotentRepApp_id]
    exact LinearMap.ext fun x ↦ by simp

/-- **Nilpotent Jordan blocks of different sizes are non-isomorphic**: their dimension vectors
differ. -/
theorem eq_of_nonempty_oneLoopNilpotentRep_iso {m n : ℕ}
    (h : Nonempty (oneLoopNilpotentRep.{u, w} k m ≅ oneLoopNilpotentRep.{u, w} k n)) : m = n := by
  obtain ⟨e⟩ := h
  have hd := congrFun (dimVector_eq_of_iso e) Quiver.OneLoop.vertex
  rw [dimVector_oneLoopNilpotentRep, dimVector_oneLoopNilpotentRep] at hd
  omega

/-- Two nilpotent Jordan blocks are isomorphic exactly when their sizes agree. -/
@[simp]
theorem nonempty_oneLoopNilpotentRep_iso_iff {m n : ℕ} :
    Nonempty (oneLoopNilpotentRep.{u, w} k m ≅ oneLoopNilpotentRep.{u, w} k n) ↔ m = n :=
  ⟨eq_of_nonempty_oneLoopNilpotentRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

end Nilpotent

/-- **The loop quiver has infinite representation type over every field.** The nilpotent Jordan
blocks `TauCeti.oneLoopNilpotentRep k n` are finite-dimensional, indecomposable, and pairwise
non-isomorphic, so `ℕ` indexes an infinite family of them. -/
theorem not_isFiniteRepType_oneLoop (k : Type u) [Field k] :
    ¬ IsFiniteRepType.{u, 0, w, u} k Quiver.OneLoop :=
  not_isFiniteRepType_of_infinite (M := oneLoopNilpotentRep.{u, w} k) isFinDim_oneLoopNilpotentRep
    indecomposable_oneLoopNilpotentRep
    fun _ _ hne h ↦ hne (eq_of_nonempty_oneLoopNilpotentRep_iso h)

end TauCeti
