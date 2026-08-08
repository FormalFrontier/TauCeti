/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra
public import TauCeti.RingTheory.Idempotents.Module

/-!
# A module over a path algebra is a representation of the quiver

A left module `M` over the path algebra `kQ` of a finite quiver carries one `k`-subspace for each
vertex, `Mᵥ = eᵥ M`, and one `k`-linear map for each path, the action of that path. This file
builds that data and proves the three facts that make it a representation of `Q`:

* the vertex subspaces are an internal direct sum, `M = ⨁ᵥ eᵥ M`
  (`TauCeti.isInternal_vertexComponent`);
* a path from `a` to `b` carries `Mₐ` into `M_b` and annihilates every other vertex subspace
  (`TauCeti.ofPath_smul_mem_vertexComponent`,
  `TauCeti.ofPath_smul_eq_zero_of_mem_vertexComponent`);
* the resulting maps are functorial in the path (`TauCeti.pathMap_nil`,
  `TauCeti.pathMap_comp`) and in the module (`TauCeti.vertexComponentMap_id`,
  `TauCeti.vertexComponentMap_comp`), the two being compatible
  (`TauCeti.vertexComponentMap_comp_pathMap`).

This is the direction "module ↦ representation" of the equivalence between representations of `Q`
and left `kQ`-modules; the vertex idempotents are what makes it work, and the finiteness of the
vertex set is load-bearing, being what makes `∑ᵥ eᵥ = 1` a finite sum and `kQ` unital.

The orientation is fixed by the *later factor first* product of `TauCeti.pathAlgebra`: with it,
`e_b · p = p` and `p · eₐ = p` for a path `p` from `a` to `b`, so left multiplication by `p` sends
the component at the **source** to the component at the **target**, and the representations
obtained here are the covariant ones. Reversing the product would transpose every statement below.

## Implementation notes

Only the underlying data and its functoriality are built here: no object of
`TauCeti.QuiverRep k Q` (`Paths Q ⥤ ModuleCat k`, in
`TauCeti.RepresentationTheory.Quiver.Representation.Basic`) and no functor into it is assembled,
and `TauCeti.dimVector` is not used. Two things are missing for that. First, `QuiverRep` is stated
over a `Field k` while everything below needs only a `CommSemiring k`, so assembling the functor
here would either restrict the results or duplicate them. Second, the assembly is the roadmap
target `quiverRepEquivalence` itself, of which this file is the object-and-morphism half.

## Main definitions

* `TauCeti.vertexComponent k M v`: the `k`-subspace `eᵥ M` of a `kQ`-module `M`.
* `TauCeti.pathMap k M p`: the `k`-linear map `Mₐ → M_b` given by the action of a path
  `p` from `a` to `b`.
* `TauCeti.vertexComponentMap k f v`: the restriction of a `kQ`-linear map to the components at
  `v`.

## Main results

* `TauCeti.isInternal_vertexComponent`: `M = ⨁ᵥ eᵥ M`, with
  `TauCeti.coe_isInternal_vertexComponent_symm_apply` reading off the component of `x` at `v` as
  `eᵥ • x`.
* `TauCeti.finrank_eq_sum_finrank_vertexComponent`: for a `kQ`-module finite-dimensional over a
  field `k`, the dimension of `M` is the sum of the dimensions of the vertex subspaces — the total
  dimension read off the dimension vector.
* `TauCeti.pathMap_nil` and `TauCeti.pathMap_comp`: the path maps are functorial, the trivial path
  acting as the identity and a concatenation as the composite.
* `TauCeti.vertexComponentMap_comp_pathMap`: the path maps are natural in the module.

## References

Layer 1 of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose
`quiverRepEquivalence` "sends a module `M` to the representation `v ↦ eᵥ M`, with an arrow acting
by left multiplication, and inverts through the idempotent decomposition `M = ⨁ᵥ eᵥ M` (available
because `∑ᵥ eᵥ = 1`, hence the finiteness of the vertex set is load-bearing here)".

The equivalence itself is classical; see Assem--Simson--Skowroński, *Elements of the Representation
Theory of Associative Algebras I*, Ch. III, or Schiffler, *Quiver Representations*, Ch. 5.
-/

public section

namespace TauCeti

open PathAlgebra

open scoped DirectSum

section Component

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M]

/-- The **vertex component** `eᵥ M` of a module over the path algebra: the `k`-subspace on which
the vertex idempotent at `v` acts as the identity. It is the value at `v` of the representation of
`Q` attached to `M`. -/
noncomputable def vertexComponent (v : Q) : Submodule k M :=
  smulRange k M (vertexIdempotent k v)

/-- The vertex component is the piece cut out by the vertex idempotent, so the general API of
`TauCeti.smulRange` applies to it. -/
theorem vertexComponent_eq_smulRange (v : Q) :
    vertexComponent k M v = smulRange k M (vertexIdempotent k v) := (rfl)

variable {k M}

/-- Membership in `eᵥ M` is the fixed-point condition for the vertex idempotent. -/
@[simp]
theorem mem_vertexComponent_iff_smul_eq_self {v : Q} {x : M} :
    x ∈ vertexComponent k M v ↔ (vertexIdempotent k v : pathAlgebra k Q) • x = x :=
  mem_smulRange_iff_smul_eq_self (vertexIdempotent_mul_self v)

/-- The vertex idempotent fixes its own component. -/
theorem vertexIdempotent_smul_eq_self_of_mem_vertexComponent {v : Q} {x : M}
    (hx : x ∈ vertexComponent k M v) : (vertexIdempotent k v : pathAlgebra k Q) • x = x :=
  mem_vertexComponent_iff_smul_eq_self.1 hx

/-- **A path lands in the component of its target.** Together with
`TauCeti.ofPath_smul_eq_zero_of_mem_vertexComponent` this says that a path from `a` to `b` acts as
a map from the component at its *source* to the component at its *target*, which is the
orientation the *later factor first* product of the path algebra was chosen to produce. -/
theorem ofPath_smul_mem_vertexComponent {a b : Q} (p : _root_.Quiver.Path a b) (x : M) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • x ∈ vertexComponent k M b :=
  smul_mem_smulRange_of_mul_eq_self (vertexIdempotent_mul_ofPath p) x

/-- **A path annihilates every vertex component but that of its source.** -/
theorem ofPath_smul_eq_zero_of_mem_vertexComponent {a b c : Q} (p : _root_.Quiver.Path a b)
    (h : c ≠ a) {x : M} (hx : x ∈ vertexComponent k M c) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • x = 0 :=
  smul_eq_zero_of_mul_eq_zero_of_mem_smulRange (ofPath_mul_vertexIdempotent_of_ne _ h) hx

variable (k M)

/-- The `k`-linear map `eₐ M → e_b M` given by the action of a path from `a` to `b`. These are the
structure maps of the representation of `Q` attached to `M`. -/
noncomputable def pathMap {a b : Q} (p : _root_.Quiver.Path a b) :
    vertexComponent k M a →ₗ[k] vertexComponent k M b where
  toFun x := ⟨(ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • (x : M),
    ofPath_smul_mem_vertexComponent p (x : M)⟩
  map_add' x y := Subtype.ext (smul_add _ (x : M) (y : M))
  map_smul' r x := Subtype.ext (smul_comm (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) r (x : M))

@[simp]
theorem coe_pathMap_apply {a b : Q} (p : _root_.Quiver.Path a b)
    (x : vertexComponent k M a) :
    (pathMap k M p x : M) = (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • (x : M) :=
  (rfl)

/-- **The trivial path acts as the identity.** -/
@[simp]
theorem pathMap_nil (a : Q) :
    pathMap k M (_root_.Quiver.Path.nil : _root_.Quiver.Path a a) = LinearMap.id := by
  ext x
  rw [coe_pathMap_apply, ← vertexIdempotent_eq_ofPath,
    vertexIdempotent_smul_eq_self_of_mem_vertexComponent x.2]
  simp

/-- **Concatenation of paths is composition of the maps they act by.** Together with
`TauCeti.pathMap_nil` this says that the assignment `v ↦ eᵥ M` is functorial in the path. -/
@[simp]
theorem pathMap_comp {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path b c) :
    pathMap k M (p.comp q) = (pathMap k M q).comp (pathMap k M p) := by
  ext x
  simp only [coe_pathMap_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [smul_smul, ofPath_mul_ofPath_of_comp q p]

/-- The composition law in the form paths are destructured: extending `p` by an arrow `f` composes
the map of `p` with that of `f`. -/
@[simp]
theorem pathMap_cons {a b c : Q} (p : _root_.Quiver.Path a b) (f : b ⟶ c) :
    pathMap k M (p.cons f) = (pathMap k M f.toPath).comp (pathMap k M p) := by
  rw [← _root_.Quiver.Path.comp_toPath_eq_cons, pathMap_comp]

end Component

section Naturality

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]
variable {M N P : Type*} [AddCommMonoid M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M] [AddCommMonoid N] [Module k N]
  [Module (pathAlgebra k Q) N] [IsScalarTower k (pathAlgebra k Q) N] [AddCommMonoid P]
  [Module k P] [Module (pathAlgebra k Q) P] [IsScalarTower k (pathAlgebra k Q) P]

/-- A `kQ`-linear map restricts to a `k`-linear map between the components at each vertex: it
commutes with the action of `eᵥ`, so it preserves the fixed points of `eᵥ`. This is
`TauCeti.smulRangeMap` at the vertex idempotent. -/
noncomputable def vertexComponentMap (f : M →ₗ[pathAlgebra k Q] N) (v : Q) :
    vertexComponent k M v →ₗ[k] vertexComponent k N v :=
  smulRangeMap k (vertexIdempotent k v) f

@[simp]
theorem coe_vertexComponentMap_apply (f : M →ₗ[pathAlgebra k Q] N) (v : Q)
    (x : vertexComponent k M v) : (vertexComponentMap k f v x : N) = f (x : M) :=
  coe_smulRangeMap_apply _ f x

/-- **The restriction to the components is functorial**: the identity restricts to the identity.
This is `TauCeti.smulRangeMap_id` at the vertex idempotent. -/
@[simp]
theorem vertexComponentMap_id (v : Q) :
    vertexComponentMap k (LinearMap.id : M →ₗ[pathAlgebra k Q] M) v = LinearMap.id :=
  smulRangeMap_id _

/-- **The restriction to the components is functorial**: a composite restricts to the composite of
the restrictions. This is `TauCeti.smulRangeMap_comp` at the vertex idempotent. -/
@[simp]
theorem vertexComponentMap_comp (g : N →ₗ[pathAlgebra k Q] P) (f : M →ₗ[pathAlgebra k Q] N)
    (v : Q) :
    vertexComponentMap k (g.comp f) v
      = (vertexComponentMap k g v).comp (vertexComponentMap k f v) :=
  smulRangeMap_comp _ g f

/-- **The path maps are natural in the module**: restricting a `kQ`-linear map to the vertex
components commutes with the action of every path. This is the morphism half of the passage from
`kQ`-modules to representations of `Q`. -/
@[simp]
theorem vertexComponentMap_comp_pathMap (f : M →ₗ[pathAlgebra k Q] N) {a b : Q}
    (p : _root_.Quiver.Path a b) :
    (vertexComponentMap k f b).comp (pathMap k M p)
      = (pathMap k N p).comp (vertexComponentMap k f a) := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, coe_vertexComponentMap_apply,
    coe_pathMap_apply]
  exact map_smul f _ (x : M)

end Naturality

section Internal

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q] [DecidableEq Q]
variable (M : Type*) [AddCommMonoid M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M]

/-- **A module over the path algebra is the direct sum of its vertex components**, `M = ⨁ᵥ eᵥ M`.
The component of `x` at `v` is `eᵥ • x`, and the decomposition is the one the identity
`∑ᵥ eᵥ = 1` provides. -/
theorem isInternal_vertexComponent :
    DirectSum.IsInternal fun v : Q => vertexComponent k M v := by
  let := Fintype.ofFinite Q
  exact isInternal_smulRange (completeOrthogonalIdempotents_vertexIdempotent k Q)

/-- **The component of `x` at `v` is `eᵥ • x`**: the inverse of the decomposition, read off one
vertex at a time. This is the fact the roadmap's inversion of `quiverRepEquivalence` runs on. -/
@[simp]
theorem coe_isInternal_vertexComponent_symm_apply (x : M) (v : Q) :
    (((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun w : Q => vertexComponent k M w)
        (isInternal_vertexComponent k M)).symm x v : vertexComponent k M v) : M)
      = (vertexIdempotent k v : pathAlgebra k Q) • x := by
  let := Fintype.ofFinite Q
  exact coe_isInternal_smulRange_symm_apply (completeOrthogonalIdempotents_vertexIdempotent k Q)
    x v

end Internal

section Finrank

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M] [Module.Finite k M]

/-- **The dimension of a finite-dimensional `kQ`-module is the sum of the dimensions of its vertex
components**: the total dimension is read off the dimension vector `v ↦ dim (eᵥ M)`. -/
theorem finrank_eq_sum_finrank_vertexComponent :
    Module.finrank k M = ∑ v : Q, Module.finrank k (vertexComponent k M v : Submodule k M) :=
  finrank_eq_sum_finrank_smulRange (completeOrthogonalIdempotents_vertexIdempotent k Q)

end Finrank

end TauCeti
