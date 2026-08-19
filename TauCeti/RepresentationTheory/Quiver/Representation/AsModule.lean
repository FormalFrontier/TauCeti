/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.OfModule
public import Mathlib.Algebra.DirectSum.Module

/-!
# The module over the path algebra carried by a representation of a quiver

`TauCeti.RepresentationTheory.Quiver.Representation.OfModule` turns a left module over the path
algebra `kQ` of a finite quiver into a representation of `Q`, and proves that functor **fully
faithful**.  This file supplies the other half: the `kQ`-module `TauCeti.QuiverRep.asModule`
carried by a representation, the identification of its vertex components with the vertex spaces of
the representation one started from, and hence the **essential surjectivity** that completes the
equivalence

`TauCeti.quiverRepEquivalence : QuiverRep k Q ≌ ModuleCat (pathAlgebra k Q)`.

## The construction

The carrier is the direct sum `⨁ᵥ Mᵥ` of the vertex spaces.  A basis path `p : a ⟶ b` of `kQ` acts
on it by the endomorphism `TauCeti.QuiverRep.pathEnd` that reads off the `a`-component, applies the
structure map `M.map p`, and puts the result in the `b`-component; two such endomorphisms compose
to the endomorphism of the concatenated path when the paths meet
(`TauCeti.QuiverRep.pathEnd_mul`) and to zero when they do not
(`TauCeti.QuiverRep.pathEnd_mul_eq_zero`), while the trivial paths give the component projections,
which sum to the identity (`TauCeti.QuiverRep.sum_pathEnd_nil`).  Extending linearly along the path
basis `TauCeti.pathAlgebraBasis` therefore gives an algebra homomorphism
`TauCeti.QuiverRep.toEnd : kQ →ₐ[k] End_k (⨁ᵥ Mᵥ)`, and `TauCeti.QuiverRep.asModule` is `⨁ᵥ Mᵥ`
with the module structure it induces.

With that in hand the vertex idempotent `eᵥ` acts as the composite of the projection to `Mᵥ` and
the inclusion back (`TauCeti.QuiverRep.vertexIdempotent_smul`), so the vertex component
`eᵥ · asModule` is exactly the image of `Mᵥ` (`TauCeti.QuiverRep.vertexComponent_asModule`) and the
inclusion is a `k`-linear isomorphism onto it.  Those isomorphisms are natural in the path, because
a path acts on the image of `Mₐ` through `M.map p` (`TauCeti.QuiverRep.smul_ofVertex`), which is
the natural isomorphism `TauCeti.QuiverRep.asModuleIso`.

## Main definitions

* `TauCeti.QuiverRep.vertexSpace`: the vector space a representation assigns to a vertex, as a bare
  type indexed by the vertices, with `TauCeti.QuiverRep.mapₗ` the structure maps between those.
* `TauCeti.QuiverRep.pathEnd`: the endomorphism of `⨁ᵥ Mᵥ` by which a basis path of `kQ` acts.
* `TauCeti.QuiverRep.toEndₗ` and `TauCeti.QuiverRep.toEnd`: that action extended along the path
  basis, first linearly and then as a `k`-algebra homomorphism into `End_k (⨁ᵥ Mᵥ)`.
* `TauCeti.QuiverRep.asModule`: **the `kQ`-module carried by a representation of `Q`**, the direct
  sum `⨁ᵥ Mᵥ` with the action of `TauCeti.QuiverRep.toEnd`.
* `TauCeti.QuiverRep.ofVertex` and `TauCeti.QuiverRep.toVertex`: the inclusion of a vertex space
  into that module and the projection onto it.
* `TauCeti.quiverRepEquivalence`: **representations of a quiver are modules over its path
  algebra.**

## Main results

* `TauCeti.QuiverRep.vertexIdempotent_smul`: the vertex idempotent `eᵥ` acts on `asModule` as the
  projection onto the summand `Mᵥ`, whence `TauCeti.QuiverRep.vertexComponent_asModule`: the vertex
  component of `asModule` at `v` is the image of `Mᵥ`.
* `TauCeti.QuiverRep.vertexComponentEquiv`: the vertex space `Mᵥ` is that vertex component, and
  `TauCeti.QuiverRep.pathMap_vertexComponentEquiv`: the identification is natural in the path.
* `TauCeti.QuiverRep.asModuleIso`: **the representation carried by `asModule M` is `M`**, so
  `TauCeti.quiverRepFunctor` is essentially surjective, and being fully faithful already it is an
  equivalence.  `TauCeti.QuiverRep.dimVector_asModule` records that the dimension vector is
  unchanged.

## Implementation notes

The vertex spaces are named as a family `TauCeti.QuiverRep.vertexSpace` rather than used as
`M.obj v` directly.  A representation is a functor out of `CategoryTheory.Paths Q`, whose objects
are vertices only after unfolding the semireducible `CategoryTheory.Paths`; instance search does
not see through that when it is asked for the *family* `∀ v : Q, AddCommMonoid (M.obj v)` that a
direct sum indexed by the vertices needs, although it succeeds at each individual vertex.  Naming
the family and giving it its two instances by `inferInstanceAs` is what makes `DirectSum Q` usable
here at all.  For the same reason the naturality square of `TauCeti.QuiverRep.asModuleIso` opens
with `change Q at a`, restating its quantified objects as vertices.

The `k`-module structure on `TauCeti.QuiverRep.asModule` is deliberately **not** the one the direct
sum already carries: it is `Module.restrictScalars k (pathAlgebra k Q)`, restriction of scalars
along `algebraMap`.  That is exactly the structure `ModuleCat.moduleOfAlgebraModule` puts on an
object of `ModuleCat (kQ)`, which is the one `TauCeti.quiverRepFunctor` uses; taking the direct
sum's own structure instead would give a second, only propositionally equal, `Module k` instance
and the essential-surjectivity isomorphism would not typecheck against the functor.  The two agree
by `TauCeti.QuiverRep.smul_asModule_k`, which is what upgrades the underlying additive equivalence
`TauCeti.QuiverRep.asModuleEquiv` to the `k`-linear `TauCeti.QuiverRep.asModuleLinearEquiv`.

`DecidableEq Q` is needed to write down the summand inclusions `DirectSum.lof`, so it is carried
through the construction; the essential-surjectivity instance is a `Prop` and discharges it with
`classical`, so neither it nor `TauCeti.quiverRepEquivalence` asks for it.

The universes are the reason the equivalence is stated for representations valued in
`ModuleCat.{max v t} k` for a vertex type in `Type v`: the direct sum of a `Type v`-indexed family
of `Type t`-modules lands in `Type (max v t)`, so a representation is carried by a module in that
universe and no smaller one.  For the usual case of a vertex type and vector spaces in the same
universe this is no restriction.

## References

This is the essential-surjectivity half of `quiverRepEquivalence`, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for the
equivalence "sending a module `M` to the representation `v ↦ eᵥ M`, with an arrow acting by left
multiplication, and inverting through the idempotent decomposition `M = ⨁ᵥ eᵥ M`"; the fully
faithful half is `TauCeti.quiverRepFunctorFullyFaithful`.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Ch. III, or R. Schiffler, *Quiver Representations*, Ch. 5.
-/

public section

namespace TauCeti

open CategoryTheory PathAlgebra

universe u v w t

namespace QuiverRep

section Vertex

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- The vertex space, as a bare type indexed by the vertices. -/
@[expose]
def vertexSpace (v : Q) : Type t := M.obj v

instance instAddCommGroupVertexSpace (v : Q) : AddCommGroup (vertexSpace k Q M v) :=
  inferInstanceAs (AddCommGroup (M.obj v))

instance instModuleVertexSpace (v : Q) : Module k (vertexSpace k Q M v) :=
  inferInstanceAs (Module k (M.obj v))

/-- The structure map of a representation along a path, retyped between vertex spaces. -/
noncomputable def mapₗ {a b : Q} (p : _root_.Quiver.Path a b) :
    vertexSpace k Q M a →ₗ[k] vertexSpace k Q M b := (M.map p).hom

-- Not `@[simp]`: `TauCeti.QuiverRep.mapₗ` is the simp-normal form of a structure map here, since
-- it is the retyping that lets the direct sum see the vertex spaces; rewriting with this would
-- undo that everywhere and take `TauCeti.QuiverRep.smul_ofVertex` and
-- `TauCeti.QuiverRep.pathMap_vertexComponentEquiv` out of simp normal form.
/-- The retyped structure map is the structure map. -/
theorem mapₗ_apply {a b : Q} (p : _root_.Quiver.Path a b) (z : vertexSpace k Q M a) :
    mapₗ k Q M p z = (M.map p) z := (rfl)

/-- **The trivial path acts as the identity**, the element-level
`TauCeti.QuiverRep.map_nil_apply` read as an equation of linear maps. -/
@[simp]
theorem mapₗ_nil (a : Q) : mapₗ k Q M (_root_.Quiver.Path.nil : _root_.Quiver.Path a a)
    = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  rw [mapₗ_apply, LinearMap.id_apply]
  exact QuiverRep.map_nil_apply M a z

/-- **Concatenation of paths composes the structure maps**, the functoriality of a representation
read on the retyped maps. -/
theorem mapₗ_comp {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path b c) :
    mapₗ k Q M (p.comp q) = (mapₗ k Q M q).comp (mapₗ k Q M p) := by
  refine LinearMap.ext fun z => ?_
  have h : M.map (p.comp q) = M.map p ≫ M.map q := M.map_comp p q
  rw [mapₗ_apply, h]
  rfl

end Vertex

section Basic

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [DecidableEq Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- The endomorphism of `⨁ᵥ Mᵥ` by which a path acts. -/
noncomputable def pathEnd (x : Quiver.TotalPath Q) :
    Module.End k (DirectSum Q (vertexSpace k Q M)) :=
  (DirectSum.lof k Q (vertexSpace k Q M) x.2.1).comp
    ((mapₗ k Q M x.2.2).comp (DirectSum.component k Q (vertexSpace k Q M) x.1))

/-- The endomorphism of a path reads off the component at its source, applies the structure map,
and puts the result in the component at its target. -/
theorem pathEnd_apply (x : Quiver.TotalPath Q) (z : DirectSum Q (vertexSpace k Q M)) :
    pathEnd k Q M x z = DirectSum.lof k Q (vertexSpace k Q M) x.2.1
      (mapₗ k Q M x.2.2 (DirectSum.component k Q (vertexSpace k Q M) x.1 z)) := (rfl)

/-- `TauCeti.QuiverRep.pathEnd_apply` on a path given by its source, target and underlying path,
the form in which the endpoints are available for rewriting. -/
theorem pathEnd_mk_apply {a b : Q} (p : _root_.Quiver.Path a b)
    (z : DirectSum Q (vertexSpace k Q M)) :
    pathEnd k Q M ⟨a, b, p⟩ z = DirectSum.lof k Q (vertexSpace k Q M) b
      (mapₗ k Q M p (DirectSum.component k Q (vertexSpace k Q M) a z)) := (rfl)

/-- **Composable paths compose**: the endomorphisms of two paths that meet multiply to the
endomorphism of their concatenation, later factor first, as the path algebra multiplies them. -/
theorem pathEnd_mul {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path c a) :
    pathEnd k Q M ⟨a, b, p⟩ * pathEnd k Q M ⟨c, a, q⟩ = pathEnd k Q M ⟨c, b, q.comp p⟩ := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, pathEnd_mk_apply, pathEnd_mk_apply, pathEnd_mk_apply,
    mapₗ_comp k Q M q p]
  exact congrArg _ (congrArg _ (DirectSum.component.lof_self k a _))

/-- **Paths that do not meet annihilate one another**, because the second lands in a summand the
first reads as zero. This is the other half of the multiplicativity of
`TauCeti.QuiverRep.toEnd`. -/
theorem pathEnd_mul_eq_zero {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    pathEnd k Q M x * pathEnd k Q M y = 0 := by
  refine LinearMap.ext fun z => ?_
  have key : DirectSum.component k Q (vertexSpace k Q M) x.1 (pathEnd k Q M y z) = 0 := by
    rw [pathEnd_apply]
    -- the projection onto a summand kills every other summand
    exact (DirectSum.component.of k x.1 y.2.1 _).trans (dite_eq_right h)
  rw [Module.End.mul_apply, pathEnd_apply, key, map_zero, map_zero, LinearMap.zero_apply]

/-- **The trivial paths give the summand projections**, and those sum to the identity: this is what
makes `TauCeti.QuiverRep.toEnd` unital, the unit of the path algebra being the sum of the vertex
idempotents. -/
theorem sum_pathEnd_nil [Fintype Q] :
    ∑ v : Q, pathEnd k Q M ⟨v, v, _root_.Quiver.Path.nil⟩ = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.sum_apply]
  simp only [pathEnd_apply, mapₗ_nil, LinearMap.id_coe, id_eq,
    ← DirectSum.apply_eq_component, Module.End.one_apply, DirectSum.lof_eq_of]
  exact DirectSum.sum_univ_of z

/-- The action of the path algebra on `⨁ᵥ Mᵥ`, as a linear map. -/
noncomputable def toEndₗ :
    pathAlgebra k Q →ₗ[k] Module.End k (DirectSum Q (vertexSpace k Q M)) :=
  (pathAlgebraBasis k Q).constr k (pathEnd k Q M)

/-- The action of a basis path is the endomorphism it was assigned. -/
@[simp]
theorem toEndₗ_ofPath (x : Quiver.TotalPath Q) :
    toEndₗ k Q M (ofPath x) = pathEnd k Q M x := by
  have h := (pathAlgebraBasis k Q).constr_basis k (pathEnd k Q M) x
  rwa [coe_pathAlgebraBasis] at h

/-- The action of a scaled basis path scales its endomorphism. -/
theorem toEndₗ_single (x : Quiver.TotalPath Q) (c : k) :
    toEndₗ k Q M (single x c) = c • pathEnd k Q M x := by
  have hx : (single x c : pathAlgebra k Q) = c • ofPath x := by
    rw [ofPath_eq_single, smul_single, mul_one]
  rw [hx, map_smul, toEndₗ_ofPath]

/-- The action of a vertex idempotent is the endomorphism of the trivial path there, which by
`TauCeti.QuiverRep.mapₗ_nil` is the projection onto that summand. -/
theorem toEndₗ_vertexIdempotent (v : Q) :
    toEndₗ k Q M (vertexIdempotent k v) = pathEnd k Q M ⟨v, v, _root_.Quiver.Path.nil⟩ := by
  rw [vertexIdempotent_eq_single, toEndₗ_single, one_smul]

/-- **The action is multiplicative**, by `TauCeti.QuiverRep.pathEnd_mul` on composable basis paths
and `TauCeti.QuiverRep.pathEnd_mul_eq_zero` on the rest. -/
theorem toEndₗ_mul (f g : pathAlgebra k Q) :
    toEndₗ k Q M (f * g) = toEndₗ k Q M f * toEndₗ k Q M g := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | single x c =>
    induction g using PathAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | single y d =>
      obtain ⟨a, b, p⟩ := x
      obtain ⟨c', a', q⟩ := y
      by_cases hy : a' = a
      · subst hy
        rw [single_mul_single_of_comp, toEndₗ_single, toEndₗ_single, toEndₗ_single,
          smul_mul_smul_comm, pathEnd_mul]
      · rw [single_mul_single_of_not_composable hy, map_zero, toEndₗ_single, toEndₗ_single,
          smul_mul_smul_comm, pathEnd_mul_eq_zero k Q M hy, smul_zero]

end Basic

section Algebra

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q] [DecidableEq Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- **The action is unital**: the unit of the path algebra is the sum of the vertex idempotents,
whose endomorphisms are the summand projections. -/
theorem toEndₗ_one : toEndₗ k Q M 1 = 1 := by
  let _ := Fintype.ofFinite Q
  rw [one_def, map_sum]
  simp only [toEndₗ_vertexIdempotent]
  exact sum_pathEnd_nil k Q M

/-- The action of the path algebra on `⨁ᵥ Mᵥ`, as an algebra map. -/
noncomputable def toEnd : pathAlgebra k Q →ₐ[k] Module.End k (DirectSum Q (vertexSpace k Q M)) :=
  AlgHom.mk'
    { toFun := toEndₗ k Q M
      map_one' := toEndₗ_one k Q M
      map_mul' := toEndₗ_mul k Q M
      map_zero' := map_zero _
      map_add' := fun f g => map_add _ f g }
    fun c x => (toEndₗ k Q M).map_smul c x

/-- The algebra map acts by the linear map it was built from. -/
@[simp]
theorem toEnd_apply (f : pathAlgebra k Q) : toEnd k Q M f = toEndₗ k Q M f := (rfl)

/-- The module over the path algebra carried by a representation of `Q`. -/
@[expose]
def asModule : Type max v t := DirectSum Q (vertexSpace k Q M)

instance : AddCommGroup (asModule k Q M) :=
  inferInstanceAs (AddCommGroup (DirectSum Q (vertexSpace k Q M)))

/-- **The defining `kQ`-action**: the path algebra acts on `⨁ᵥ Mᵥ` through the algebra map
`TauCeti.QuiverRep.toEnd` into its `k`-linear endomorphisms. -/
noncomputable instance : Module (pathAlgebra k Q) (asModule k Q M) :=
  Module.compHom (DirectSum Q (vertexSpace k Q M)) (toEnd k Q M).toRingHom

/-- The `k`-action, by restriction of scalars along `algebraMap k (kQ)` — deliberately *not* the
direct sum's own `k`-action, though `TauCeti.QuiverRep.smul_asModule_k` says the two agree; see the
implementation notes. -/
noncomputable instance : Module k (asModule k Q M) :=
  Module.restrictScalars k (pathAlgebra k Q) (asModule k Q M)

/-- The `k`-action on `TauCeti.QuiverRep.asModule` is the restriction of the `kQ`-action, so the
two are compatible by construction. -/
instance : IsScalarTower k (pathAlgebra k Q) (asModule k Q M) :=
  IsScalarTower.restrictScalars k (pathAlgebra k Q) (asModule k Q M)

/-- The additive equivalence identifying `TauCeti.QuiverRep.asModule` with the direct sum `⨁ᵥ Mᵥ`
underlying it. -/
@[expose]
def asModuleEquiv : asModule k Q M ≃+ DirectSum Q (vertexSpace k Q M) := AddEquiv.refl _

/-- The defining action on `TauCeti.QuiverRep.asModule`: an element of the path algebra acts
through `TauCeti.QuiverRep.toEnd`. -/
theorem smul_asModule_def (f : pathAlgebra k Q) (x : asModule k Q M) :
    f • x = toEnd k Q M f (asModuleEquiv k Q M x) := (rfl)

/-- **The two `k`-actions agree**: the restriction of scalars along `algebraMap k (kQ)` that
`TauCeti.QuiverRep.asModule` carries is the direct sum's own `k`-action, because
`TauCeti.QuiverRep.toEnd` is a `k`-algebra map. This is what makes
`TauCeti.QuiverRep.asModuleLinearEquiv` `k`-linear. -/
theorem smul_asModule_k (r : k) (x : asModule k Q M) :
    asModuleEquiv k Q M (r • x) = r • asModuleEquiv k Q M x := by
  change asModuleEquiv k Q M ((algebraMap k (pathAlgebra k Q) r) • x) = _
  rw [smul_asModule_def, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The underlying direct sum of the module carried by a representation, `k`-linearly. -/
noncomputable def asModuleLinearEquiv :
    asModule k Q M ≃ₗ[k] DirectSum Q (vertexSpace k Q M) :=
  { asModuleEquiv k Q M with map_smul' := smul_asModule_k k Q M }

/-- The `k`-linear identification with the underlying direct sum is the additive one. -/
@[simp]
theorem asModuleLinearEquiv_apply (x : asModule k Q M) :
    asModuleLinearEquiv k Q M x = asModuleEquiv k Q M x := (rfl)

/-- The inclusion of a vertex space into the module carried by a representation. -/
noncomputable def ofVertex (v : Q) : vertexSpace k Q M v →ₗ[k] asModule k Q M :=
  (asModuleLinearEquiv k Q M).symm.toLinearMap.comp (DirectSum.lof k Q (vertexSpace k Q M) v)

/-- The projection of the module carried by a representation onto a vertex space. -/
noncomputable def toVertex (v : Q) : asModule k Q M →ₗ[k] vertexSpace k Q M v :=
  (DirectSum.component k Q (vertexSpace k Q M) v).comp
    (asModuleLinearEquiv k Q M).toLinearMap

/-- The inclusion of a vertex space is the inclusion of the corresponding summand. -/
@[simp]
theorem asModuleEquiv_ofVertex (v : Q) (z : vertexSpace k Q M v) :
    asModuleEquiv k Q M (ofVertex k Q M v z) = DirectSum.lof k Q (vertexSpace k Q M) v z := (rfl)

/-- The projection onto a vertex space undoes its inclusion. -/
@[simp]
theorem toVertex_ofVertex (v : Q) (z : vertexSpace k Q M v) :
    toVertex k Q M v (ofVertex k Q M v z) = z :=
  DirectSum.component.lof_self k v z

/-- The inclusion of a vertex space is injective. -/
theorem ofVertex_injective (v : Q) : Function.Injective (ofVertex k Q M v) :=
  Function.LeftInverse.injective (toVertex_ofVertex k Q M v)

/-- **A path acts on the image of its source through the structure map**: this is the naturality
that makes `TauCeti.QuiverRep.asModuleIso` a morphism of representations. -/
theorem smul_ofVertex {a b : Q} (p : _root_.Quiver.Path a b) (z : vertexSpace k Q M a) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • ofVertex k Q M a z
      = ofVertex k Q M b (mapₗ k Q M p z) := by
  apply (asModuleEquiv k Q M).injective
  rw [smul_asModule_def, toEnd_apply, toEndₗ_ofPath, pathEnd_mk_apply, asModuleEquiv_ofVertex,
    asModuleEquiv_ofVertex]
  exact congrArg (fun y => DirectSum.lof k Q (vertexSpace k Q M) b (mapₗ k Q M p y))
    (DirectSum.component.lof_self k a z)

/-- **The vertex idempotent acts as the projection onto its summand**, the fact from which the
vertex component of `TauCeti.QuiverRep.asModule` is read off. -/
@[simp]
theorem vertexIdempotent_smul (v : Q) (x : asModule k Q M) :
    (vertexIdempotent k v : pathAlgebra k Q) • x = ofVertex k Q M v (toVertex k Q M v x) := by
  apply (asModuleEquiv k Q M).injective
  rw [smul_asModule_def, toEnd_apply, toEndₗ_vertexIdempotent, pathEnd_mk_apply,
    asModuleEquiv_ofVertex, mapₗ_nil]
  rfl

/-- **The vertex component is the image of the vertex space**: the piece of
`TauCeti.QuiverRep.asModule` that the vertex idempotent fixes is the summand `Mᵥ`. -/
theorem vertexComponent_asModule (v : Q) :
    vertexComponent k (asModule k Q M) v = LinearMap.range (ofVertex k Q M v) := by
  ext x
  rw [mem_vertexComponent_iff_smul_eq_self, vertexIdempotent_smul, LinearMap.mem_range]
  constructor
  · exact fun h => ⟨toVertex k Q M v x, h⟩
  · rintro ⟨z, rfl⟩
    rw [toVertex_ofVertex]

/-- The vertex space of a representation is the vertex component of the module it carries. -/
noncomputable def vertexComponentEquiv (v : Q) :
    vertexSpace k Q M v ≃ₗ[k] vertexComponent k (asModule k Q M) v :=
  (LinearEquiv.ofInjective _ (ofVertex_injective k Q M v)).trans
    (LinearEquiv.ofEq _ _ (vertexComponent_asModule k Q M v).symm)

/-- The identification of a vertex space with a vertex component is the inclusion of the
summand. -/
@[simp]
theorem coe_vertexComponentEquiv (v : Q) (z : vertexSpace k Q M v) :
    (vertexComponentEquiv k Q M v z : asModule k Q M) = ofVertex k Q M v z := (rfl)

/-- **The identification is natural in the path**: the action of a path on the vertex components of
`TauCeti.QuiverRep.asModule` is the structure map of the representation. -/
@[simp]
theorem pathMap_vertexComponentEquiv {a b : Q} (p : _root_.Quiver.Path a b)
    (z : vertexSpace k Q M a) :
    pathMap k (asModule k Q M) p (vertexComponentEquiv k Q M a z)
      = vertexComponentEquiv k Q M b (mapₗ k Q M p z) := by
  apply Subtype.ext
  rw [coe_pathMap_apply, coe_vertexComponentEquiv, coe_vertexComponentEquiv, smul_ofVertex]

end Algebra

section EssSurj

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q] [DecidableEq Q]
variable (M : QuiverRep.{u, v, w, max v t} k Q)

/-- **Essential surjectivity, as an isomorphism**: the representation carried by the module
carried by `M` is `M` again. -/
noncomputable def asModuleIso : quiverRepOfModule k Q (asModule k Q M) ≅ M :=
  NatIso.ofComponents (fun a => (vertexComponentEquiv k Q M a).toModuleIso.symm)
    (fun {a b} p => by
      change Q at a
      change Q at b
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      -- both sides of the naturality square are `ModuleCat.ofHom` of a composite of a structure
      -- map with a `LinearEquiv.toModuleIso`, and the bundling is definitional: no rewrite lemma
      -- states the elementwise form, because `ModuleCat.hom_comp` and
      -- `LinearEquiv.toModuleIso_symm_hom` fire only on the unapplied morphisms, leaving the
      -- coercions to unfold anyway. `change` names the elementwise goal in one step.
      change (vertexComponentEquiv k Q M b).symm (pathMap k (asModule k Q M) p x)
        = mapₗ k Q M p ((vertexComponentEquiv k Q M a).symm x)
      rw [LinearEquiv.symm_apply_eq, ← pathMap_vertexComponentEquiv]
      exact congrArg _ ((vertexComponentEquiv k Q M a).apply_symm_apply x).symm)

/-- **The dimension vector is unchanged** by passing to the module a representation carries and
back. -/
theorem dimVector_asModule :
    dimVector (quiverRepOfModule k Q (asModule k Q M)) = dimVector M :=
  dimVector_eq_of_iso (asModuleIso k Q M)

end EssSurj

section Equivalence

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- **The module-to-representation functor is essentially surjective**: every representation is
carried by the `kQ`-module `TauCeti.QuiverRep.asModule` built from it. -/
instance : (quiverRepFunctor.{u, v, w, max v t} k Q).EssSurj where
  mem_essImage M := by
    classical
    exact ⟨ModuleCat.of (pathAlgebra k Q) (asModule k Q M), ⟨asModuleIso k Q M⟩⟩

/-- **The module-to-representation functor is an equivalence**: it is fully faithful by
`TauCeti.quiverRepFunctorFullyFaithful` and essentially surjective by the instance above. -/
instance : (quiverRepFunctor.{u, v, w, max v t} k Q).IsEquivalence where

/-- **Representations of a quiver are modules over its path algebra.** -/
noncomputable def _root_.TauCeti.quiverRepEquivalence :
    QuiverRep.{u, v, w, max v t} k Q ≌ ModuleCat.{max v t} (pathAlgebra k Q) :=
  (quiverRepFunctor.{u, v, w, max v t} k Q).asEquivalence.symm

/-- The inverse of `TauCeti.quiverRepEquivalence` is `TauCeti.quiverRepFunctor`: the equivalence is
the module-to-representation functor of
`TauCeti.RepresentationTheory.Quiver.Representation.OfModule`, turned around. -/
theorem _root_.TauCeti.quiverRepEquivalence_inverse :
    (quiverRepEquivalence.{u, v, w, t} k Q).inverse = quiverRepFunctor k Q := (rfl)

end Equivalence

end QuiverRep

end TauCeti
