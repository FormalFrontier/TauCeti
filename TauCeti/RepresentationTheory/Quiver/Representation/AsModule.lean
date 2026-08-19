/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.OfModule
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Shrink

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
(`TauCeti.QuiverRep.pathEnd_mul_pathEnd_of_comp`) and to zero when they do not
(`TauCeti.QuiverRep.pathEnd_mul_pathEnd_of_not_composable`), while the trivial paths give the
component projections, which sum to the identity (`TauCeti.QuiverRep.sum_pathEnd_nil`).  Those are
exactly the three hypotheses of the universal property `TauCeti.PathAlgebra.liftAlgHom`, so the
assignment extends to an algebra homomorphism
`TauCeti.QuiverRep.toEnd : kQ →ₐ[k] End_k (⨁ᵥ Mᵥ)`, and `TauCeti.QuiverRep.asModule` is `⨁ᵥ Mᵥ`
with the module structure it induces.

With that in hand the vertex idempotent `eᵥ` acts as the composite of the projection to `Mᵥ` and
the inclusion back (`TauCeti.QuiverRep.vertexIdempotent_smul`), so the vertex component
`eᵥ · asModule` is exactly the image of `Mᵥ` (`TauCeti.QuiverRep.vertexComponent_asModule`) and the
inclusion is a `k`-linear isomorphism onto it, `TauCeti.QuiverRep.vertexComponentEquiv`.  Those
isomorphisms are natural in the path, because a path acts on the image of `Mₐ` through `M.map p`
(`TauCeti.QuiverRep.smul_ofVertex`, whence
`TauCeti.QuiverRep.pathMap_vertexComponentEquiv`); assembling them with
`CategoryTheory.NatIso.ofComponents` gives the natural isomorphism
`TauCeti.QuiverRep.asModuleIso`.  Transported to the model
`TauCeti.QuiverRep.asModuleShrink` of the carrier in the universe of the representation itself,
that isomorphism becomes `TauCeti.QuiverRep.asModuleShrinkIso`, the essential surjectivity of
`TauCeti.quiverRepFunctor`.

## Main definitions

* `TauCeti.QuiverRep.pathEnd`: the endomorphism of `⨁ᵥ Mᵥ` by which a basis path of `kQ` acts, and
  `TauCeti.QuiverRep.toEnd`: that action extended along the path basis as a `k`-algebra
  homomorphism into `End_k (⨁ᵥ Mᵥ)`.
* `TauCeti.QuiverRep.asModule`: **the `kQ`-module carried by a representation of `Q`**, the direct
  sum `⨁ᵥ Mᵥ` with the action of `TauCeti.QuiverRep.toEnd`.
* `TauCeti.QuiverRep.ofVertex` and `TauCeti.QuiverRep.toVertex`: the inclusion of a vertex space
  into that module and the projection onto it.
* `TauCeti.QuiverRep.asModuleShrink`: the model of that module in the universe of the
  representation, `TauCeti.QuiverRep.asModuleShrinkEquiv` identifying the two.
* `TauCeti.quiverRepEquivalence`: **representations of a quiver are modules over its path
  algebra**, with `TauCeti.quiverRepEquivalenceFunctorObjIso` identifying the module it sends a
  representation to with `TauCeti.QuiverRep.asModule`.

## Main results

* `TauCeti.QuiverRep.smul_ofPath`: a basis path acts on `asModule` by reading off the component at
  its source, applying the structure map and putting the result in the component at its target;
  the two cases used below are `TauCeti.QuiverRep.smul_ofVertex` and
  `TauCeti.QuiverRep.vertexIdempotent_smul`, the latter saying that the vertex idempotent `eᵥ` acts
  as the projection onto the summand `Mᵥ`, whence
  `TauCeti.QuiverRep.vertexComponent_asModule`: the vertex component of `asModule` at `v` is the
  image of `Mᵥ`.
* `TauCeti.QuiverRep.vertexComponentEquiv`: the vertex space `Mᵥ` is that vertex component, and
  `TauCeti.QuiverRep.pathMap_vertexComponentEquiv`: the identification is natural in the path.
* `TauCeti.QuiverRep.asModuleIso`: **the representation carried by `asModule M` is `M`**, whence
  `TauCeti.QuiverRep.asModuleShrinkIso` says the same of the small model, so
  `TauCeti.quiverRepFunctor` is essentially surjective, and being fully faithful already it is an
  equivalence.  `TauCeti.QuiverRep.dimVector_asModule` records that the dimension vector is
  unchanged.

## Implementation notes

The vertex spaces are used through the family `TauCeti.QuiverRep.vertexSpace` of
`TauCeti.RepresentationTheory.Quiver.Representation.Basic` rather than as `M.obj v` directly,
because instance search does not see the objects of `CategoryTheory.Paths Q` as vertices when it is
asked for the *family* of instances that a direct sum indexed by the vertices needs; that file's
implementation notes say more.  For the same reason the naturality squares of
`TauCeti.QuiverRep.asModuleIso` and `TauCeti.QuiverRep.asModuleShrinkIso` open with
`change Q at a`, restating their quantified objects as vertices.

The `k`-module structure on `TauCeti.QuiverRep.asModule` is deliberately **not** the one the direct
sum already carries: it is `Module.restrictScalars k (pathAlgebra k Q)`, restriction of scalars
along `algebraMap`.  That is exactly the structure `ModuleCat.moduleOfAlgebraModule` puts on an
object of `ModuleCat (kQ)`, which is the one `TauCeti.quiverRepFunctor` uses; taking the direct
sum's own structure instead would give a second, only propositionally equal, `Module k` instance
and the essential-surjectivity isomorphism would not typecheck against the functor.  That the two
agree is what makes the identification `TauCeti.QuiverRep.asModuleEquiv` with the direct sum
`k`-linear; the identity additive equivalence it upgrades is private, `asModuleEquiv` being the
identification consumers use.

`DecidableEq Q` is needed to write down the summand inclusions `DirectSum.lof`, so it is carried
through the construction; the essential-surjectivity instance is a `Prop` and discharges it with
`classical`, so neither it nor `TauCeti.quiverRepEquivalence` asks for it.

The concrete carrier is indexed by `Q : Type v` with summands in `Type t`, so
`⨁ᵥ Mᵥ : Type (max v t)`: `TauCeti.QuiverRep.asModule` lands in a larger universe than the
representation it is built from whenever the vertex type does.  `TauCeti.quiverRepEquivalence` is
nevertheless stated at an arbitrary representation universe `t`, because over a finite vertex set
that direct sum is a finite product of the vertex spaces and so has a model in `Type t`
(`TauCeti.QuiverRep.small_asModule`); the model `TauCeti.QuiverRep.asModuleShrink` of it, whose
vertex components are those of `asModule` because `TauCeti.QuiverRep.asModuleShrinkEquiv` is
`kQ`-linear, is what witnesses essential surjectivity there.  The concrete direct-sum API is kept
at `max v t`, and `TauCeti.quiverRepEquivalenceFunctorObjIso` identifies the forward direction with
`asModule` itself at that universe.

## References

This is the essential-surjectivity half of `quiverRepEquivalence`, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for the
equivalence "sending a module `M` to the representation `v ↦ eᵥ M`, with an arrow acting by left
multiplication, and inverting through the idempotent decomposition `M = ⨁ᵥ eᵥ M`"; the fully
faithful half is `TauCeti.quiverRepFunctorFullyFaithful`.

The plan of the file follows Mathlib's group-algebra analogue: the type synonym carrying a module
structure through `Module.compHom`, the equivalence with the underlying type and the shape of the
final `≌ ModuleCat (algebra)` statement are those of `Representation.asModule`,
`Representation.asModuleEquiv` and `Rep.equivalenceModuleMonoidAlgebra` for `k[G]`.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Ch. III, or R. Schiffler, *Quiver Representations*, Ch. 5.
-/

public section

namespace TauCeti

open CategoryTheory PathAlgebra

universe u v w t

namespace QuiverRep

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
theorem pathEnd_mul_pathEnd_of_comp {a b c : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path c a) :
    pathEnd k Q M ⟨a, b, p⟩ * pathEnd k Q M ⟨c, a, q⟩ = pathEnd k Q M ⟨c, b, q.comp p⟩ := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, pathEnd_mk_apply, pathEnd_mk_apply, pathEnd_mk_apply,
    mapₗ_comp k Q M q p]
  exact congrArg _ (congrArg _ (DirectSum.component.lof_self k a _))

/-- **Paths that do not meet annihilate one another**, because the second lands in a summand the
first reads as zero. This is the other half of the multiplicativity of
`TauCeti.QuiverRep.toEnd`. -/
theorem pathEnd_mul_pathEnd_of_not_composable {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
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

end Basic

section Algebra

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q] [DecidableEq Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- **The action of the path algebra on `⨁ᵥ Mᵥ`**: the universal property
`TauCeti.PathAlgebra.liftAlgHom` applied to `TauCeti.QuiverRep.pathEnd`, whose three hypotheses are
the two composition laws and the completeness of the summand projections proved above. -/
noncomputable def toEnd : pathAlgebra k Q →ₐ[k] Module.End k (DirectSum Q (vertexSpace k Q M)) :=
  PathAlgebra.liftAlgHom k (pathEnd k Q M) (pathEnd_mul_pathEnd_of_comp k Q M)
    (pathEnd_mul_pathEnd_of_not_composable k Q M) (by intro _; exact sum_pathEnd_nil k Q M)

/-- The action of a basis path is the endomorphism it was assigned. -/
@[simp]
theorem toEnd_ofPath (x : Quiver.TotalPath Q) : toEnd k Q M (ofPath x) = pathEnd k Q M x := by
  rw [toEnd, PathAlgebra.liftAlgHom_ofPath]

/-- The action of a scaled basis path scales its endomorphism. -/
@[simp]
theorem toEnd_single (x : Quiver.TotalPath Q) (c : k) :
    toEnd k Q M (single x c) = c • pathEnd k Q M x := by
  rw [toEnd, PathAlgebra.liftAlgHom_single]

/-- The action of a vertex idempotent is the endomorphism of the trivial path there, which by
`TauCeti.QuiverRep.mapₗ_nil` is the projection onto that summand. -/
theorem toEnd_vertexIdempotent (v : Q) :
    toEnd k Q M (vertexIdempotent k v) = pathEnd k Q M ⟨v, v, _root_.Quiver.Path.nil⟩ := by
  rw [vertexIdempotent_eq_single, toEnd_single, one_smul]

/-- The module over the path algebra carried by a representation of `Q`.

`@[expose]` is load-bearing rather than a leak: the `Module (pathAlgebra k Q)` instance below is
`Module.compHom` on the underlying direct sum, and the naturality square of
`TauCeti.QuiverRep.asModuleIso` is stated on elements of it, neither of which elaborates against
this type until the body is unfolded.  Consumers should still go through
`TauCeti.QuiverRep.asModuleEquiv`, since the direct sum's own `k`-action is only propositionally
the one carried here. -/
@[expose]
def asModule : Type max v t := DirectSum Q (vertexSpace k Q M)

instance : AddCommGroup (asModule k Q M) :=
  inferInstanceAs (AddCommGroup (DirectSum Q (vertexSpace k Q M)))

/-- **The defining `kQ`-action**: the path algebra acts on `⨁ᵥ Mᵥ` through the algebra map
`TauCeti.QuiverRep.toEnd` into its `k`-linear endomorphisms. -/
noncomputable instance : Module (pathAlgebra k Q) (asModule k Q M) :=
  Module.compHom (DirectSum Q (vertexSpace k Q M)) (toEnd k Q M).toRingHom

/-- The `k`-action, by restriction of scalars along `algebraMap k (kQ)` — deliberately *not* the
direct sum's own `k`-action, though the two agree, which is what makes
`TauCeti.QuiverRep.asModuleEquiv` `k`-linear; see the implementation notes. -/
noncomputable instance : Module k (asModule k Q M) :=
  Module.restrictScalars k (pathAlgebra k Q) (asModule k Q M)

/-- The `k`-action on `TauCeti.QuiverRep.asModule` is the restriction of the `kQ`-action, so the
two are compatible by construction. -/
instance : IsScalarTower k (pathAlgebra k Q) (asModule k Q M) :=
  IsScalarTower.restrictScalars k (pathAlgebra k Q) (asModule k Q M)

/-- The identity additive equivalence between `TauCeti.QuiverRep.asModule` and the direct sum
`⨁ᵥ Mᵥ` underlying it.  It is private, being only the step at which the two `k`-actions are
reconciled: the public identification is its `k`-linear upgrade
`TauCeti.QuiverRep.asModuleEquiv`. -/
private def asModuleAddEquiv : asModule k Q M ≃+ DirectSum Q (vertexSpace k Q M) := AddEquiv.refl _

/-- The defining action, read through the identity additive equivalence; the public form is
`TauCeti.QuiverRep.smul_asModule_def`. -/
private theorem asModuleAddEquiv_smul_pathAlgebra (f : pathAlgebra k Q) (x : asModule k Q M) :
    asModuleAddEquiv k Q M (f • x) = toEnd k Q M f (asModuleAddEquiv k Q M x) := (rfl)

/-- **The two `k`-actions agree**: the restriction of scalars along `algebraMap k (kQ)` that
`TauCeti.QuiverRep.asModule` carries is the direct sum's own `k`-action, because
`TauCeti.QuiverRep.toEnd` is a `k`-algebra map. This is what makes
`TauCeti.QuiverRep.asModuleEquiv` `k`-linear. -/
private theorem asModuleAddEquiv_smul (r : k) (x : asModule k Q M) :
    asModuleAddEquiv k Q M (r • x) = r • asModuleAddEquiv k Q M x := by
  rw [← algebraMap_smul (pathAlgebra k Q) r x, asModuleAddEquiv_smul_pathAlgebra, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

/-- **The module carried by a representation is its direct sum of vertex spaces**, `k`-linearly.
This is the identification consumers should go through, the `k`-action on
`TauCeti.QuiverRep.asModule` being only propositionally the direct sum's own. -/
noncomputable def asModuleEquiv : asModule k Q M ≃ₗ[k] DirectSum Q (vertexSpace k Q M) :=
  { asModuleAddEquiv k Q M with map_smul' := asModuleAddEquiv_smul k Q M }

/-- The defining action on `TauCeti.QuiverRep.asModule`: an element of the path algebra acts
through `TauCeti.QuiverRep.toEnd`. -/
theorem smul_asModule_def (f : pathAlgebra k Q) (x : asModule k Q M) :
    f • x = toEnd k Q M f (asModuleEquiv k Q M x) := (rfl)

/-- The inclusion of a vertex space into the module carried by a representation. -/
noncomputable def ofVertex (v : Q) : vertexSpace k Q M v →ₗ[k] asModule k Q M :=
  (asModuleEquiv k Q M).symm.toLinearMap.comp (DirectSum.lof k Q (vertexSpace k Q M) v)

/-- The projection of the module carried by a representation onto a vertex space. -/
noncomputable def toVertex (v : Q) : asModule k Q M →ₗ[k] vertexSpace k Q M v :=
  (DirectSum.component k Q (vertexSpace k Q M) v).comp (asModuleEquiv k Q M).toLinearMap

/-- The inclusion of a vertex space is the inclusion of the corresponding summand. -/
@[simp]
theorem asModuleEquiv_ofVertex (v : Q) (z : vertexSpace k Q M v) :
    asModuleEquiv k Q M (ofVertex k Q M v z)
      = DirectSum.lof k Q (vertexSpace k Q M) v z := (rfl)

-- Not `@[simp]`: this is the counterpart of `TauCeti.QuiverRep.asModuleEquiv_ofVertex`, stated
-- so that the projection can be computed, but rewriting with it would take
-- `TauCeti.QuiverRep.toVertex` out of the simp-normal form that
-- `TauCeti.QuiverRep.toVertex_ofVertex` and `TauCeti.QuiverRep.vertexIdempotent_smul` fix.
/-- The projection onto a vertex space reads off the corresponding component. -/
theorem toVertex_apply (v : Q) (x : asModule k Q M) :
    toVertex k Q M v x
      = DirectSum.component k Q (vertexSpace k Q M) v (asModuleEquiv k Q M x) := (rfl)

/-- The projection onto a vertex space undoes its inclusion. -/
@[simp]
theorem toVertex_ofVertex (v : Q) (z : vertexSpace k Q M v) :
    toVertex k Q M v (ofVertex k Q M v z) = z :=
  DirectSum.component.lof_self k v z

/-- **The summands are independent**: the projection onto a vertex space kills the image of every
other one. -/
@[simp]
theorem toVertex_ofVertex_of_ne {u v : Q} (h : u ≠ v) (z : vertexSpace k Q M v) :
    toVertex k Q M u (ofVertex k Q M v z) = 0 := by
  rw [toVertex_apply, asModuleEquiv_ofVertex, DirectSum.component.of k u v z]
  exact dite_eq_right (Ne.symm h)

/-- **The summands exhaust the module**: every element of `TauCeti.QuiverRep.asModule` is the sum
of the images of its vertex components. -/
theorem sum_ofVertex_toVertex [Fintype Q] (x : asModule k Q M) :
    ∑ v : Q, ofVertex k Q M v (toVertex k Q M v x) = x := by
  apply (asModuleEquiv k Q M).injective
  rw [map_sum]
  simp only [asModuleEquiv_ofVertex, toVertex_apply, ← DirectSum.apply_eq_component,
    DirectSum.lof_eq_of]
  exact DirectSum.sum_univ_of _

/-- The inclusion of a vertex space is injective. -/
theorem ofVertex_injective (v : Q) : Function.Injective (ofVertex k Q M v) :=
  Function.LeftInverse.injective (toVertex_ofVertex k Q M v)

-- Not `@[simp]`: the specialized `TauCeti.QuiverRep.smul_ofVertex` and
-- `TauCeti.QuiverRep.vertexIdempotent_smul` are the simp-normal forms of the action, this one
-- being stated on an arbitrary element and so introducing `TauCeti.QuiverRep.toVertex` where they
-- do not.
/-- **A basis path acts by transporting the component at its source**: it reads off that
component, applies the structure map, and puts the result in the component at its target. This is
`TauCeti.QuiverRep.pathEnd` read on `TauCeti.QuiverRep.asModule`. -/
theorem smul_ofPath {a b : Q} (p : _root_.Quiver.Path a b) (x : asModule k Q M) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • x
      = ofVertex k Q M b (mapₗ k Q M p (toVertex k Q M a x)) := by
  apply (asModuleEquiv k Q M).injective
  rw [smul_asModule_def, toEnd_ofPath, pathEnd_mk_apply, asModuleEquiv_ofVertex, toVertex_apply]
  -- what is left is the outer `TauCeti.QuiverRep.asModuleEquiv`, which is the identity map
  rfl

/-- **A path acts on the image of its source through the structure map**: this is the naturality
that makes `TauCeti.QuiverRep.asModuleIso` a morphism of representations. -/
@[simp]
theorem smul_ofVertex {a b : Q} (p : _root_.Quiver.Path a b) (z : vertexSpace k Q M a) :
    (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • ofVertex k Q M a z
      = ofVertex k Q M b (mapₗ k Q M p z) := by
  rw [smul_ofPath, toVertex_ofVertex]

/-- **The vertex idempotent acts as the projection onto its summand**, the fact from which the
vertex component of `TauCeti.QuiverRep.asModule` is read off. -/
@[simp]
theorem vertexIdempotent_smul (v : Q) (x : asModule k Q M) :
    (vertexIdempotent k v : pathAlgebra k Q) • x = ofVertex k Q M v (toVertex k Q M v x) := by
  have h : (vertexIdempotent k v : pathAlgebra k Q)
      = ofPath ⟨v, v, _root_.Quiver.Path.nil⟩ := by
    rw [vertexIdempotent_eq_single, ofPath_eq_single]
  rw [h, smul_ofPath, mapₗ_nil, LinearMap.id_coe, id_eq]

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

/-- `TauCeti.QuiverRep.pathMap_vertexComponentEquiv` read backwards through the identification:
this is the elementwise naturality square of the isomorphisms below, in the form in which the
vertex component, rather than the vertex space, carries the element. -/
private theorem vertexComponentEquiv_symm_pathMap {a b : Q} (p : _root_.Quiver.Path a b)
    (y : vertexComponent k (asModule k Q M) a) :
    (vertexComponentEquiv k Q M b).symm (pathMap k (asModule k Q M) p y)
      = mapₗ k Q M p ((vertexComponentEquiv k Q M a).symm y) := by
  rw [LinearEquiv.symm_apply_eq, ← pathMap_vertexComponentEquiv]
  exact congrArg _ ((vertexComponentEquiv k Q M a).apply_symm_apply y).symm

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
      -- both sides of the naturality square are `ModuleCat.ofHom` of a composite of a structure
      -- map with a `LinearEquiv.toModuleIso`, and the bundling is definitional, so the square is
      -- the elementwise `TauCeti.QuiverRep.vertexComponentEquiv_symm_pathMap`
      exact ModuleCat.hom_ext
        (LinearMap.ext fun x => vertexComponentEquiv_symm_pathMap k Q M p x))

/-- **The dimension vector is unchanged** by passing to the module a representation carries and
back. -/
theorem dimVector_asModule :
    dimVector (quiverRepOfModule k Q (asModule k Q M)) = dimVector M :=
  dimVector_eq_of_iso (asModuleIso k Q M)

end EssSurj

section Shrink

-- the two instances of `Mathlib.Algebra.Category.ModuleCat.Algebra` that give the underlying type
-- of an object of `ModuleCat (pathAlgebra k Q)` its `k`-structure are scoped
open scoped ModuleCat

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q] [DecidableEq Q]
variable (M : QuiverRep.{u, v, w, t} k Q)

/-- **The module carried by a representation is no larger than the representation**: over a finite
vertex set the direct sum `⨁ᵥ Mᵥ` is a finite product of the vertex spaces, so it has a model in
their universe even though it is indexed by a vertex type that may live in a larger one. -/
instance small_asModule : Small.{t} (asModule k Q M) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Small.{t} Q := small_map (Finite.equivFin Q)
  exact small_map (α := asModule k Q M) (DFinsupp.equivFunOnFintype (β := vertexSpace k Q M))

/-- **The module carried by a representation, in the universe of the representation**: a model of
`TauCeti.QuiverRep.asModule` in `Type t`, as an object of `ModuleCat (kQ)`.  It is bundled as an
object rather than as a type so that its `k`-structure is the restriction of scalars that
`ModuleCat.moduleOfAlgebraModule` puts on it, and not the one `Shrink` transports; that is the
structure `TauCeti.quiverRepFunctor` reads it with. -/
noncomputable def asModuleShrink : ModuleCat.{t} (pathAlgebra k Q) :=
  ModuleCat.of (pathAlgebra k Q) (Shrink.{t} (asModule k Q M))

/-- **The small model is the module carried by the representation**, `kQ`-linearly. -/
noncomputable def asModuleShrinkEquiv :
    (asModuleShrink k Q M : Type t) ≃ₗ[pathAlgebra k Q] asModule k Q M :=
  Shrink.linearEquiv (pathAlgebra k Q) (asModule k Q M)

/-- The vertex components of the small model are those of `TauCeti.QuiverRep.asModule`, the
restriction of `TauCeti.QuiverRep.asModuleShrinkEquiv` to them. -/
private noncomputable def vertexComponentShrinkEquiv (a : Q) :
    vertexComponent k (asModuleShrink k Q M : Type t) a
      ≃ₗ[k] vertexComponent k (asModule k Q M) a :=
  LinearEquiv.ofLinearMap (vertexComponentMap k (asModuleShrinkEquiv k Q M).toLinearMap a)
    (vertexComponentMap k (asModuleShrinkEquiv k Q M).symm.toLinearMap a)
    (by
      rw [← vertexComponentMap_comp]
      simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
        vertexComponentMap_id])
    (by
      rw [← vertexComponentMap_comp]
      simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
        vertexComponentMap_id])

/-- The vertex space of the representation is the vertex component of the small model: this is
`TauCeti.QuiverRep.vertexComponentEquiv` transported along
`TauCeti.QuiverRep.asModuleShrinkEquiv`. -/
private noncomputable def vertexShrinkEquiv (a : Q) :
    vertexComponent k (asModuleShrink k Q M : Type t) a ≃ₗ[k] vertexSpace k Q M a :=
  (vertexComponentShrinkEquiv k Q M a).trans (vertexComponentEquiv k Q M a).symm

private theorem vertexShrinkEquiv_apply (a : Q)
    (x : vertexComponent k (asModuleShrink k Q M : Type t) a) :
    vertexShrinkEquiv k Q M a x
      = (vertexComponentEquiv k Q M a).symm (vertexComponentShrinkEquiv k Q M a x) := (rfl)

/-- The restriction of a `kQ`-linear map to the vertex components commutes with the action of a
path, so the vertex components of the small model carry a path the same way. -/
private theorem vertexComponentShrinkEquiv_pathMap {a b : Q} (p : _root_.Quiver.Path a b)
    (x : vertexComponent k (asModuleShrink k Q M : Type t) a) :
    vertexComponentShrinkEquiv k Q M b (pathMap k (asModuleShrink k Q M : Type t) p x)
      = pathMap k (asModule k Q M) p (vertexComponentShrinkEquiv k Q M a x) :=
  LinearMap.congr_fun
    (vertexComponentMap_comp_pathMap k (asModuleShrinkEquiv k Q M).toLinearMap p) x

/-- **The identification is natural in the path**, the naturality square of the isomorphism
below. -/
private theorem vertexShrinkEquiv_pathMap {a b : Q} (p : _root_.Quiver.Path a b)
    (x : vertexComponent k (asModuleShrink k Q M : Type t) a) :
    vertexShrinkEquiv k Q M b (pathMap k (asModuleShrink k Q M : Type t) p x)
      = mapₗ k Q M p (vertexShrinkEquiv k Q M a x) := by
  rw [vertexShrinkEquiv_apply, vertexShrinkEquiv_apply, vertexComponentShrinkEquiv_pathMap,
    vertexComponentEquiv_symm_pathMap]

/-- **Essential surjectivity in the universe of the representation**: the representation carried by
the small model of the module carried by `M` is `M` again.  This is
`TauCeti.QuiverRep.asModuleIso` transported along `TauCeti.QuiverRep.asModuleShrinkEquiv`, and it is
what makes `TauCeti.quiverRepEquivalence` an equivalence at an arbitrary representation
universe. -/
noncomputable def asModuleShrinkIso :
    quiverRepOfModule k Q (asModuleShrink k Q M : Type t) ≅ M :=
  NatIso.ofComponents (fun a => (vertexShrinkEquiv k Q M a).toModuleIso)
    (fun {a b} p => by
      change Q at a
      change Q at b
      -- as for `TauCeti.QuiverRep.asModuleIso`, the bundling of both sides of the square is
      -- definitional, so the square is the elementwise
      -- `TauCeti.QuiverRep.vertexShrinkEquiv_pathMap`
      exact ModuleCat.hom_ext (LinearMap.ext fun x => vertexShrinkEquiv_pathMap k Q M p x))

end Shrink

section Equivalence

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- **The module-to-representation functor is essentially surjective**: every representation is
carried by the `kQ`-module `TauCeti.QuiverRep.asModule` built from it, read in the universe of the
representation through `TauCeti.QuiverRep.asModuleShrink`. -/
instance : (quiverRepFunctor.{u, v, w, t} k Q).EssSurj where
  mem_essImage M := by
    classical
    exact ⟨asModuleShrink k Q M, ⟨asModuleShrinkIso k Q M⟩⟩

/-- **The module-to-representation functor is an equivalence**: it is fully faithful by
`TauCeti.quiverRepFunctorFullyFaithful` and essentially surjective by the instance above. -/
instance : (quiverRepFunctor.{u, v, w, t} k Q).IsEquivalence where

/-- **Representations of a quiver are modules over its path algebra.** -/
noncomputable def _root_.TauCeti.quiverRepEquivalence :
    QuiverRep.{u, v, w, t} k Q ≌ ModuleCat.{t} (pathAlgebra k Q) :=
  (quiverRepFunctor.{u, v, w, t} k Q).asEquivalence.symm

/-- The inverse of `TauCeti.quiverRepEquivalence` is `TauCeti.quiverRepFunctor`: the equivalence is
the module-to-representation functor of
`TauCeti.RepresentationTheory.Quiver.Representation.OfModule`, turned around. -/
theorem _root_.TauCeti.quiverRepEquivalence_inverse :
    (quiverRepEquivalence.{u, v, w, t} k Q).inverse = quiverRepFunctor k Q := (rfl)

/-- **The forward direction of `TauCeti.quiverRepEquivalence` is
`TauCeti.QuiverRep.asModule`.** The functor of the equivalence is `CategoryTheory.Functor.inv`, so
on objects it is a choice of preimage; this identifies that choice with the module built here,
which is what a consumer transporting a representation across the equivalence needs.  It is stated
at the universe `max v t` where the direct sum `⨁ᵥ Mᵥ` lives; for a representation valued in a
smaller universe the preimage is the model `TauCeti.QuiverRep.asModuleShrink` of that sum. -/
noncomputable def _root_.TauCeti.quiverRepEquivalenceFunctorObjIso [DecidableEq Q]
    (M : QuiverRep.{u, v, w, max v t} k Q) :
    (quiverRepEquivalence.{u, v, w, max v t} k Q).functor.obj M
      ≅ ModuleCat.of (pathAlgebra k Q) (asModule k Q M) :=
  (quiverRepFunctorFullyFaithful k Q).preimageIso
    ((quiverRepFunctor.{u, v, w, max v t} k Q).objObjPreimageIso M ≪≫ (asModuleIso k Q M).symm)

end Equivalence

end QuiverRep

end TauCeti
