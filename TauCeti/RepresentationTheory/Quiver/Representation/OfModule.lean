/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.RepresentationTheory.Quiver.ModuleDecomposition` is imported publicly: the path algebra
-- `TauCeti.pathAlgebra` and the three pieces of data it carries on a module — the vertex component
-- `TauCeti.vertexComponent`, the path action `TauCeti.pathMap`, and the restriction
-- `TauCeti.vertexComponentMap` — all occur in the statements below.
public import TauCeti.RepresentationTheory.Quiver.ModuleDecomposition
-- `TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector` is imported publicly:
-- `TauCeti.dimVector` occurs in a statement below, and the module re-exports
-- `TauCeti.RepresentationTheory.Quiver.Representation.Basic`, hence `TauCeti.QuiverRep`, which is
-- the type this file constructs.
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
-- `Mathlib.Algebra.Category.ModuleCat.Algebra` is imported publicly for the two scoped instances
-- `ModuleCat.moduleOfAlgebraModule` and `ModuleCat.isScalarTower_of_algebra_moduleCat`, which give
-- an object of `ModuleCat (pathAlgebra k Q)` the `k`-structure that the declarations below ask of a
-- `kQ`-module; they are needed to state anything about `TauCeti.quiverRepFunctor` on objects.
public import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# The representation of a quiver carried by a module over its path algebra

`TauCeti.RepresentationTheory.Quiver.ModuleDecomposition` equips a left module `M` over the path
algebra `kQ` of a finite quiver with the data of a representation of `Q`: the `k`-subspace
`eᵥ M = TauCeti.vertexComponent k M v` at each vertex, the `k`-linear map `TauCeti.pathMap` along
each path, and the restriction `TauCeti.vertexComponentMap` of a `kQ`-linear map to those
subspaces. This file assembles that data into an object and a morphism of `TauCeti.QuiverRep k Q`,
bundles the assignment as a functor `ModuleCat (kQ) ⥤ TauCeti.QuiverRep k Q`, and proves that
functor **fully faithful**.

## Main definitions

* `TauCeti.quiverRepOfModule k Q M`: the representation `v ↦ eᵥ M` of `Q` carried by a `kQ`-module.
* `TauCeti.quiverRepHomOfModule k Q f`: the morphism of representations carried by a `kQ`-linear
  map.
* `TauCeti.quiverRepHomComponent k Q φ v`: the component at `v` of a morphism between two such
  representations, retyped as a map `eᵥ M →ₗ[k] eᵥ N`.
* `TauCeti.moduleHomOfQuiverRepHom k Q φ`: the `kQ`-linear map glued from those components,
  inverse to `TauCeti.quiverRepHomOfModule`.
* `TauCeti.quiverRepFunctor k Q`: the two previous assignments bundled as a functor
  `ModuleCat (kQ) ⥤ TauCeti.QuiverRep k Q`, and
  `TauCeti.quiverRepFunctorFullyFaithful`: its full faithfulness.

## Main results

* `TauCeti.dimVector_quiverRepOfModule`: the dimension vector of `quiverRepOfModule k Q M` is
  `v ↦ dimₖ (eᵥ M)`, and `TauCeti.finrank_eq_sum_dimVector_quiverRepOfModule`: over a
  finite-dimensional module its coordinates sum to `dimₖ M`.
* `TauCeti.quiverRepHomOfModule_id` and `TauCeti.quiverRepHomOfModule_comp`: the assignment is
  functorial.
* `TauCeti.quiverRepHomOfModule_injective` and
  `TauCeti.quiverRepHomOfModule_moduleHomOfQuiverRepHom`: it is **injective** and **surjective** on
  `Hom`-sets, packaged as `TauCeti.quiverRepHomOfModule_bijective` and, on the bundled functor, as
  `TauCeti.quiverRepFunctorFullyFaithful`. The inverse laws for the explicit inverse are that
  surjectivity statement together with `TauCeti.moduleHomOfQuiverRepHom_quiverRepHomOfModule`.

## Implementation notes

Both the module and the resulting representation are described through the *subspaces* `eᵥ M` of
`M`, not through an abstract direct-sum carrier; that is what makes `TauCeti.vertexProjection` and
the identity `∑ᵥ eᵥ • x = x` (`TauCeti.sum_coe_vertexProjection`), both from
`TauCeti.RepresentationTheory.Quiver.ModuleDecomposition`, available, and those two carry the whole
content of full faithfulness: injectivity is the fact that a `kQ`-linear map is determined by its
restrictions to the components, and surjectivity glues the components of a morphism back together,
the naturality in the paths being exactly what makes the glued map `kQ`-linear.

The vertex set is finite throughout, as it must be: the unit `1 = ∑ᵥ eᵥ` of `kQ` is a finite sum of
vertex idempotents, and without it a module is not the sum of its vertex components at all. It is
carried as `[Finite Q]`, refined to `[Fintype Q]` only where a sum over the vertices is genuinely
in a statement; elsewhere `Fintype.ofFinite` supplies the enumeration a proof or a body needs. The
base is a field only because `TauCeti.QuiverRep` is; the underlying data of
`TauCeti.RepresentationTheory.Quiver.ModuleDecomposition` needs no more than a commutative
semiring. The `k`-linear structure carried on `M` alongside the `kQ`-action is asked for as
`[Module k M]` with `[IsScalarTower k (pathAlgebra k Q) M]`, not extracted from the algebra,
exactly as in that file. The three modules of the morphism section share one universe, since
`ModuleCat k` — and hence `TauCeti.QuiverRep k Q` — has objects in a single universe. Those two
hypotheses are what forces the source category of `TauCeti.quiverRepFunctor` to be spelled with the
scoped instances `ModuleCat.moduleOfAlgebraModule` and
`ModuleCat.isScalarTower_of_algebra_moduleCat` of
`Mathlib.Algebra.Category.ModuleCat.Algebra`, which restrict the scalars of an object of
`ModuleCat (kQ)` along `algebraMap k (kQ)`; a file stating anything about that functor must
`open scoped ModuleCat` for the same reason.

A representation is a functor out of `CategoryTheory.Paths Q`, whose objects are the vertices of
`Q` only after unfolding the semireducible `CategoryTheory.Paths`. Two devices from the
neighbouring files handle that: `change Q at v` restates a quantified object as a vertex, and the
functorial equations of `quiverRepOfModule` are proved by first naming the intended identity with
the vertex-indexed `TauCeti.pathMap_nil` and `TauCeti.pathMap_comp`, whose statements are then
matched definitionally. The morphism-level API is stated on `ModuleCat` homomorphisms rather than
on elements for the same reason: an element of `(quiverRepOfModule k Q M).obj v` is an element of
`eᵥ M` only up to unfolding, so a coercion of it to `M` does not elaborate. That is what
`TauCeti.quiverRepHomComponent` is for: it names the component of a morphism at the vertex-indexed
type `eᵥ M →ₗ[k] eᵥ N` once and for all, and everything about the gluing is stated through it.

## References

This is the fully faithful half of `quiverRepEquivalence`, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which asks for the
equivalence "sending a module `M` to the representation `v ↦ eᵥ M`, with an arrow acting by left
multiplication, and inverting through the idempotent decomposition `M = ⨁ᵥ eᵥ M`". Full
faithfulness is proved here; the essential surjectivity that completes the equivalence — a
`kQ`-module structure on `⨁ᵥ Mᵥ` for a given representation — is
`TauCeti.RepresentationTheory.Quiver.Representation.AsModule`, where the two halves are assembled
into `TauCeti.quiverRepEquivalence`.

The equivalence itself is classical; see Assem--Simson--Skowroński, *Elements of the Representation
Theory of Associative Algebras I*, Ch. III, or Schiffler, *Quiver Representations*, Ch. 5.
-/

public section

namespace TauCeti

open CategoryTheory PathAlgebra

universe u v w t

section Object

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]
variable (M : Type t) [AddCommGroup M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M]

/-- **The representation of `Q` carried by a module over its path algebra**: the vector space at a
vertex `v` is the component `eᵥ M`, and a path acts by left multiplication, carrying the component
at its source to the component at its target.

`@[expose]` is load-bearing rather than a leak: the *statements* of `TauCeti.quiverRepOfModule_map`
and of `TauCeti.quiverRepHomOfModule` speak of maps between the objects `(quiverRepOfModule k Q
M).obj v`, which only typecheck against `ModuleCat.of k (eᵥ M)` once this body is unfolded. -/
@[expose]
noncomputable def quiverRepOfModule : QuiverRep k Q where
  obj v := ModuleCat.of k (vertexComponent (Q := Q) k M v)
  map p := ModuleCat.ofHom (pathMap (Q := Q) k M p)
  map_id v := by
    -- the identity of `CategoryTheory.Paths` at a vertex is the trivial path there
    have h : pathMap (Q := Q) k M (𝟙 v) = LinearMap.id := pathMap_nil (Q := Q) k M v
    rw [h]
    rfl
  map_comp p q := by
    -- composition in `CategoryTheory.Paths` is concatenation of paths
    have h : pathMap (Q := Q) k M (p ≫ q)
        = (pathMap (Q := Q) k M q).comp (pathMap (Q := Q) k M p) :=
      pathMap_comp (Q := Q) k M p q
    rw [h, ModuleCat.ofHom_comp]

/-- The vector space of `quiverRepOfModule k Q M` at a vertex is the component of `M` there. -/
@[simp]
theorem quiverRepOfModule_obj (v : Q) :
    (quiverRepOfModule k Q M).obj v = ModuleCat.of k (vertexComponent k M v) := (rfl)

/-- A path acts on `quiverRepOfModule k Q M` by left multiplication. -/
@[simp]
theorem quiverRepOfModule_map {a b : Q} (p : _root_.Quiver.Path a b) :
    (quiverRepOfModule k Q M).map p = ModuleCat.ofHom (pathMap k M p) := (rfl)

-- Not `@[simp]`: `TauCeti.dimVector_apply` already rewrites the left-hand side into a
-- `Module.finrank` of a vertex space, so tagging this would be a simp-normal-form violation
-- (`simpNF`). It is stated because that rewrite leaves the vertex indexed by `Paths.of`, a form no
-- lemma about `TauCeti.vertexComponent` matches.
/-- **The dimension vector of the representation carried by a module** is the vertexwise dimension
of its components. -/
theorem dimVector_quiverRepOfModule (v : Q) :
    dimVector (quiverRepOfModule k Q M) v = Module.finrank k (vertexComponent k M v) :=
  dimVector_apply _ v

/-- **The dimension vector of a finite-dimensional module sums to its dimension**: this is
`TauCeti.finrank_eq_sum_finrank_vertexComponent` read on the associated representation. -/
theorem finrank_eq_sum_dimVector_quiverRepOfModule [Fintype Q] [Module.Finite k M] :
    Module.finrank k M = ∑ v : Q, dimVector (quiverRepOfModule k Q M) v := by
  simp only [dimVector_quiverRepOfModule]
  exact finrank_eq_sum_finrank_vertexComponent k M

end Object

section Morphism

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]
variable {M N P : Type t} [AddCommGroup M] [Module k M] [Module (pathAlgebra k Q) M]
  [IsScalarTower k (pathAlgebra k Q) M] [AddCommGroup N] [Module k N]
  [Module (pathAlgebra k Q) N] [IsScalarTower k (pathAlgebra k Q) N] [AddCommGroup P]
  [Module k P] [Module (pathAlgebra k Q) P] [IsScalarTower k (pathAlgebra k Q) P]

/-- **The morphism of representations carried by a `kQ`-linear map**: at each vertex it is the
restriction of the map to the components there, natural in the path by
`TauCeti.vertexComponentMap_comp_pathMap`. -/
noncomputable def quiverRepHomOfModule (f : M →ₗ[pathAlgebra k Q] N) :
    quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N where
  app v := ModuleCat.ofHom (vertexComponentMap (Q := Q) k f v)
  -- both sides are `ModuleCat.ofHom` of the two composites, so this is the naturality of the
  -- restriction maps in the path, transported along `ModuleCat.ofHom`
  naturality {a b} p :=
    congrArg ModuleCat.ofHom (vertexComponentMap_comp_pathMap (a := a) (b := b) k f p)

@[simp]
theorem quiverRepHomOfModule_app (f : M →ₗ[pathAlgebra k Q] N) (v : Q) :
    (quiverRepHomOfModule k Q f).app v = ModuleCat.ofHom (vertexComponentMap k f v) :=
  (rfl)

/-- **The assignment is functorial**: the identity map goes to the identity morphism. -/
@[simp]
theorem quiverRepHomOfModule_id :
    quiverRepHomOfModule k Q (LinearMap.id : M →ₗ[pathAlgebra k Q] M)
      = 𝟙 (quiverRepOfModule k Q M) := by
  refine NatTrans.ext (funext fun v ↦ ?_)
  change Q at v
  rw [quiverRepHomOfModule_app, vertexComponentMap_id]
  exact ModuleCat.ofHom_id

/-- **The assignment is functorial**: a composite goes to the composite. -/
@[simp]
theorem quiverRepHomOfModule_comp (f : M →ₗ[pathAlgebra k Q] N) (g : N →ₗ[pathAlgebra k Q] P) :
    quiverRepHomOfModule k Q (g.comp f)
      = quiverRepHomOfModule k Q f ≫ quiverRepHomOfModule k Q g := by
  refine NatTrans.ext (funext fun v ↦ ?_)
  change Q at v
  rw [quiverRepHomOfModule_app, vertexComponentMap_comp]
  exact ModuleCat.ofHom_comp (vertexComponentMap k f v) (vertexComponentMap k g v)

/-- **Faithfulness**: a `kQ`-linear map is determined by the morphism of representations it
carries, a module being the sum of its vertex components. -/
theorem quiverRepHomOfModule_injective :
    Function.Injective (quiverRepHomOfModule (k := k) (Q := Q) (M := M) (N := N)) := by
  intro f g hfg
  have hcomp : ∀ v : Q, vertexComponentMap (Q := Q) k f v = vertexComponentMap (Q := Q) k g v := by
    intro v
    have h := congrArg (fun φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N ↦ φ.app v) hfg
    rw [quiverRepHomOfModule_app, quiverRepHomOfModule_app] at h
    simpa using congrArg ModuleCat.Hom.hom h
  refine LinearMap.ext fun x ↦ ?_
  have key : ∀ v : Q, f ((vertexProjection k M v x : M)) = g ((vertexProjection k M v x : M)) := by
    intro v
    have h := congrArg
      (fun ψ : vertexComponent k M v →ₗ[k] vertexComponent k N v ↦
        (ψ (vertexProjection k M v x) : N))
      (hcomp v)
    simpa only [coe_vertexComponentMap_apply] using h
  let := Fintype.ofFinite Q
  calc f x = ∑ v : Q, f ((vertexProjection k M v x : M)) := by
        rw [← map_sum, sum_coe_vertexProjection]
    _ = ∑ v : Q, g ((vertexProjection k M v x : M)) := Finset.sum_congr rfl fun v _ ↦ key v
    _ = g x := by rw [← map_sum, sum_coe_vertexProjection]

/-- **The component at a vertex of a morphism between representations carried by modules**, named
at the vertex-indexed type `eᵥ M →ₗ[k] eᵥ N`. It is the component of `φ` as a `ModuleCat`
homomorphism, retyped: that is what lets its values be spoken of as elements of `eᵥ N`, which the
object type of `TauCeti.quiverRepOfModule` otherwise hides. -/
noncomputable def quiverRepHomComponent
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) (v : Q) :
    vertexComponent k M v →ₗ[k] vertexComponent k N v :=
  (φ.app v).hom

/-- **The components of a morphism commute with the action of a path.** This is the naturality of
`φ`, read at the vertex-indexed types. -/
theorem quiverRepHomComponent_comp_pathMap
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) {a b : Q}
    (p : _root_.Quiver.Path a b) :
    (quiverRepHomComponent k Q φ b).comp (pathMap (Q := Q) k M p)
      = (pathMap (Q := Q) k N p).comp (quiverRepHomComponent k Q φ a) :=
  congrArg ModuleCat.Hom.hom (φ.naturality p)

/-- The `k`-linear map underlying `TauCeti.moduleHomOfQuiverRepHom`: glue the components of `φ`
along the decomposition `M = ⨁ᵥ eᵥ M`. Private: only its `kQ`-linear upgrade is public. -/
private noncomputable def moduleHomAux [Fintype Q]
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) : M →ₗ[k] N where
  toFun x := ∑ v : Q, ((quiverRepHomComponent k Q φ v) (vertexProjection k M v x) : N)
  map_add' x y := by
    simp only [map_add, Submodule.coe_add]
    exact Finset.sum_add_distrib
  map_smul' r x := by
    simp only [map_smul, SetLike.val_smul, RingHom.id_apply, ← Finset.smul_sum]

private theorem moduleHomAux_apply [Fintype Q]
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) (x : M) :
    moduleHomAux k Q φ x
      = ∑ v : Q, ((quiverRepHomComponent k Q φ v) (vertexProjection k M v x) : N) :=
  (rfl)

/-- On the component at `v` the glued map is the component of `φ` there: the other summands vanish,
the projections at the other vertices killing `eᵥ M`. -/
private theorem moduleHomAux_apply_of_mem [Fintype Q]
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) {v : Q} (x : vertexComponent k M v) :
    moduleHomAux k Q φ (x : M) = ((quiverRepHomComponent k Q φ v) x : N) := by
  -- the projection lemmas are stated on the ambient values in `M`, so `Subtype.ext` lifts them to
  -- the equalities in `eᵥ M` that the summands are built from
  have hfix : vertexProjection k M v (x : M) = x :=
    Subtype.ext (coe_vertexProjection_apply_of_mem x.2)
  have hkill : ∀ u : Q, u ≠ v → vertexProjection k M u (x : M) = 0 := fun u hu ↦
    Subtype.ext (coe_vertexProjection_apply_eq_zero_of_ne hu x.2)
  rw [moduleHomAux_apply, Finset.sum_eq_single v]
  · rw [hfix]
  · intro u _ hu
    rw [hkill u hu, map_zero, ZeroMemClass.coe_zero]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

/-- **The glued map commutes with the action of a basis path.** This is
`TauCeti.quiverRepHomComponent_comp_pathMap` once the two sums have been cut down: on the left
because a path lands in the component of its target, on the right because it annihilates every
component but that of its source. -/
private theorem moduleHomAux_ofPath_smul [Fintype Q]
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) {a b : Q}
    (p : _root_.Quiver.Path a b) (x : M) :
    moduleHomAux k Q φ ((ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • x)
      = (ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • moduleHomAux k Q φ x := by
  have hmem : (ofPath (⟨a, b, p⟩ : Quiver.TotalPath Q) : pathAlgebra k Q) • x
      ∈ vertexComponent k M b := ofPath_smul_mem_vertexComponent p x
  have hleft : moduleHomAux k Q φ ((ofPath ⟨a, b, p⟩ : pathAlgebra k Q) • x)
      = ((quiverRepHomComponent k Q φ b) ⟨_, hmem⟩ : N) := moduleHomAux_apply_of_mem k Q φ ⟨_, hmem⟩
  have hstep : (⟨_, hmem⟩ : vertexComponent k M b)
      = pathMap (Q := Q) k M p (vertexProjection k M a x) :=
    Subtype.ext (by
      rw [coe_pathMap_apply, coe_vertexProjection_apply, smul_smul, ofPath_mul_vertexIdempotent])
  have hnat := congrArg (fun ψ : vertexComponent k M a →ₗ[k] vertexComponent k N b ↦
    (ψ (vertexProjection k M a x) : N)) (quiverRepHomComponent_comp_pathMap k Q φ p)
  rw [hleft, hstep]
  refine .trans (by simpa using hnat) ?_
  -- the closing `rfl` of the rewrite is `TauCeti.coe_pathMap_apply`
  rw [moduleHomAux_apply, Finset.smul_sum, Finset.sum_eq_single a]
  · intro u _ hu
    exact ofPath_smul_eq_zero_of_ne_of_mem_vertexComponent p hu
      ((quiverRepHomComponent k Q φ u) (vertexProjection k M u x)).2
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- The component of the morphism carried by a `kQ`-linear map is the restriction of that map. -/
@[simp]
theorem quiverRepHomComponent_quiverRepHomOfModule (f : M →ₗ[pathAlgebra k Q] N) (v : Q) :
    quiverRepHomComponent k Q (quiverRepHomOfModule k Q f) v = vertexComponentMap k f v :=
  (rfl)

/-- **The `kQ`-linear map recovered from a morphism of the associated representations.** It glues
the components of `φ` along the decomposition `M = ⨁ᵥ eᵥ M`; the naturality of `φ` in the paths is
exactly what makes the glued map commute with the action of the path algebra.

Only `[Finite Q]` is asked for: the gluing needs an enumeration of the vertices, but no sum over
them occurs in the type, so `Fintype.ofFinite` supplies one in the body. -/
noncomputable def moduleHomOfQuiverRepHom
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) : M →ₗ[pathAlgebra k Q] N :=
  let _ := Fintype.ofFinite Q
  { toFun := moduleHomAux k Q φ
    map_add' := map_add _
    map_smul' a x := by
      induction a using PathAlgebra.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [add_smul, map_add, hf, hg]
      | single y c =>
        obtain ⟨b, c', p⟩ := y
        -- the induction hands the basis element in the `single` form, while
        -- `TauCeti.moduleHomAux_ofPath_smul` is stated on `TauCeti.ofPath`; the two differ by the
        -- scalar `c`, which `TauCeti.PathAlgebra.single_eq_smul_ofPath` extracts
        rw [single_eq_smul_ofPath, smul_assoc, map_smul, moduleHomAux_ofPath_smul,
          RingHom.id_apply, smul_assoc] }

/-- The recovered map, spelled out: glue the components of `φ` along the vertex projections. -/
theorem moduleHomOfQuiverRepHom_apply [Fintype Q]
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) (x : M) :
    moduleHomOfQuiverRepHom k Q φ x
      = ∑ v : Q, ((quiverRepHomComponent k Q φ v) (vertexProjection k M v x) : N) := by
  -- the enumeration `Fintype.ofFinite Q` chosen in the body and the ambient one index the same
  -- sum, `Fintype Q` being a subsingleton
  obtain rfl : ‹Fintype Q› = Fintype.ofFinite Q := Subsingleton.elim _ _
  rfl

/-- **On a vertex component the recovered map is the component of `φ` there.** -/
theorem moduleHomOfQuiverRepHom_apply_of_mem
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) {v : Q}
    (x : vertexComponent k M v) :
    moduleHomOfQuiverRepHom k Q φ (x : M) = ((quiverRepHomComponent k Q φ v) x : N) := by
  let := Fintype.ofFinite Q
  exact moduleHomAux_apply_of_mem k Q φ x

/-- **Fullness**: every morphism of the associated representations is carried by a `kQ`-linear map,
namely `TauCeti.moduleHomOfQuiverRepHom`. -/
@[simp]
theorem quiverRepHomOfModule_moduleHomOfQuiverRepHom
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) :
    quiverRepHomOfModule k Q (moduleHomOfQuiverRepHom k Q φ) = φ := by
  refine NatTrans.ext (funext fun v ↦ ?_)
  change Q at v
  rw [quiverRepHomOfModule_app]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
  simp only [ModuleCat.hom_ofHom, coe_vertexComponentMap_apply]
  exact moduleHomOfQuiverRepHom_apply_of_mem k Q φ x

/-- **Faithfulness**, in inverse form: gluing the components of the morphism carried by a
`kQ`-linear map returns that map. -/
@[simp]
theorem moduleHomOfQuiverRepHom_quiverRepHomOfModule (f : M →ₗ[pathAlgebra k Q] N) :
    moduleHomOfQuiverRepHom k Q (quiverRepHomOfModule k Q f) = f :=
  quiverRepHomOfModule_injective k Q
    (quiverRepHomOfModule_moduleHomOfQuiverRepHom k Q (quiverRepHomOfModule k Q f))

/-- **Fullness**, in existential form. -/
theorem exists_quiverRepHomOfModule_eq
    (φ : quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N) :
    ∃ f : M →ₗ[pathAlgebra k Q] N, quiverRepHomOfModule k Q f = φ :=
  ⟨moduleHomOfQuiverRepHom k Q φ, quiverRepHomOfModule_moduleHomOfQuiverRepHom k Q φ⟩

/-- **Full faithfulness on a `Hom`-set**: the `kQ`-linear maps `M → N` are exactly the morphisms
`quiverRepOfModule k Q M ⟶ quiverRepOfModule k Q N`. With `TauCeti.quiverRepHomOfModule_id` and
`TauCeti.quiverRepHomOfModule_comp` this is one half of the roadmap's `quiverRepEquivalence`; the
other half is essential surjectivity. -/
theorem quiverRepHomOfModule_bijective :
    Function.Bijective (quiverRepHomOfModule (k := k) (Q := Q) (M := M) (N := N)) :=
  ⟨quiverRepHomOfModule_injective k Q, exists_quiverRepHomOfModule_eq k Q⟩

end Morphism

section Functor

-- the two instances of `Mathlib.Algebra.Category.ModuleCat.Algebra` that give the underlying type
-- of an object of `ModuleCat (pathAlgebra k Q)` its `k`-structure are scoped
open scoped ModuleCat

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- **The functor from `kQ`-modules to representations of `Q`**: it carries a module to
`TauCeti.quiverRepOfModule` and a `kQ`-linear map to `TauCeti.quiverRepHomOfModule`, the
functoriality being `TauCeti.quiverRepHomOfModule_id` and `TauCeti.quiverRepHomOfModule_comp`.
This is the module-to-representation half of the roadmap's `quiverRepEquivalence`, and
`TauCeti.quiverRepFunctorFullyFaithful` is its full faithfulness.

`@[expose]` here is load-bearing for the same reason as on `TauCeti.quiverRepOfModule`: the
*statement* of `TauCeti.quiverRepFunctor_map` speaks of a morphism between the objects
`(quiverRepFunctor k Q).obj M`, which only typechecks against a morphism of
`TauCeti.quiverRepOfModule` once this body is unfolded. -/
@[expose]
noncomputable def quiverRepFunctor : ModuleCat.{t} (pathAlgebra k Q) ⥤ QuiverRep k Q where
  obj M := quiverRepOfModule k Q M
  map f := quiverRepHomOfModule k Q f.hom
  map_id M := by rw [ModuleCat.hom_id]; exact quiverRepHomOfModule_id k Q
  map_comp f g := by rw [ModuleCat.hom_comp]; exact quiverRepHomOfModule_comp k Q f.hom g.hom

/-- The functor carries a module to the representation it carries. -/
@[simp]
theorem quiverRepFunctor_obj (M : ModuleCat.{t} (pathAlgebra k Q)) :
    (quiverRepFunctor k Q).obj M = quiverRepOfModule k Q M := (rfl)

/-- The functor carries a `kQ`-linear map to the morphism of representations it carries. -/
@[simp]
theorem quiverRepFunctor_map {M N : ModuleCat.{t} (pathAlgebra k Q)} (f : M ⟶ N) :
    (quiverRepFunctor k Q).map f = quiverRepHomOfModule k Q f.hom := (rfl)

/-- **The functor from `kQ`-modules to representations of `Q` is fully faithful**: this is
`TauCeti.quiverRepHomOfModule_bijective`, with `TauCeti.moduleHomOfQuiverRepHom` as the explicit
preimage. It is one half of the roadmap's `quiverRepEquivalence`; the other half is essential
surjectivity, proved in
`TauCeti.RepresentationTheory.Quiver.Representation.AsModule`. -/
noncomputable def quiverRepFunctorFullyFaithful :
    (quiverRepFunctor.{u, v, w, t} k Q).FullyFaithful where
  preimage {_ _} φ := ModuleCat.ofHom (moduleHomOfQuiverRepHom k Q φ)
  map_preimage φ := quiverRepHomOfModule_moduleHomOfQuiverRepHom k Q φ
  preimage_map f := by
    rw [quiverRepFunctor_map, moduleHomOfQuiverRepHom_quiverRepHomOfModule, ModuleCat.ofHom_hom]

instance : (quiverRepFunctor.{u, v, w, t} k Q).Full :=
  (quiverRepFunctorFullyFaithful k Q).full

instance : (quiverRepFunctor.{u, v, w, t} k Q).Faithful :=
  (quiverRepFunctorFullyFaithful k Q).faithful

end Functor

end TauCeti
