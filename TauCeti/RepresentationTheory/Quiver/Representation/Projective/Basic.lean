/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The projective representation at a vertex of a quiver

For a vertex `i` of a quiver `Q`, the representation `Pᵢ` puts the free `k`-module on the paths
`i → j` at the vertex `j`, an arrow `e : a ⟶ b` acting by appending `e` to a path. Under the
identification of representations with left modules over the path algebra it is the left ideal
`kQ · eᵢ`, whose basis is the paths starting at `i`.

## Main definitions

* `TauCeti.indecProjRep k Q i`: the representation `Pᵢ`.
* `TauCeti.indecProjRepBasis`: the paths `i → j` as a `k`-basis of `(Pᵢ)_j`.
* `TauCeti.indecProjRepHom`: the morphism `Pᵢ ⟶ M` determined by an element of `M` at `i`.

## Main results

* `TauCeti.indecProjRepHomEquiv`: `Pᵢ` **represents evaluation at `i`**, by the `k`-linear
  isomorphism `(Pᵢ ⟶ M) ≃ₗ[k] Mᵢ` sending a morphism to the image of the trivial path. This is the
  universal property from which everything else here follows.
* `TauCeti.projective_indecProjRep`: `Pᵢ` is a projective object of `TauCeti.QuiverRep k Q`.
* `TauCeti.dimVector_indecProjRep`: the dimension vector of `Pᵢ` counts the paths out of `i`, and
  `TauCeti.not_isZero_indecProjRep`: `Pᵢ` is nonzero.
* `TauCeti.finrank_hom_indecProjRep_indecProjRep`: `dim Hom(Pᵢ, Pⱼ)` is the number of paths
  `j → i`, the path-counting form of the Cartan matrix of a path algebra. Its acyclic consequence,
  that `Pᵢ` is then a brick, is in
  `TauCeti.RepresentationTheory.Quiver.Representation.Projective.Acyclic`.

## Implementation notes

The name `indecProjRep` is the one the roadmap pins for this object. Indecomposability is *not*
proved here: it needs the Krull-Schmidt theory of Layer 2, which is not yet available. What is
proved is projectivity, and the universal property that makes `Pᵢ` the representable functor at
`i`; both are independent of any finiteness assumption on `Q`, so no such assumption is made.

`Pᵢ` is built by `CategoryTheory.Paths.lift`: a representation of `Q` is a functor out of the free
category on `Q`, so a module at each vertex and a map along each arrow suffice, and Mathlib
supplies functoriality along path concatenation. No definition here exposes its body. Downstream
names an element of `(Pᵢ)_j` through the basis `indecProjRepBasis`, indexed by the paths `i → j`,
and every public lemma — on the action of a path, on the morphism attached to an element of the
target, on the universal property — is stated on those basis vectors; anyone who wants the
underlying free module has the explicit transport `(indecProjRepBasis k i j).repr`. The lemmas that
name finitely supported functions directly are private to this file.

A vertex `i : Q` is used below as an object of the free category `CategoryTheory.Paths Q`, which is
`Q` itself only by unfolding a semireducible definition. Goals about the action of a path are
therefore not type-correct at `instances` transparency, where `rw` and `simp` build their motives;
the one proof that has to reach the underlying statement about finitely supported functions does so
by `change`, and says so in a comment.

The vector space `(Pᵢ)_j` lives in the universe of `Quiver.Path i j →₀ k`, which is larger than
the universe of `k` unless the vertex and arrow types are small. The vertex simple `Sᵢ` of
`TauCeti.RepresentationTheory.Quiver.Representation.Simple` is built on `k` itself, so the two
objects sit in a common category only when those universes agree, and the projective cover
`Pᵢ ↠ Sᵢ` is therefore not stated here.

## References

This implements the indecomposable projectives of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

/-- **The projective representation at a vertex** `Pᵢ`: the free `k`-module on the paths `i → j`
at the vertex `j`, an arrow acting by appending itself to a path. Under the identification of
representations with left modules over the path algebra this is the left ideal `kQ · eᵢ`. -/
noncomputable def indecProjRep (i : Q) : QuiverRep k Q :=
  Paths.lift
    { obj := fun j ↦ ModuleCat.of k (Quiver.Path i j →₀ k)
      map := fun {a _} e ↦
        ModuleCat.ofHom (Finsupp.lmapDomain k k fun p : Quiver.Path i a ↦ p.cons e) }

variable {k Q}

/-- An arrow acts on `Pᵢ` by appending it to a path. Private: its statement names the underlying
finitely supported functions, which the public API hides behind `indecProjRepBasis`. -/
private theorem indecProjRep_map_toPath (i : Q) {a b : Q} (e : a ⟶ b) :
    (indecProjRep k Q i).map e.toPath
      = ModuleCat.ofHom (Finsupp.lmapDomain k k fun p : Quiver.Path i a ↦ p.cons e) :=
  Paths.lift_toPath _ e

/-- A path carries the basis element of `q : Quiver.Path i a` in `(Pᵢ)_a` to the basis element of
the concatenation `q.comp p`. Private: `indecProjRep_map_basis` is its public form. -/
private theorem indecProjRep_map_single (i : Q) {a b : Q} (p : Quiver.Path a b)
    (q : Quiver.Path i a) (c : k) :
    (indecProjRep k Q i).map p (Finsupp.single q c) = Finsupp.single (q.comp p) c := by
  induction p with
  | nil =>
    rw [QuiverRep.map_nil, ModuleCat.id_apply]
    rfl
  | cons p e ih =>
    have hcons : (indecProjRep k Q i).map (p.cons e)
        = (indecProjRep k Q i).map p ≫ (indecProjRep k Q i).map e.toPath :=
      (indecProjRep k Q i).map_comp p e.toPath
    rw [hcons, ModuleCat.comp_apply, ih, indecProjRep_map_toPath]
    exact Finsupp.mapDomain_single

/-- A path acts on `Pᵢ` by concatenation on the right. Private: it is the `Finsupp.lmapDomain`
form of `indecProjRep_map_basis`, used below to get at `Finsupp.lmapDomain_linearCombination`. -/
private theorem indecProjRep_map (i : Q) {a b : Q} (p : Quiver.Path a b) :
    (indecProjRep k Q i).map p
      = ModuleCat.ofHom (Finsupp.lmapDomain k k fun q : Quiver.Path i a ↦ q.comp p) := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun q c ↦ ?_)
  -- The goal here mentions `(indecProjRep k Q i).obj a` for a vertex `a : Q` read as an object of
  -- `CategoryTheory.Paths Q`, so it is not type-correct at `instances` transparency: neither `rw`
  -- nor `simp` can build a motive for it, and `change` is the only way to state the underlying
  -- equality of finitely supported functions.
  change (indecProjRep k Q i).map p (Finsupp.single q c)
      = Finsupp.mapDomain (fun r : Quiver.Path i a ↦ r.comp p) (Finsupp.single q c)
  rw [Finsupp.mapDomain_single, indecProjRep_map_single]

variable (k) in
/-- The paths `i → j` are a `k`-basis of the vector space that `Pᵢ` puts at `j`. This is the handle
on `(Pᵢ)_j`: the construction of `Pᵢ` is opaque, and the lemmas below name the elements of `(Pᵢ)_j`
through this basis. -/
noncomputable def indecProjRepBasis (i j : Q) :
    Module.Basis (Quiver.Path i j) k ((indecProjRep k Q i).obj j) :=
  Finsupp.basisSingleOne

/-- **A path acts on `Pᵢ` by concatenation**: it carries the basis vector of a path `q : i → a` to
the basis vector of the concatenation `q.comp p`. -/
@[simp]
theorem indecProjRep_map_basis (i : Q) {a b : Q} (p : Quiver.Path a b) (q : Quiver.Path i a) :
    (indecProjRep k Q i).map p (indecProjRepBasis k i a q) = indecProjRepBasis k i b (q.comp p) :=
  indecProjRep_map_single i p q 1

instance finiteDimensional_indecProjRep_obj (i j : Q) [Finite (Quiver.Path i j)] :
    FiniteDimensional k ((indecProjRep k Q i).obj j) :=
  Module.Finite.of_basis (indecProjRepBasis k i j)

/-- The dimension vector of `Pᵢ` counts, at each vertex, the paths from `i` to it. With infinitely
many paths `i → j` both sides are `0`, by the conventions for `Module.finrank` and `Nat.card`. -/
theorem dimVector_indecProjRep (i j : Q) :
    dimVector (indecProjRep k Q i) j = Nat.card (Quiver.Path i j) := by
  rw [dimVector_apply, Paths.of_obj, Module.finrank_eq_nat_card_basis (indecProjRepBasis k i j)]

/-! ### The universal property -/

/-- The morphism `Pᵢ ⟶ M` determined by an element `x` of `M` at the vertex `i`: it sends the basis
element of a path `p : i → j` to the image of `x` under the action of `p`. -/
noncomputable def indecProjRepHom (i : Q) (M : QuiverRep k Q) (x : M.obj i) :
    indecProjRep k Q i ⟶ M where
  app j := ModuleCat.ofHom (Finsupp.linearCombination k fun p : Quiver.Path i j ↦ M.map p x)
  naturality {a b} p := by
    have hcomp : ∀ q : Quiver.Path i a, (M.map p) ((M.map q) x) = M.map (q.comp p) x := fun q ↦
      (congrArg (fun g : M.obj i ⟶ M.obj b ↦ g x) (M.map_comp q p)).symm
    rw [indecProjRep_map]
    exact ModuleCat.hom_ext (Finsupp.lmapDomain_linearCombination (R := k)
      (v := fun q : Quiver.Path i a ↦ M.map q x) (v' := fun r : Quiver.Path i b ↦ M.map r x)
      (fun q : Quiver.Path i a ↦ q.comp p) (M.map p).hom hcomp)

/-- The morphism attached to `x : Mᵢ` sends the basis vector of a path `p` to the action of `p`
on `x`. -/
@[simp]
theorem indecProjRepHom_app_basis (i : Q) (M : QuiverRep k Q) (x : M.obj i) (j : Q)
    (p : Quiver.Path i j) :
    (indecProjRepHom i M x).app j (indecProjRepBasis k i j p) = M.map p x := by
  have h : (indecProjRepHom i M x).app j (indecProjRepBasis k i j p) = (1 : k) • M.map p x :=
    Finsupp.linearCombination_single k 1 p
  rwa [one_smul] at h

-- Not `@[simp]`: `simp` proves this outright, from `indecProjRepHom_app_basis` and
-- `QuiverRep.map_nil`, so tagging it is a simp-normal-form violation (`simpNF`). It is kept as a
-- named lemma because it is one half of the universal property below.
/-- The morphism attached to `x : Mᵢ` sends the basis vector of the trivial path back to `x`. -/
theorem indecProjRepHom_app_nil (i : Q) (M : QuiverRep k Q) (x : M.obj i) :
    (indecProjRepHom i M x).app i (indecProjRepBasis k i i Quiver.Path.nil) = x := by
  simp

/-- A morphism out of `Pᵢ` is determined by the image of the basis vector of the trivial path
at `i`. -/
@[simp]
theorem indecProjRepHom_app_nil_self {i : Q} {M : QuiverRep k Q} (f : indecProjRep k Q i ⟶ M) :
    indecProjRepHom i M (f.app i (indecProjRepBasis k i i Quiver.Path.nil)) = f := by
  refine NatTrans.ext (funext fun j ↦ ModuleCat.hom_ext
    ((indecProjRepBasis k i j).ext fun p ↦ ?_))
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality p))
    (indecProjRepBasis k i i Quiver.Path.nil)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    indecProjRep_map_basis, Quiver.Path.nil_comp] at h
  simp only [indecProjRepHom_app_basis, h]

/-- **`Pᵢ` represents evaluation at `i`.** A morphism out of `Pᵢ` is determined by, and can be
prescribed by, the image of the basis vector of the trivial path at `i`; the bijection is
`k`-linear. -/
noncomputable def indecProjRepHomEquiv (i : Q) (M : QuiverRep k Q) :
    (indecProjRep k Q i ⟶ M) ≃ₗ[k] M.obj i where
  toFun f := f.app i (indecProjRepBasis k i i Quiver.Path.nil)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := indecProjRepHom i M x
  left_inv f := indecProjRepHom_app_nil_self f
  right_inv x := indecProjRepHom_app_nil i M x

/-- The basis vector of the trivial path is the element of `Pᵢ` at `i` that the universal property
picks out. -/
@[simp]
theorem indecProjRepHomEquiv_apply (i : Q) (M : QuiverRep k Q) (f : indecProjRep k Q i ⟶ M) :
    indecProjRepHomEquiv i M f = f.app i (indecProjRepBasis k i i Quiver.Path.nil) :=
  (rfl)

@[simp]
theorem indecProjRepHomEquiv_symm_apply (i : Q) (M : QuiverRep k Q) (x : M.obj i) :
    (indecProjRepHomEquiv i M).symm x = indecProjRepHom i M x :=
  (rfl)

-- Not `@[simp]`: `simp` already proves this from `indecProjRepHomEquiv_apply` and
-- `CategoryTheory.NatTrans.comp_app`, so tagging it is a `simpNF` violation.
/-- The universal property is natural in the target: postcomposition with `g` corresponds to
applying `g` at `i`. -/
theorem indecProjRepHomEquiv_comp (i : Q) {M N : QuiverRep k Q} (f : indecProjRep k Q i ⟶ M)
    (g : M ⟶ N) :
    indecProjRepHomEquiv i N (f ≫ g) = g.app i (indecProjRepHomEquiv i M f) :=
  (rfl)

/-- **The representations `Pᵢ` are projective.** A morphism out of `Pᵢ` lifts along any
epimorphism, because it is determined by a single element of the target at `i` and an epimorphism
of representations is surjective there. -/
instance projective_indecProjRep (i : Q) : Projective (indecProjRep k Q i) where
  factors {E X} f e he := by
    obtain ⟨y, hy⟩ :=
      (ModuleCat.epi_iff_surjective (e.app i)).mp inferInstance (indecProjRepHomEquiv i X f)
    refine ⟨(indecProjRepHomEquiv i E).symm y, (indecProjRepHomEquiv i X).injective ?_⟩
    rw [indecProjRepHomEquiv_comp, LinearEquiv.apply_symm_apply, hy]

/-- Morphisms out of `Pᵢ` are as many as the elements of the target at `i`: the dimension of
`Hom(Pᵢ, M)` is the `i`-th entry of the dimension vector of `M`. -/
theorem finrank_hom_indecProjRep (i : Q) (M : QuiverRep k Q) :
    Module.finrank k (indecProjRep k Q i ⟶ M) = dimVector M i := by
  rw [dimVector_apply]
  exact (indecProjRepHomEquiv i M).finrank_eq

/-- **The path-counting form of the Cartan matrix of a path algebra**: the dimension of
`Hom(Pᵢ, Pⱼ)` is the number of paths `j → i`. -/
theorem finrank_hom_indecProjRep_indecProjRep (i j : Q) :
    Module.finrank k (indecProjRep k Q i ⟶ indecProjRep k Q j) = Nat.card (Quiver.Path j i) := by
  rw [finrank_hom_indecProjRep, dimVector_indecProjRep]

/-- The representation `Pᵢ` is nonzero: the basis vector of the trivial path at `i` is a nonzero
element of `(Pᵢ)_i`. -/
theorem not_isZero_indecProjRep (i : Q) : ¬ IsZero (indecProjRep k Q i) := by
  intro h
  letI := ModuleCat.subsingleton_of_isZero (h.obj i)
  exact (indecProjRepBasis k i i).ne_zero Quiver.Path.nil (Subsingleton.elim _ _)

end TauCeti
