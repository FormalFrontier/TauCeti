/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The injective representation at a vertex of a quiver

For a vertex `i` of a quiver `Q`, the representation `Iᵢ` puts the space of *all* `k`-valued
functions on the paths `j → i` at the vertex `j`, a path `p` acting by precomposition,
`(p · x) q = x (p.comp q)`. Under the identification of representations with left modules over the
path algebra it is the `k`-dual `D(eᵢ · kQ)` of the right ideal spanned by the paths ending at `i`.

## Main definitions

* `TauCeti.indecInjRep k Q i`: the representation `Iᵢ`.
* `TauCeti.indecInjRepHom`: the morphism `M ⟶ Iᵢ` determined by a linear functional on `M` at `i`.

## Main results

* `TauCeti.indecInjRepHomEquiv`: `Iᵢ` **represents the dual of evaluation at `i`**, by the
  `k`-linear isomorphism `(M ⟶ Iᵢ) ≃ₗ[k] Module.Dual k Mᵢ` sending a morphism to the functional
  reading off its value on the trivial path. This is the universal property from which everything
  else here follows, and it is dual to `TauCeti.indecProjRepHomEquiv`.
* `TauCeti.injective_indecInjRep`: `Iᵢ` is an injective object of `TauCeti.QuiverRep k Q`.
* `TauCeti.dimVector_indecInjRep`: the dimension vector of `Iᵢ` counts the paths into `i`, and
  `TauCeti.not_isZero_indecInjRep`: `Iᵢ` is nonzero.
* `TauCeti.finrank_hom_indecInjRep_indecInjRep`: `dim Hom(Iᵢ, Iⱼ)` is the number of paths `j → i`,
  the same path count as `TauCeti.finrank_hom_indecProjRep_indecProjRep`.

## Implementation notes

The name `indecInjRep` is the one the roadmap pins for this object. As with the projectives,
indecomposability is *not* proved here: it needs the Krull-Schmidt theory of Layer 2, which is not
yet available. What is proved is injectivity, and the universal property that makes `Iᵢ` the
representing object of the contravariant functor `M ↦ Module.Dual k Mᵢ`; both are independent of any
finiteness assumption on `Q`, so no such assumption is made.

`Iᵢ` puts the **product** `Quiver.Path j i → k` at `j`, not the free module on the paths `j → i`.
The two agree exactly when there are finitely many paths `j → i`, and the product is the right
choice: it is the full `k`-dual of the span of the paths ending at `i`, and only the product
corepresents `Module.Dual k Mᵢ` on representations with infinite-dimensional vertex spaces. The
dimension count `TauCeti.dimVector_indecInjRep` is nevertheless unconditional, because
`Module.finrank` of an infinite-dimensional space and `Nat.card` of an infinite type are both `0`.

Because the vertex spaces are function types rather than `Finsupp`s, no basis is needed to name
their elements: every lemma below is stated on the value of a function at a path, and `Iᵢ` admits a
uniform description of the action of a path, `TauCeti.indecInjRep_map_apply`, which
`TauCeti.indecProjRep_map_basis` can only give on basis vectors.

`Iᵢ` is built by `CategoryTheory.Paths.lift`, so only its value on arrows is written down and
Mathlib supplies functoriality along path concatenation. `indecInjRep` is the one definition here
that exposes its body: that is what makes `(Iᵢ)_j` *definitionally* the function type
`Quiver.Path j i → k`, so an element of it can be applied to a path with no transport in the way,
which is the point of choosing a function type over a `Finsupp` here. The morphism it receives and
the universal-property equivalence keep their bodies sealed; their characteristic lemmas
`TauCeti.indecInjRepHom_app_apply`, `TauCeti.indecInjRepHomEquiv_apply` and
`TauCeti.indecInjRepHomEquiv_symm_apply` are the whole public interface.

A vertex `i : Q` is used below as an object of the free category `CategoryTheory.Paths Q`, and
`(Iᵢ)_j` is the function type `Quiver.Path j i → k` only by unfolding `indecInjRep` and
`CategoryTheory.Paths.lift`. Goals that cross that identification are therefore not reached by
`ModuleCat.hom_ofHom`, `LinearMap.pi_apply` or `LinearMap.proj_apply`, which have nothing to match
on; the two proofs inside `TauCeti.indecInjRepHom` and `TauCeti.indecInjRepHomEquiv` that have to
cross it do so by `change`, and each says in a comment which definitional equality it is recording.

The vector space `(Iᵢ)_j` lives in the universe of `Quiver.Path j i → k`, which is larger than the
universe of `k` unless the vertex and arrow types are small. The vertex simple `Sᵢ` of
`TauCeti.RepresentationTheory.Quiver.Representation.Simple` is built on `k` itself, so the two
objects sit in a common category only when those universes agree, and the embedding
`Sᵢ ↪ Iᵢ` is therefore not stated here, exactly as the surjection `Pᵢ ↠ Sᵢ` is not stated in
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic`; both are stated in
`TauCeti.RepresentationTheory.Quiver.Representation.Cover`, where those universes are aligned.

## References

This implements the indecomposable injectives of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

/-- **The injective representation at a vertex** `Iᵢ`: the `k`-valued functions on the paths
`j → i` at the vertex `j`, an arrow acting by prepending itself to a path. Under the identification
of representations with left modules over the path algebra this is the `k`-dual `D(eᵢ · kQ)` of the
right ideal spanned by the paths ending at `i`. -/
@[expose] def indecInjRep (i : Q) : QuiverRep k Q :=
  Paths.lift
    { obj := fun j ↦ ModuleCat.of k (Quiver.Path j i → k)
      map := fun {_ b} e ↦
        ModuleCat.ofHom (LinearMap.funLeft k k fun q : Quiver.Path b i ↦ e.toPath.comp q) }

variable {k Q}

/-- An arrow acts on `Iᵢ` by prepending it to a path. Private: `indecInjRep_map_apply` is the
public, element-level form, and is what every later proof uses. -/
private theorem indecInjRep_map_toPath (i : Q) {a b : Q} (e : a ⟶ b) :
    (indecInjRep k Q i).map e.toPath
      = ModuleCat.ofHom (LinearMap.funLeft k k fun q : Quiver.Path b i ↦ e.toPath.comp q) :=
  Paths.lift_toPath _ e

/-- **A path acts on `Iᵢ` by precomposition**: the value of `p · x` on a path `q : b → i` is the
value of `x` on the concatenation `p.comp q`. -/
@[simp]
theorem indecInjRep_map_apply (i : Q) {a b : Q} (p : Quiver.Path a b)
    (x : Quiver.Path a i → k) (q : Quiver.Path b i) :
    (indecInjRep k Q i).map p x q = x (p.comp q) := by
  induction p with
  | nil =>
    rw [QuiverRep.map_nil]
    -- The identity component is indexed by `(Paths.of Q).obj _`; expose its definitional
    -- identification with the underlying vertex before rewriting path concatenation.
    change x q = x (Quiver.Path.nil.comp q)
    rw [Quiver.Path.nil_comp]
  | cons p e ih =>
    have hcons : (indecInjRep k Q i).map (p.cons e)
        = (indecInjRep k Q i).map p ≫ (indecInjRep k Q i).map e.toPath :=
      (indecInjRep k Q i).map_comp p e.toPath
    rw [hcons]
    -- `ModuleCat.comp_apply` cannot cross the `Paths.of` object wrapper, so expose the component
    -- types definitionally before applying the explicit arrow-action lemma.
    change (indecInjRep k Q i).map e.toPath ((indecInjRep k Q i).map p x) q =
      x ((p.cons e).comp q)
    rw [indecInjRep_map_toPath]
    exact (ih (e.toPath.comp q)).trans
      (congrArg x (Quiver.Path.comp_assoc p e.toPath q).symm)

/-- The dimension of the vector space `Iᵢ` puts at `j` is the number of paths `j → i`. With
infinitely many such paths both sides are `0`, by the conventions for `Module.finrank` and
`Nat.card`. -/
theorem finrank_indecInjRep_obj (i j : Q) :
    Module.finrank k ((indecInjRep k Q i).obj j) = Nat.card (Quiver.Path j i) := by
  -- `(Iᵢ)_j` is by construction the full `k`-dual of the free module on the paths `j → i`.
  let e : ((indecInjRep k Q i).obj j) ≃ₗ[k] Module.Dual k (Quiver.Path j i →₀ k) :=
    Finsupp.llift (M := k) (R := k) (S := k) (X := Quiver.Path j i)
  rw [e.finrank_eq, Subspace.dual_finrank_eq,
    Module.finrank_eq_nat_card_basis
      (Finsupp.basisSingleOne : Module.Basis (Quiver.Path j i) k _)]

instance finiteDimensional_indecInjRep_obj (i j : Q) [Finite (Quiver.Path j i)] :
    FiniteDimensional k ((indecInjRep k Q i).obj j) :=
  Module.Finite.pi

/-- The dimension vector of `Iᵢ` counts, at each vertex, the paths from it to `i`. Together with
`TauCeti.dimVector_indecProjRep` this says that the dimension vectors of the injectives are the
transposes of the dimension vectors of the projectives. -/
theorem dimVector_indecInjRep (i j : Q) :
    dimVector (indecInjRep k Q i) j = Nat.card (Quiver.Path j i) := by
  rw [dimVector_apply, Paths.of_obj]
  exact finrank_indecInjRep_obj i j

/-- The dimension vector of `Iᵢ` is the transpose of the dimension vector of `Pⱼ`: both count the
paths `j → i`. -/
theorem dimVector_indecInjRep_eq_dimVector_indecProjRep (i j : Q) :
    dimVector (indecInjRep k Q i) j = dimVector (indecProjRep k Q j) i := by
  rw [dimVector_indecInjRep, dimVector_indecProjRep]

/-! ### The universal property -/

-- A representation is now indexed by the free category `Paths Q`. Mathlib's `Paths.of Q` is
-- definitionally the identity on objects, but elaboration no longer unfolds that fact
-- automatically in dependent component types. The explicit `(Paths.of Q).obj` annotations and
-- `change` steps below expose that canonical object identification without adding a parallel API.

/-- The morphism `M ⟶ Iᵢ` determined by a linear functional `φ` on `M` at the vertex `i`: at the
vertex `j` it sends `x` to the function reading off `φ` of the action of a path `j → i` on `x`. -/
def indecInjRepHom (i : Q) (M : QuiverRep k Q)
    (φ : Module.Dual k (M.obj ((Paths.of Q).obj i))) :
    M ⟶ indecInjRep k Q i where
  app j := ModuleCat.ofHom (LinearMap.pi fun q : Quiver.Path (V := Q) j i ↦ φ ∘ₗ (M.map q).hom)
  naturality {a b} p := by
    change Q at a b
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun q ↦ ?_)
    have hcomp : (M.map q) ((M.map p) x) = M.map (p.comp q) x :=
      (congrArg (fun g : M.obj a ⟶ M.obj i ↦ g x) (M.map_comp p q)).symm
    -- `ModuleCat.hom_ofHom` and `LinearMap.pi_apply` cannot rewrite here: `(Iᵢ)_b` is the function
    -- type `Quiver.Path b i → k` only after `indecInjRep` and `Paths.lift` unfold, so neither side
    -- is syntactically an `ofHom` of a `LinearMap.pi` into a pi type. The `change` records that
    -- unfolding: each component of this morphism *is* `x ↦ fun r ↦ φ (M.map r x)`.
    change φ ((M.map q) ((M.map p) x))
      = (indecInjRep k Q i).map p (fun r : Quiver.Path (V := Q) a i ↦ φ ((M.map r) x)) q
    rw [indecInjRep_map_apply]
    exact congrArg φ hcomp

/-- The morphism attached to `φ : Module.Dual k Mᵢ` sends `x` at the vertex `j` to the function
whose value on a path `q : j → i` is `φ` of the action of `q` on `x`. -/
@[simp]
theorem indecInjRepHom_app_apply (i : Q) (M : QuiverRep k Q)
    (φ : Module.Dual k (M.obj ((Paths.of Q).obj i))) (j : Q)
    (x : M.obj ((Paths.of Q).obj j)) (q : Quiver.Path j i) :
    (indecInjRepHom i M φ).app ((Paths.of Q).obj j) x q = φ (M.map q x) :=
  -- The parentheses are load-bearing, as in `TauCeti.indecProjRepHomEquiv_apply`: `indecInjRepHom`
  -- does not expose its body, and the bare-`rfl` elaborator refuses to unfold a definition whose
  -- body is sealed, even inside the module that defines it. The same holds of the three `(rfl)`
  -- proofs below.
  (rfl)

/-- **A morphism into `Iᵢ` is determined by its value on the trivial path at `i`**: naturality
propagates that single functional to every vertex. -/
theorem hom_indecInjRep_app_apply (i : Q) {M : QuiverRep k Q} (f : M ⟶ indecInjRep k Q i) (j : Q)
    (x : M.obj ((Paths.of Q).obj j)) (q : Quiver.Path j i) :
    f.app ((Paths.of Q).obj j) x q =
      f.app ((Paths.of Q).obj i) (M.map q x) Quiver.Path.nil := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality q)) x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  change f.app ((Paths.of Q).obj i) (M.map q x) =
    (indecInjRep k Q i).map q (f.app ((Paths.of Q).obj j) x) at h
  have hn := congrFun h Quiver.Path.nil
  have hmap :
      (indecInjRep k Q i).map q (f.app ((Paths.of Q).obj j) x) Quiver.Path.nil =
        f.app ((Paths.of Q).obj j) x (q.comp Quiver.Path.nil) :=
    indecInjRep_map_apply i q _ _
  have hn' := hn.trans hmap
  rw [Quiver.Path.comp_nil] at hn'
  exact hn'.symm

/-- A morphism into `Iᵢ` is recovered from the functional it induces at `i`. -/
@[simp]
theorem indecInjRepHom_app_nil_self {i : Q} {M : QuiverRep k Q} (f : M ⟶ indecInjRep k Q i) :
    indecInjRepHom i M
      (LinearMap.proj Quiver.Path.nil ∘ₗ (f.app ((Paths.of Q).obj i)).hom) = f := by
  refine NatTrans.ext (funext fun j ↦ ?_)
  change Q at j
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  change M.obj ((Paths.of Q).obj j) at x
  refine funext fun q ↦ ?_
  change (indecInjRepHom i M
      (LinearMap.proj Quiver.Path.nil ∘ₗ (f.app ((Paths.of Q).obj i)).hom)).app
        ((Paths.of Q).obj j) x q =
    f.app ((Paths.of Q).obj j) x q
  rw [indecInjRepHom_app_apply]
  exact (hom_indecInjRep_app_apply i f j x q).symm

/-- **`Iᵢ` represents the dual of evaluation at `i`.** A morphism into `Iᵢ` is determined by, and
can be prescribed by, the linear functional reading off its value on the trivial path at `i`; the
bijection is `k`-linear. This is the exact dual of `TauCeti.indecProjRepHomEquiv`. -/
def indecInjRepHomEquiv (i : Q) (M : QuiverRep k Q) :
    (M ⟶ indecInjRep k Q i) ≃ₗ[k] Module.Dual k (M.obj ((Paths.of Q).obj i)) where
  toFun f := LinearMap.proj Quiver.Path.nil ∘ₗ (f.app ((Paths.of Q).obj i)).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := indecInjRepHom i M φ
  left_inv f := indecInjRepHom_app_nil_self f
  right_inv φ := by
    refine LinearMap.ext fun x ↦ ?_
    -- `LinearMap.proj_apply` cannot rewrite here: `(Iᵢ)_i` is the function type
    -- `Quiver.Path i i → k` only after `indecInjRep` and `Paths.lift` unfold, so the `proj` in the
    -- goal is not syntactically a projection of a pi type. The `change` records that unfolding:
    -- applying `LinearMap.proj Quiver.Path.nil ∘ₗ (·.app i).hom` to `x` *is* evaluating the
    -- component at `i` on the trivial path.
    change φ (M.map (Quiver.Path.nil : Quiver.Path i i) x) = φ x
    rw [QuiverRep.map_nil]
    rfl

@[simp]
theorem indecInjRepHomEquiv_apply (i : Q) (M : QuiverRep k Q) (f : M ⟶ indecInjRep k Q i)
    (x : M.obj ((Paths.of Q).obj i)) :
    indecInjRepHomEquiv i M f x =
      f.app ((Paths.of Q).obj i) x Quiver.Path.nil :=
  (rfl)

@[simp]
theorem indecInjRepHomEquiv_symm_apply (i : Q) (M : QuiverRep k Q)
    (φ : Module.Dual k (M.obj ((Paths.of Q).obj i))) :
    (indecInjRepHomEquiv i M).symm φ = indecInjRepHom i M φ :=
  (rfl)

/-- The universal property is natural in the source: precomposition with `g` corresponds to
precomposition of functionals with `g` at `i`. -/
theorem indecInjRepHomEquiv_comp (i : Q) {M N : QuiverRep k Q} (g : M ⟶ N)
    (f : N ⟶ indecInjRep k Q i) :
    indecInjRepHomEquiv i M (g ≫ f) =
      indecInjRepHomEquiv i N f ∘ₗ (g.app ((Paths.of Q).obj i)).hom :=
  (rfl)

/-- **The representations `Iᵢ` are injective.** A morphism into `Iᵢ` is a single linear functional
on the source at `i`, a monomorphism of representations is injective there, and a linear functional
extends along an injective linear map of vector spaces. -/
instance injective_indecInjRep (i : Q) : Injective (indecInjRep k Q i) where
  factors {X Y} f g _ := by
    have hinj : Function.Injective (g.app ((Paths.of Q).obj i)).hom :=
      (ModuleCat.mono_iff_injective (g.app ((Paths.of Q).obj i))).mp inferInstance
    obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective hinj (indecInjRepHomEquiv i X f)
    exact ⟨(indecInjRepHomEquiv i Y).symm ψ, (indecInjRepHomEquiv i X).injective (by
      rw [indecInjRepHomEquiv_comp, LinearEquiv.apply_symm_apply]
      exact hψ)⟩

/-- Morphisms into `Iᵢ` are as many as the linear functionals on the source at `i`: the dimension
of `Hom(M, Iᵢ)` is the `i`-th entry of the dimension vector of `M`. -/
theorem finrank_hom_indecInjRep (i : Q) (M : QuiverRep k Q) :
    Module.finrank k (M ⟶ indecInjRep k Q i) = dimVector M i := by
  rw [dimVector_apply]
  change Module.finrank k (M ⟶ indecInjRep k Q i) =
    Module.finrank k (M.obj ((Paths.of Q).obj i))
  rw [(indecInjRepHomEquiv i M).finrank_eq, Subspace.dual_finrank_eq]

/-- **The path-counting form of the Cartan matrix, read on injectives**: the dimension of
`Hom(Iᵢ, Iⱼ)` is the number of paths `j → i`, the same count as for `Hom(Pⱼ, Pᵢ)`. -/
theorem finrank_hom_indecInjRep_indecInjRep (i j : Q) :
    Module.finrank k (indecInjRep k Q i ⟶ indecInjRep k Q j) = Nat.card (Quiver.Path j i) := by
  rw [finrank_hom_indecInjRep, dimVector_indecInjRep]

/-- The representation `Iᵢ` is nonzero: the function that is `1` on every path is a nonzero element
of `(Iᵢ)_i`, since the trivial path is one of them. -/
theorem not_isZero_indecInjRep (i : Q) : ¬ IsZero (indecInjRep k Q i) := by
  intro h
  letI : Subsingleton ((indecInjRep k Q i).obj i) := ModuleCat.subsingleton_of_isZero (h.obj i)
  have h1 : (fun _ : Quiver.Path i i ↦ (1 : k)) = (fun _ : Quiver.Path i i ↦ (0 : k)) :=
    Subsingleton.elim (α := ((indecInjRep k Q i).obj i : Type _)) _ _
  exact one_ne_zero (congrFun h1 Quiver.Path.nil)

end TauCeti
