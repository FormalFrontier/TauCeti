/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced
public import TauCeti.RepresentationTheory.Induction.Restriction

/-!
# Transitivity of induction and coinduction

This file records restriction and coinduction in stages for representations along composable monoid
homomorphisms, and induction in stages along composable group homomorphisms. It obtains the natural
isomorphisms from the equality of restriction functors `TauCeti.resFunctor_comp` and
Mathlib's induction--restriction and restriction--coinduction adjunctions. This is the categorical
core used by the subgroup form of induction in the induction and Mackey-theory roadmap.

Uniqueness of adjoints produces those isomorphisms without ever saying what they *do*, and a
comparison map known only up to an abstract adjoint characterisation is of no use to a computation
with induced characters or with the Mackey decomposition, both of which have to follow a chosen
coset representative through the isomorphism. The second half of this file therefore evaluates them
on representatives:

`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ ↦ ⟦ψ(h) κ ⊗ₜ a⟧`,  `⟦κ ⊗ₜ a⟧ ↦ ⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`

for induction, and dually `F ↦ (κ ↦ F κ 1)`, `f ↦ (κ ↦ (h ↦ f (ψ(h) κ)))` for coinduction.

The route to these formulas is the mates calculus rather than an unfolding of
`Adjunction.leftAdjointCompIso`. The identity `CategoryTheory.unit_conjugateEquiv` says that
conjugate natural transformations agree after composing with the two units; since the unit of the
induction--restriction adjunction is the generator map `a ↦ ⟦1 ⊗ₜ a⟧` and `resFunctorCompIso` is
the identity on vectors, that identity computes the *inverse* isomorphism
`(indFunctorCompIso φ ψ).inv` on the generator `⟦1 ⊗ₜ a⟧` of the singly induced representation,
which is where both units land. Equivariance then spreads that single value over all group
coordinates, giving the inverse on every generator, and the forward formula follows by inverting
it. Both steps use the relation `⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` inside the coinvariants
(`TauCeti.indV_mk_ind_mk`), which also says that the elements with inner coordinate `1`
generate, so that the formula determines the map. The coinduction side is the same argument run
through `CategoryTheory.conjugateEquiv_counit_symm` and the counit, which is evaluation at `1`;
there it is the forward isomorphism that the counits compute, and the inverse that is derived.

## Main definitions

* `TauCeti.Rep.resFunctorCompIso`, `TauCeti.Rep.indFunctorCompIso`,
  `TauCeti.Rep.coindFunctorCompIso`: restriction, induction and coinduction in stages, as natural
  isomorphisms of functors.

## Main statements

* `TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk` and
  `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`: **induction in stages on representatives**,
  the two directions of the isomorphism computed on the generators of the induced representation.
* `TauCeti.Rep.eq_indFunctorCompIso_hom_app`: those formulas pin the isomorphism down. A morphism
  of representations sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to `⟦1 ⊗ₜ a⟧` for every `a : A` *is* the
  induction-in-stages isomorphism, which is how a comparison map built by hand is identified with
  the adjoint one.
* `TauCeti.Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply` and
  `TauCeti.Rep.coindFunctorCompIso_inv_app_hom_apply_coe_apply_coe_apply`: **coinduction in stages
  on functions**, the dual formulas.
* `TauCeti.indV_mk_apply_inv`, `TauCeti.indV_mk_ind_mk` and `TauCeti.indV_ind_hom_ext`: the
  coinvariants relation moving the group action of an induced representation into its group
  coordinate, its form for a twice-induced representation, and the resulting extensionality
  principle.
* `TauCeti.Rep.ind_hom_apply_mk` and `TauCeti.Rep.ind_ind_hom_ext`: a morphism out of an induced
  representation is the translate of its value at the group coordinate `1`, so two morphisms out of
  a twice-induced representation already agree once they agree on `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`.

## Implementation notes

The four representative formulas are tagged with the pre-order `@[simp↓]` rather than `@[simp]`,
like `TauCeti.Rep.resFunctorCompIso_hom_app_apply` above them. Their left-hand sides are readable
but not in post-order `simp`-normal form: on the induction side `Representation.IndV.mk φ ρ h` is a
reducible abbreviation that `simp` unfolds to `Representation.Coinvariants.mk _ (single h 1 ⊗ₜ a)`,
and on the coinduction side `simp` rewrites the source and target of
`(coindFunctorCompIso φ ψ).hom.app A`, which appear as implicit arguments, with
`CategoryTheory.Functor.comp_obj` and `Rep.coindFunctor_obj`. A plain `@[simp]` tag is therefore
rejected by the `simpNF` linter and would never fire, and restating the formulas in the linter's
normal form is not a way out: that form pairs rewritten implicit type arguments with an unrewritten
`Representation.IntertwiningMap.instFunLike` instance argument, which no surface syntax elaborates
to. `@[simp↓]` fires the lemma before those subterms are normalised, so `simp` closes goals stated
in the readable form, and `rw` and `exact` still apply the lemmas as usual.

## References

This is the "explicit representative-level formula for the isomorphism" that Layer 0 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` asks for alongside
transitivity of induction, "rather than leaving it an abstract adjoint comparison". See
C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §10, and J.-P. Serre,
*Linear Representations of Finite Groups*, §7.
-/

public section

namespace TauCeti

open CategoryTheory

universe t u v w x y z

variable {k : Type u} {G : Type v} {H : Type w} {K : Type x}

/-! ### Generators of induced and coinduced representations

The lemmas of this section speak only about `Representation.IndV` and `Representation.coindV` and
mention no object of `Rep`, so they are not declared in the `Rep` namespace. They also stay out of a
`Representation` namespace: `scripts/lint-dot-notation.py` rejects a Mathlib type namespace nested
inside `TauCeti`, because the resulting name would not give dot notation on `Representation`. -/

section IndV

variable [CommRing k] [Group G] [Group H] [Group K]

/-- Moving the group action out of an induced representation into its group coordinate:
`⟦κ ⊗ₜ τ h⁻¹ y⟧ = ⟦ψ(h) κ ⊗ₜ y⟧`. This is `Representation.Coinvariants.mk_tmul_inv` for the
tensor product defining `Representation.IndV`. -/
lemma indV_mk_apply_inv {W : Type*} [AddCommGroup W] [Module k W] (ψ : H →* K)
    (τ : Representation k H W) (h : H) (κ : K) (y : W) :
    Representation.IndV.mk ψ τ κ (τ h⁻¹ y) = Representation.IndV.mk ψ τ (ψ h * κ) y := by
  -- `Representation.Coinvariants.mk_tmul_inv` is the `simp` lemma doing the work; the extra
  -- rewrite evaluates the left regular representation on the group coordinate.
  simp [Representation.ofMulAction_single]

/-- Moving the inner group coordinate of a twice-induced representation out to the outer one:
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Every element of `Ind_ψ (Ind_φ A)` is therefore a sum of
elements whose inner coordinate is `1`, which is what makes the two representative formulas below
determine the induction-in-stages isomorphism. -/
lemma indV_mk_ind_mk {V : Type*} [AddCommGroup V] [Module k V] (φ : G →* H) (ψ : H →* K)
    (ρ : Representation k G V) (h : H) (κ : K) (a : V) :
    Representation.IndV.mk ψ (Representation.ind φ ρ) κ (Representation.IndV.mk φ ρ h a) =
      Representation.IndV.mk ψ (Representation.ind φ ρ) (ψ h * κ)
        (Representation.IndV.mk φ ρ 1 a) := by
  rw [← indV_mk_apply_inv ψ (Representation.ind φ ρ) h κ, Representation.ind_mk, inv_inv, one_mul]

/-- Two linear maps out of a twice-induced representation agree as soon as they agree on the
elements `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` whose inner group coordinate is `1`. -/
lemma indV_ind_hom_ext {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (φ : G →* H) (ψ : H →* K) (ρ : Representation k G V)
    {f g : Representation.IndV ψ (Representation.ind φ ρ) →ₗ[k] W}
    (hfg : ∀ (κ : K) (a : V),
      f (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ 1 a)) =
        g (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ 1 a))) :
    f = g := by
  have key : ∀ (κ : K) (h : H) (a : V),
      f (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ h a)) =
        g (Representation.IndV.mk ψ (Representation.ind φ ρ) κ
          (Representation.IndV.mk φ ρ h a)) := fun κ h a => by
    rw [indV_mk_ind_mk φ ψ ρ h κ a]
    exact hfg _ a
  exact Representation.IndV.hom_ext ψ _ fun κ =>
    Representation.IndV.hom_ext φ _ fun h => LinearMap.ext fun a => key κ h a

end IndV

section CoindV

variable [CommRing k] [Monoid G] [Monoid H]

/-- The coinduced action translates the argument of a function: `(h • f) h₁ = f (h₁ * h)`. Used to
retype the values of a coinduced representation along the group action. -/
private lemma coind_ρ_apply_coe_apply {V : Type*} [AddCommGroup V] [Module k V] (φ : G →* H)
    (ρ : Representation k G V) (f : Representation.coindV φ ρ) (h h₁ : H) :
    ((Representation.coind φ ρ h) f).1 h₁ = f.1 (h₁ * h) :=
  rfl

end CoindV

namespace Rep

section Restriction

variable [Semiring k] [Monoid G] [Monoid H] [Monoid K]

/-- Restriction along two composable group homomorphisms is naturally isomorphic to restriction
along their composite.  The two functors are in fact equal (`TauCeti.resFunctor_comp`), so this is
that equality read as an isomorphism. -/
def resFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.resFunctor.{max u v w x} (k := k) ψ ⋙
      _root_.Rep.resFunctor.{max u v w x} (k := k) φ ≅
        _root_.Rep.resFunctor.{max u v w x} (k := k) (ψ.comp φ) :=
  eqToIso (resFunctor_comp ψ φ).symm

/-- The forward component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_hom_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).hom.app A) x = x :=
  by
    unfold resFunctorCompIso
    rfl

/-- The inverse component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_inv_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).inv.app A) x = x :=
  by
    unfold resFunctorCompIso
    rfl

end Restriction

section Induction

variable [CommRing k] [Group G] [Group H] [Group K]

/-- Induction in stages: induction along a composite is naturally isomorphic to successive
inductions along the two group homomorphisms. -/
noncomputable def indFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.indFunctor.{max u v w x} k φ ⋙
      _root_.Rep.indFunctor.{max u v w x} k ψ ≅
        _root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (_root_.Rep.indResAdjunction.{max u v w x} k φ)
    (_root_.Rep.indResAdjunction.{max u v w x} k ψ)
    (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (resFunctorCompIso φ ψ)

/-- The induction-in-stages isomorphism is characterized by the restriction-composition
isomorphism under the adjunction equivalence. -/
@[simp]
lemma conjugateEquiv_indFunctorCompIso_inv (φ : G →* H) (ψ : H →* K) :
    conjugateEquiv
      ((_root_.Rep.indResAdjunction.{max u v w x} k φ).comp
        (_root_.Rep.indResAdjunction.{max u v w x} k ψ))
      (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
      (indFunctorCompIso φ ψ).inv =
        (resFunctorCompIso φ ψ).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The unit of Mathlib's induction--restriction adjunction is the generator map
`a ↦ ⟦1 ⊗ₜ a⟧` of the induced representation. Used to turn the abstract adjunction identity
`unit_conjugateEquiv` into a statement about elements. -/
private lemma indResAdjunction_unit_app_hom_apply (φ : G →* H) (A : _root_.Rep.{max u w t} k G)
    (a : A) :
    ((_root_.Rep.indResAdjunction.{t} k φ).unit.app A).hom a =
      Representation.IndV.mk φ A.ρ 1 a :=
  rfl

/-- The induction-in-stages isomorphism, backwards, on the generator `⟦1 ⊗ₜ a⟧`. This is the
adjunction identity `unit_conjugateEquiv` read on elements: both units are generator maps and
`resFunctorCompIso` is the identity on vectors, so the abstract characterisation
`conjugateEquiv_indFunctorCompIso_inv` becomes this single value. -/
private lemma indFunctorCompIso_inv_app_hom_apply_mk_one (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (a : A) :
    ((indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) =
      Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a) := by
  have key := unit_conjugateEquiv
    ((_root_.Rep.indResAdjunction.{max u v w x} k φ).comp
      (_root_.Rep.indResAdjunction.{max u v w x} k ψ))
    (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (indFunctorCompIso φ ψ).inv A
  rw [conjugateEquiv_indFunctorCompIso_inv] at key
  -- Read the resulting identity of morphisms on `a`, then rewrite the composite unit into the two
  -- generator maps and delete the restriction functors, which act as the identity on vectors.
  have key := congrArg (fun f => Rep.Hom.hom f a) key
  simp only [Adjunction.comp_unit_app, _root_.Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply] at key
  rw [_root_.Rep.resMap_hom_apply, _root_.Rep.resMap_hom_apply,
    indResAdjunction_unit_app_hom_apply, indResAdjunction_unit_app_hom_apply,
    indResAdjunction_unit_app_hom_apply, resFunctorCompIso_hom_app_apply] at key
  exact key.symm

/-- A morphism out of an induced representation is the `κ⁻¹`-translate of its value at the group
coordinate `1`: it sends `⟦κ ⊗ₜ b⟧` to `Y.ρ κ⁻¹` of its value on `⟦1 ⊗ₜ b⟧`. Together with
`TauCeti.indV_ind_hom_ext` this is what lets a formula at the coordinate `1` determine a
morphism out of an induced representation. -/
lemma ind_hom_apply_mk {J : Type y} [Group J] (σ : J →* K) {B : _root_.Rep.{z} k J}
    {Y : _root_.Rep.{max u x z} k K} (f : _root_.Rep.ind σ B ⟶ Y) (κ : K) (b : B) :
    f.hom (Representation.IndV.mk σ B.ρ κ b) =
      Y.ρ κ⁻¹ (f.hom (Representation.IndV.mk σ B.ρ 1 b)) := by
  have hsrc : Representation.IndV.mk σ B.ρ κ b =
      (_root_.Rep.ind σ B).ρ κ⁻¹ (Representation.IndV.mk σ B.ρ 1 b) := by
    simp
  rw [hsrc, _root_.Rep.hom_comm_apply]

/-- Two morphisms of `K`-representations out of a twice-induced representation agree as soon as
they agree on the elements `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. This is the `Rep`-morphism companion of
`TauCeti.indV_ind_hom_ext`: equivariance removes the outer group coordinate from its
hypothesis. -/
lemma ind_ind_hom_ext (φ : G →* H) (ψ : H →* K) (A : _root_.Rep.{max u v w x} k G)
    {B : _root_.Rep.{max u v w x} k K}
    {f g : (_root_.Rep.indFunctor.{max u v w x} k φ ⋙
      _root_.Rep.indFunctor.{max u v w x} k ψ).obj A ⟶ B}
    (hfg : ∀ a : A,
      f.hom (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
          (Representation.IndV.mk φ A.ρ 1 a)) =
        g.hom (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
          (Representation.IndV.mk φ A.ρ 1 a))) :
    f = g := by
  refine _root_.Rep.hom_ext (Representation.IntertwiningMap.ext
    (indV_ind_hom_ext φ ψ A.ρ fun κ a => ?_))
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply,
    ind_hom_apply_mk ψ (B := _root_.Rep.ind φ A) f κ _,
    ind_hom_apply_mk ψ (B := _root_.Rep.ind φ A) g κ _, hfg]

/-- **Induction in stages on representatives, backwards**: the inverse of the induction-in-stages
isomorphism sends `⟦κ ⊗ₜ a⟧` to `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Tagged `@[simp↓]` rather than `@[simp]` because
`simp` unfolds the reducible `Representation.IndV.mk` in the left-hand side. -/
@[simp↓]
lemma indFunctorCompIso_inv_app_hom_apply_mk (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (κ : K) (a : A) :
    ((indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ κ a) =
      Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ 1 a) := by
  rw [ind_hom_apply_mk (ψ.comp φ) (B := A) ((indFunctorCompIso φ ψ).inv.app A) κ a,
    indFunctorCompIso_inv_app_hom_apply_mk_one]
  simp

/-- **Induction in stages on representatives**: the induction-in-stages isomorphism sends
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧` to `⟦ψ(h) κ ⊗ₜ a⟧`. This is the explicit formula the character and Mackey
computations consume, in place of the abstract adjoint comparison. Tagged `@[simp↓]` for the same
reason as `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. -/
@[simp↓]
lemma indFunctorCompIso_hom_app_hom_apply_mk_mk (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (h : H) (κ : K) (a : A) :
    ((indFunctorCompIso φ ψ).hom.app A).hom
        (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ h a)) =
      Representation.IndV.mk (ψ.comp φ) A.ρ (ψ h * κ) a := by
  have hinv := indFunctorCompIso_inv_app_hom_apply_mk φ ψ A (ψ h * κ) a
  rw [← indV_mk_ind_mk φ ψ A.ρ h κ a] at hinv
  rw [← hinv, ← _root_.Rep.comp_apply, (indFunctorCompIso φ ψ).inv_hom_id_app,
    _root_.Rep.id_apply]

/-- **The induction-in-stages isomorphism is determined by its values on the generators.** A
morphism of `K`-representations `Ind_ψ (Ind_φ A) ⟶ Ind_{ψφ} A` sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to
`⟦1 ⊗ₜ a⟧` for every `a : A` is the induction-in-stages isomorphism. This is how a comparison map
built by hand is identified with the adjoint one produced by `TauCeti.Rep.indFunctorCompIso`. -/
lemma eq_indFunctorCompIso_hom_app (φ : G →* H) (ψ : H →* K) (A : _root_.Rep.{max u v w x} k G)
    {f : (_root_.Rep.indFunctor.{max u v w x} k φ ⋙
        _root_.Rep.indFunctor.{max u v w x} k ψ).obj A ⟶
      (_root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ)).obj A}
    (hf : ∀ a : A, f.hom (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a)) = Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) :
    f = (indFunctorCompIso φ ψ).hom.app A := by
  refine ind_ind_hom_ext φ ψ A fun a => ?_
  rw [hf, indFunctorCompIso_hom_app_hom_apply_mk_mk φ ψ A 1 1 a, map_one, one_mul]

end Induction

section Coinduction

variable [CommRing k] [Monoid G] [Monoid H] [Monoid K]

/-- Coinduction in stages: successive coinductions are naturally isomorphic to coinduction along
the composite homomorphism. -/
noncomputable def coindFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.coindFunctor.{max u v w x} k φ ⋙
      _root_.Rep.coindFunctor.{max u v w x} k ψ ≅
        _root_.Rep.coindFunctor.{max u v w x} k (ψ.comp φ) := by
  let adjφ := _root_.Rep.resCoindAdjunction.{max u v w x} k φ
  let adjψ := _root_.Rep.resCoindAdjunction.{max u v w x} k ψ
  let adjφψ := adjψ.comp adjφ
  let adjψφ := _root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ)
  exact conjugateIsoEquiv adjφψ adjψφ (resFunctorCompIso φ ψ).symm

/-- The coinduction-in-stages isomorphism is characterized by the inverse
restriction-composition isomorphism under the inverse adjunction equivalence. -/
@[simp]
lemma conjugateEquiv_symm_coindFunctorCompIso_hom (φ : G →* H) (ψ : H →* K) : ((conjugateEquiv
      ((_root_.Rep.resCoindAdjunction.{max u v w x} k ψ).comp
        (_root_.Rep.resCoindAdjunction.{max u v w x} k φ))
      (_root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))).symm
      (coindFunctorCompIso φ ψ).hom) = (resFunctorCompIso φ ψ).inv := by
  unfold coindFunctorCompIso
  exact Equiv.symm_apply_apply _ _

/-- The counit of Mathlib's restriction--coinduction adjunction is evaluation at `1`. Used to turn
the abstract adjunction identity `conjugateEquiv_counit_symm` into a statement about elements. -/
private lemma resCoindAdjunction_counit_app_hom_apply (φ : G →* H) (A : _root_.Rep.{max w t} k G)
    (f : _root_.Rep.coind φ A) :
    ((_root_.Rep.resCoindAdjunction.{t} k φ).counit.app A).hom f = f.1 1 :=
  rfl

/-- The coinduction-in-stages isomorphism evaluated at `1`: it reads off the value of a doubly
coinduced function at the pair `(1, 1)`. This is the adjunction identity
`conjugateEquiv_counit_symm` read on elements, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk_one`. -/
private lemma coindFunctorCompIso_hom_app_hom_apply_coe_one (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (F : _root_.Rep.coind ψ (_root_.Rep.coind φ A)) :
    (((coindFunctorCompIso φ ψ).hom.app A).hom F).1 1 = (F.1 1).1 1 := by
  have key := conjugateEquiv_counit_symm
    ((_root_.Rep.resCoindAdjunction.{max u v w x} k ψ).comp
      (_root_.Rep.resCoindAdjunction.{max u v w x} k φ))
    (_root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))
    (coindFunctorCompIso φ ψ).hom A
  rw [conjugateEquiv_symm_coindFunctorCompIso_hom] at key
  -- Read the resulting identity of morphisms on `F`, then rewrite the composite counit into the
  -- two evaluations at `1` and delete the restriction functors, which act as the identity.
  have key := congrArg (fun f : _ ⟶ A => Rep.Hom.hom f F) key
  simp only [Adjunction.comp_counit_app, _root_.Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply] at key
  rw [_root_.Rep.resMap_hom_apply, _root_.Rep.resMap_hom_apply,
    resCoindAdjunction_counit_app_hom_apply, resCoindAdjunction_counit_app_hom_apply,
    resCoindAdjunction_counit_app_hom_apply, resFunctorCompIso_inv_app_apply] at key
  exact key

/-- **Coinduction in stages on functions**: the coinduction-in-stages isomorphism sends an
`H`-equivariant function `F : K → coind φ A`, whose values are themselves the `G`-equivariant
functions `H → A`, to `κ ↦ F κ 1`. This is the dual of
`TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk_mk`, and is obtained from its value at `1` by
`K`-equivariance. Tagged `@[simp↓]` rather than `@[simp]` because `simp` rewrites the source and
target of the isomorphism component in the left-hand side. -/
@[simp↓]
lemma coindFunctorCompIso_hom_app_hom_apply_coe_apply (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (F : _root_.Rep.coind ψ (_root_.Rep.coind φ A)) (κ : K) :
    (((coindFunctorCompIso φ ψ).hom.app A).hom F).1 κ = (F.1 κ).1 1 := by
  have hcomm := _root_.Rep.hom_comm_apply ((coindFunctorCompIso φ ψ).hom.app A) κ F
  have h1 := coindFunctorCompIso_hom_app_hom_apply_coe_one φ ψ A
    (((_root_.Rep.coindFunctor.{max u v w x} k φ ⋙
      _root_.Rep.coindFunctor.{max u v w x} k ψ).obj A).ρ κ F)
  rw [hcomm] at h1
  simp only [Functor.comp_obj, _root_.Rep.coindFunctor_obj, _root_.Rep.of_ρ] at h1
  rw [coind_ρ_apply_coe_apply, coind_ρ_apply_coe_apply] at h1
  simpa using h1

/-- **Coinduction in stages on functions, backwards**: the inverse of the coinduction-in-stages
isomorphism turns a `G`-equivariant function `f : K → A` into `κ ↦ (h ↦ f (ψ(h) κ))`, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. Tagged `@[simp↓]` for the same reason as
`TauCeti.Rep.coindFunctorCompIso_hom_app_hom_apply_coe_apply`. -/
@[simp↓]
lemma coindFunctorCompIso_inv_app_hom_apply_coe_apply_coe_apply (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (f : _root_.Rep.coind (ψ.comp φ) A) (κ : K) (h : H) :
    ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 h = f.1 (ψ h * κ) := by
  have hfF : ((coindFunctorCompIso φ ψ).hom.app A).hom
      (((coindFunctorCompIso φ ψ).inv.app A).hom f) = f := by
    rw [← _root_.Rep.comp_apply, (coindFunctorCompIso φ ψ).inv_hom_id_app, _root_.Rep.id_apply]
  have hhom : ∀ κ' : K, ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ').1 1 = f.1 κ' :=
    fun κ' => (coindFunctorCompIso_hom_app_hom_apply_coe_apply φ ψ A _ κ').symm.trans
      (congrArg (fun y : _root_.Rep.coind (ψ.comp φ) A => y.1 κ') hfF)
  have hmem := (((coindFunctorCompIso φ ψ).inv.app A).hom f).2 h κ
  simp only [_root_.Rep.coindFunctor_obj, _root_.Rep.of_ρ] at hmem
  have hx : f.1 (ψ h * κ) = ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 (1 * h) := by
    rw [← hhom (ψ h * κ), hmem, coind_ρ_apply_coe_apply]
  rw [hx, one_mul]

end Coinduction

end Rep

end TauCeti
