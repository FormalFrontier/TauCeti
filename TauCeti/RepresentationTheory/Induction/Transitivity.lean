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
the identity on vectors, that identity *is* the value of the induction-in-stages isomorphism on
`⟦1 ⊗ₜ a⟧`. Equivariance then spreads the single value over all group coordinates, using the
relation `⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` inside the coinvariants
(`TauCeti.Rep.indV_mk_ind_mk`), which also says that the elements with inner coordinate `1`
generate, so that the formula determines the map. The coinduction side is the same argument run
through `CategoryTheory.conjugateEquiv_counit_symm` and the counit, which is evaluation at `1`.

## Main definitions

* `TauCeti.Rep.resFunctorCompIso`, `TauCeti.Rep.indFunctorCompIso`,
  `TauCeti.Rep.coindFunctorCompIso`: restriction, induction and coinduction in stages, as natural
  isomorphisms of functors.

## Main statements

* `TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk` and
  `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`: **induction in stages on representatives**,
  the two directions of the isomorphism computed on the generators of the induced representation.
* `TauCeti.Rep.eq_indFunctorCompIso_hom_app`: those formulas pin the isomorphism down. A morphism
  of representations sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to `⟦1 ⊗ₜ a⟧` *is* the induction-in-stages
  isomorphism, which is how a comparison map built by hand is identified with the adjoint one.
* `TauCeti.Rep.coindFunctorCompIso_hom_app_hom_apply_apply` and
  `TauCeti.Rep.coindFunctorCompIso_inv_app_hom_apply_apply`: **coinduction in stages on functions**,
  the dual formulas.
* `TauCeti.Rep.indV_mk_ind_mk` and `TauCeti.Rep.indV_ind_hom_ext`: the coinvariants relation moving
  the inner group coordinate of a twice-induced representation out to the outer one, and the
  resulting extensionality principle.

## Implementation notes

`Representation.IndV.mk φ ρ h` is a reducible abbreviation that `simp` unfolds, so the generator
formulas below are stated with it for readability but are **not** `simp` lemmas: their left-hand
sides are not in `simp`-normal form and they would never fire. This matches Mathlib's own
`Rep.coinvariantsTensorIndHom_mk_tmul_indVMk` and the sibling
`TauCeti.indProjection_hom_hom_apply`. They are applied by explicit `rw` instead.

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

universe u v w x

variable {k : Type u} {G : Type v} {H : Type w} {K : Type x}

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
`a ↦ ⟦1 ⊗ₜ a⟧` of the induced representation. -/
lemma indResAdjunction_unit_app_hom_apply (φ : G →* H) (A : _root_.Rep.{max u v w x} k G) (a : A) :
    ((_root_.Rep.indResAdjunction.{max u v w x} k φ).unit.app A).hom a =
      Representation.IndV.mk φ A.ρ 1 a :=
  rfl

/-- The induction-in-stages isomorphism, backwards, on the generator `⟦1 ⊗ₜ a⟧`. This is the
adjunction identity `unit_conjugateEquiv` read on elements: both units are generator maps and
`resFunctorCompIso` is the identity on vectors, so the abstract characterisation
`conjugateEquiv_indFunctorCompIso_inv` becomes this single value. -/
lemma indFunctorCompIso_inv_app_hom_apply_mk_one (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (a : A) :
    ((indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) =
      Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a) := by
  have := unit_conjugateEquiv
    ((_root_.Rep.indResAdjunction.{max u v w x} k φ).comp
      (_root_.Rep.indResAdjunction.{max u v w x} k ψ))
    (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (indFunctorCompIso φ ψ).inv A
  rw [conjugateEquiv_indFunctorCompIso_inv] at this
  exact (congrArg (fun f => Rep.Hom.hom f a) this).symm

/-- Moving the inner group coordinate of a twice-induced representation out to the outer one:
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧ = ⟦ψ(h) κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Every element of `Ind_ψ (Ind_φ A)` is therefore a sum of
elements whose inner coordinate is `1`, which is what makes the two formulas below determine the
induction-in-stages isomorphism. -/
lemma indV_mk_ind_mk {V : Type max u v w x} [AddCommGroup V] [Module k V] (φ : G →* H) (ψ : H →* K)
    (ρ : Representation k G V) (h : H) (κ : K) (a : V) :
    Representation.IndV.mk ψ (Representation.ind φ ρ) κ (Representation.IndV.mk φ ρ h a) =
      Representation.IndV.mk ψ (Representation.ind φ ρ) (ψ h * κ)
        (Representation.IndV.mk φ ρ 1 a) := by
  have := Representation.Coinvariants.mk_inv_tmul ((_root_.Representation.leftRegular k K).comp ψ)
    (Representation.ind φ ρ) (MonoidAlgebra.single κ (1 : k))
    (Representation.IndV.mk φ ρ 1 a) h⁻¹
  simpa [Representation.ofMulAction_single, Representation.ind_mk] using this.symm

/-- Two linear maps out of a twice-induced representation agree as soon as they agree on the
elements `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` whose inner group coordinate is `1`. -/
lemma indV_ind_hom_ext {V W : Type max u v w x} [AddCommGroup V] [Module k V] [AddCommGroup W]
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

/-- **Induction in stages on representatives, backwards**: the inverse of the induction-in-stages
isomorphism sends `⟦κ ⊗ₜ a⟧` to `⟦κ ⊗ₜ ⟦1 ⊗ₜ a⟧⟧`. Not a `simp` lemma: `simp` unfolds the reducible
`Representation.IndV.mk`, so the left-hand side is not in `simp`-normal form. -/
lemma indFunctorCompIso_inv_app_hom_apply_mk (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (κ : K) (a : A) :
    ((indFunctorCompIso φ ψ).inv.app A).hom (Representation.IndV.mk (ψ.comp φ) A.ρ κ a) =
      Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ 1 a) := by
  have hsrc : Representation.IndV.mk (ψ.comp φ) A.ρ κ a =
      ((_root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ)).obj A).ρ κ⁻¹
        (Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) := by
    simp
  have hcomm := _root_.Rep.hom_comm_apply ((indFunctorCompIso φ ψ).inv.app A) κ⁻¹
    (Representation.IndV.mk (ψ.comp φ) A.ρ 1 a)
  rw [hsrc, hcomm, indFunctorCompIso_inv_app_hom_apply_mk_one]
  simp

/-- **Induction in stages on representatives**: the induction-in-stages isomorphism sends
`⟦κ ⊗ₜ ⟦h ⊗ₜ a⟧⟧` to `⟦ψ(h) κ ⊗ₜ a⟧`. This is the explicit formula the character and Mackey
computations consume, in place of the abstract adjoint comparison. Not a `simp` lemma, for the same
reason as `TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. -/
lemma indFunctorCompIso_hom_app_hom_apply_mk (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (h : H) (κ : K) (a : A) :
    ((indFunctorCompIso φ ψ).hom.app A).hom
        (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ κ (Representation.IndV.mk φ A.ρ h a)) =
      Representation.IndV.mk (ψ.comp φ) A.ρ (ψ h * κ) a := by
  have hinv := indFunctorCompIso_inv_app_hom_apply_mk φ ψ A (ψ h * κ) a
  rw [← indV_mk_ind_mk φ ψ A.ρ h κ a] at hinv
  rw [← hinv]
  exact congrArg (fun f => Rep.Hom.hom f _) ((indFunctorCompIso φ ψ).inv_hom_id_app A)

/-- **The induction-in-stages isomorphism is determined by one value.** A morphism of
`K`-representations `Ind_ψ (Ind_φ A) ⟶ Ind_{ψφ} A` sending `⟦1 ⊗ₜ ⟦1 ⊗ₜ a⟧⟧` to `⟦1 ⊗ₜ a⟧` is the
induction-in-stages isomorphism. This is how a comparison map built by hand is identified with the
adjoint one produced by `TauCeti.Rep.indFunctorCompIso`. -/
lemma eq_indFunctorCompIso_hom_app (φ : G →* H) (ψ : H →* K) (A : _root_.Rep.{max u v w x} k G)
    {f : (_root_.Rep.indFunctor.{max u v w x} k φ ⋙
        _root_.Rep.indFunctor.{max u v w x} k ψ).obj A ⟶
      (_root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ)).obj A}
    (hf : ∀ a : A, f.hom (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
        (Representation.IndV.mk φ A.ρ 1 a)) = Representation.IndV.mk (ψ.comp φ) A.ρ 1 a) :
    f = (indFunctorCompIso φ ψ).hom.app A := by
  refine _root_.Rep.hom_ext (Representation.IntertwiningMap.ext
    (indV_ind_hom_ext φ ψ A.ρ fun κ a => ?_))
  have hsrc : Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ κ
        (Representation.IndV.mk φ A.ρ 1 a) =
      ((_root_.Rep.indFunctor.{max u v w x} k φ ⋙
          _root_.Rep.indFunctor.{max u v w x} k ψ).obj A).ρ κ⁻¹
        (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1
          (Representation.IndV.mk φ A.ρ 1 a)) := by
    simp
  have hcomm := _root_.Rep.hom_comm_apply f κ⁻¹
    (Representation.IndV.mk ψ (_root_.Rep.ind φ A).ρ 1 (Representation.IndV.mk φ A.ρ 1 a))
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply,
    indFunctorCompIso_hom_app_hom_apply_mk φ ψ A 1 κ a, map_one, one_mul, hsrc, hcomm, hf]
  simp

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

/-- The counit of Mathlib's restriction--coinduction adjunction is evaluation at `1`. -/
lemma resCoindAdjunction_counit_app_hom_apply (φ : G →* H) (A : _root_.Rep.{max u v w x} k G)
    (f : _root_.Rep.coind φ A) :
    ((_root_.Rep.resCoindAdjunction.{max u v w x} k φ).counit.app A).hom f = f.1 1 :=
  rfl

/-- The coinduction-in-stages isomorphism evaluated at `1`: it reads off the value of a doubly
coinduced function at the pair `(1, 1)`. This is the adjunction identity
`conjugateEquiv_counit_symm` read on elements, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk_one`. -/
lemma coindFunctorCompIso_hom_app_hom_apply_apply_one (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (F : _root_.Rep.coind ψ (_root_.Rep.coind φ A)) :
    (((coindFunctorCompIso φ ψ).hom.app A).hom F).1 1 = (F.1 1).1 1 := by
  have := conjugateEquiv_counit_symm
    ((_root_.Rep.resCoindAdjunction.{max u v w x} k ψ).comp
      (_root_.Rep.resCoindAdjunction.{max u v w x} k φ))
    (_root_.Rep.resCoindAdjunction.{max u v w x} k (ψ.comp φ))
    (coindFunctorCompIso φ ψ).hom A
  rw [conjugateEquiv_symm_coindFunctorCompIso_hom] at this
  exact congrArg (fun f : (_root_.Rep.resFunctor.{max u v w x} (k := k) (ψ.comp φ)).obj
    ((_root_.Rep.coindFunctor.{max u v w x} k φ ⋙
      _root_.Rep.coindFunctor.{max u v w x} k ψ).obj A) ⟶ A => Rep.Hom.hom f F) this

/-- **Coinduction in stages on functions**: the coinduction-in-stages isomorphism sends a
`G`-equivariant function `F : K → (H → A)` to `κ ↦ F κ 1`. This is the dual of
`TauCeti.Rep.indFunctorCompIso_hom_app_hom_apply_mk`, and is obtained from its value at `1` by
`K`-equivariance. -/
lemma coindFunctorCompIso_hom_app_hom_apply_apply (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (F : _root_.Rep.coind ψ (_root_.Rep.coind φ A)) (κ : K) :
    (((coindFunctorCompIso φ ψ).hom.app A).hom F).1 κ = (F.1 κ).1 1 := by
  have hcomm := _root_.Rep.hom_comm_apply ((coindFunctorCompIso φ ψ).hom.app A) κ F
  have h1 := coindFunctorCompIso_hom_app_hom_apply_apply_one φ ψ A
    (((_root_.Rep.coindFunctor.{max u v w x} k φ ⋙
      _root_.Rep.coindFunctor.{max u v w x} k ψ).obj A).ρ κ F)
  rw [hcomm] at h1
  have h2 : (((coindFunctorCompIso φ ψ).hom.app A).hom F).1 (1 * κ) = (F.1 (1 * κ)).1 1 := h1
  simpa using h2

/-- **Coinduction in stages on functions, backwards**: the inverse of the coinduction-in-stages
isomorphism turns a `G`-equivariant function `f : K → A` into `κ ↦ (h ↦ f (ψ(h) κ))`, the dual of
`TauCeti.Rep.indFunctorCompIso_inv_app_hom_apply_mk`. -/
lemma coindFunctorCompIso_inv_app_hom_apply_apply (φ : G →* H) (ψ : H →* K)
    (A : _root_.Rep.{max u v w x} k G) (f : _root_.Rep.coind (ψ.comp φ) A) (κ : K) (h : H) :
    ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 h = f.1 (ψ h * κ) := by
  have hfF : ((coindFunctorCompIso φ ψ).hom.app A).hom
      (((coindFunctorCompIso φ ψ).inv.app A).hom f) = f :=
    congrArg (fun m => Rep.Hom.hom m f) ((coindFunctorCompIso φ ψ).inv_hom_id_app A)
  have hhom : ∀ κ' : K, ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ').1 1 = f.1 κ' :=
    fun κ' => (coindFunctorCompIso_hom_app_hom_apply_apply φ ψ A _ κ').symm.trans
      (congrArg (fun y : _root_.Rep.coind (ψ.comp φ) A => y.1 κ') hfF)
  have hmem := (((coindFunctorCompIso φ ψ).inv.app A).hom f).2 h κ
  have hx : f.1 (ψ h * κ) = ((((coindFunctorCompIso φ ψ).inv.app A).hom f).1 κ).1 (1 * h) := by
    rw [← hhom (ψ h * κ)]
    exact congrArg (fun y => y.1 1) hmem
  rw [hx, one_mul]

end Coinduction

end Rep

end TauCeti
