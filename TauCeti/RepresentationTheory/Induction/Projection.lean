/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced

/-!
# The projection formula for induced representations

For a group homomorphism `φ : G →* H`, a `G`-representation `A` and an `H`-representation `B`, the
*projection formula* (or *tensor identity*) is the isomorphism of `H`-representations

`Ind_φ (A ⊗ Res_φ B) ≅ (Ind_φ A) ⊗ B`.

It says that induction is a morphism of modules over the representation ring of `H`: an induced
representation may be tensored with an `H`-representation either before or after inducing.

Mathlib has only the shadow of this statement obtained by taking `H`-coinvariants of both sides,
`Rep.coinvariantsTensorIndNatIso`, which it uses for Shapiro's lemma. The isomorphism of
representations itself is not a formal consequence of the induction--restriction adjunction:
`Representation.ind` is built as the coinvariants of `k[H] ⊗[k] A`, so the map has to be produced
by hand on representatives and then shown to descend and to be equivariant. That is what this file
does, over an arbitrary commutative ring, at the generality of a group homomorphism rather than a
subgroup inclusion.

The two directions are

`⟦h ⊗ₜ (a ⊗ₜ b)⟧ ↦ ⟦h ⊗ₜ a⟧ ⊗ₜ ρ_B(h⁻¹) b`,  `⟦h ⊗ₜ a⟧ ⊗ₜ b ↦ ⟦h ⊗ₜ (a ⊗ₜ ρ_B(h) b)⟧`.

The inverse `h⁻¹` is not decorative. In Mathlib's model, `g : G` identifies `h ⊗ₜ (a ⊗ₜ b)` with
`φ(g)h ⊗ₜ (ρ_A(g) a ⊗ₜ ρ_B(φ g) b)`, so a twist `ρ_B(f h)` by a function `f : H → H` descends to
the coinvariants as soon as `f (φ(g) h) · φ(g) = f h` for all `g` and `h` — a condition on `f`
alone, which does not mention `B`. The canonical solution is `f h = h⁻¹`, and it is also the one
that makes the map `H`-equivariant, because `H` acts on `Ind_φ A` by
`h₁ • ⟦h ⊗ₜ a⟧ = ⟦h h₁⁻¹ ⊗ₜ a⟧`.

## Main definitions

* `TauCeti.indProjection`: **the projection formula**,
  `Rep.ind φ (X ⊗ Rep.res φ Y) ≅ Rep.ind φ X ⊗ Y` in `Rep k H`.
* `TauCeti.indProjectionEquiv`, `TauCeti.indProjectionLEquiv`: the same isomorphism as an
  equivalence of `Representation`s and as a `k`-linear equivalence of the underlying modules, built
  from the two explicit maps `TauCeti.indProjectionHom` and `TauCeti.indProjectionInv`.
* `TauCeti.indProjectionNatIsoLeft`, `TauCeti.indProjectionNatIsoRight`: the projection formula as
  a natural isomorphism of functors, in the left tensor factor (the `Rep k G` argument) and in the
  right one (the `Rep k H` argument) respectively.

The classical corollary for a subgroup `S ≤ G`, `Ind_S^G (Res_S^G Y) ≅ k[G ⧸ S] ⊗ Y`, needs the
identification of `Ind_S^G (trivial)` with the permutation representation and therefore lives
downstream, as `TauCeti.indResProjection` in
`TauCeti/RepresentationTheory/Induction/Permutation.lean`.

## Main statements

* `TauCeti.indProjectionHom_apply_mk`, `TauCeti.indProjectionInv_apply_mk`: the two `k`-linear maps
  on generators. Every proof below about the projection formula goes through these two rules rather
  than through the definitions.
* `TauCeti.indProjection_hom_hom_apply`, `TauCeti.indProjection_inv_hom_apply`: the two directions
  of the `Rep k H` isomorphism on generators.
* `TauCeti.indProjection_hom_naturality_left`, `TauCeti.indProjection_hom_naturality_right`:
  naturality in each variable.
* `TauCeti.coinvariantsTensorIndHom_map_indProjection_mk`: the comparison with Mathlib's
  coinvariants shadow. Taking `H`-coinvariants of `indProjection` and following with Mathlib's
  `Rep.coinvariantsTensorIndHom` sends `⟦⟦h ⊗ₜ z⟧⟧` to `⟦z⟧`, with no trace of `h` left.

## Implementation notes

`Representation.IndV.mk φ ρ h` is a reducible abbreviation for
`Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (MonoidAlgebra.single h 1)`, which `simp` unfolds.
The generator lemmas below are therefore stated with `IndV.mk`, the readable form, but are not
`simp` lemmas: their left-hand sides are not in `simp`-normal form and they never fire. This
matches Mathlib's own `Rep.coinvariantsTensorIndHom_mk_tmul_indVMk` and the sibling
`TauCeti.indTrivialEquiv_apply_mk`. They are applied by explicit `rw`/`Eq.trans` instead, so that
only the two definitions `TauCeti.indProjectionHom` and `TauCeti.indProjectionInv` are ever
unfolded, and only in their own generator lemmas. For the same reason the proofs below reach the
generators by an explicit `Representation.IndV.hom_ext`/`TensorProduct.ext'` chain and peel the
resulting compositions one at a time with `LinearMap.comp_apply` under `conv_lhs`/`conv_rhs`: an
unrestricted `ext`/`simp` step also unfolds `IndV.mk`, after which the generator lemmas no longer
match.

The `Representation`-level constructions are universe-polymorphic in `k`, `G`, `H` and the two
carrier modules. The `Rep k H` layer is not, and cannot be: `Rep.{w} k G` is monoidal only for
`w` the universe of `k` (`ModuleCat.monoidalCategory` is stated for `ModuleCat.{u} R` with
`R : Type u`), while `Rep.ind φ` lands in `Rep.{max u v' w} k H` for `H : Type v'`. Tensoring
`Rep.ind φ X` with `Y` therefore forces `H` into the universe of `k`, exactly as in Mathlib's own
`Rep.coinvariantsTensorIndHom` section; only the source group `G` stays free.

## References

This is the projection formula of Layer 0 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, whose `Suggested.lean`
records it as `indProjection`. See J.-P. Serre, *Linear Representations of Finite Groups*, §3.3,
and C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §10.
-/

public section

open CategoryTheory MonoidalCategory Representation TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u v v' w w'

section Linear

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  {A : Type w} {B : Type w'} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  (ρ : Representation k G A) (τ : Representation k H B)

/-- The forward map of the projection formula, `⟦h ⊗ₜ (a ⊗ₜ b)⟧ ↦ ⟦h ⊗ₜ a⟧ ⊗ₜ τ(h⁻¹) b`. The
twist by `τ h⁻¹` is what makes the expression independent of the representative: it undoes the
translation of the group coordinate recorded by `Representation.Coinvariants.mk_self_apply`. -/
noncomputable def indProjectionHom :
    IndV φ (ρ.tprod (τ.comp φ)) →ₗ[k] IndV φ ρ ⊗[k] B :=
  Coinvariants.lift _ (TensorProduct.lift <|
    (Finsupp.lift _ k H fun h => TensorProduct.map (IndV.mk φ ρ h) (τ h⁻¹)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by
    ext h a b
    simpa using congrArg (· ⊗ₜ[k] τ h⁻¹ b)
      (Coinvariants.mk_self_apply (tprod ((leftRegular k H).comp φ) ρ) g
        (MonoidAlgebra.single h 1 ⊗ₜ[k] a))

/-- `TauCeti.indProjectionHom` on generators. This is the only place the definition is unfolded;
every later proof rewrites with this rule instead. -/
theorem indProjectionHom_apply_mk (h : H) (a : A) (b : B) :
    indProjectionHom φ ρ τ (IndV.mk φ (ρ.tprod (τ.comp φ)) h (a ⊗ₜ[k] b))
      = IndV.mk φ ρ h a ⊗ₜ[k] τ h⁻¹ b := by
  simp [indProjectionHom]

/-- The backward map of the projection formula, `⟦h ⊗ₜ a⟧ ⊗ₜ b ↦ ⟦h ⊗ₜ (a ⊗ₜ τ(h) b)⟧`. -/
noncomputable def indProjectionInv :
    IndV φ ρ ⊗[k] B →ₗ[k] IndV φ (ρ.tprod (τ.comp φ)) :=
  TensorProduct.lift <| Coinvariants.lift _ (TensorProduct.lift <|
    (Finsupp.lift _ k H fun h =>
      ((TensorProduct.mk k A B).compr₂ (IndV.mk φ (ρ.tprod (τ.comp φ)) h)).compl₂ (τ h)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by
    ext h a b
    simpa using Coinvariants.mk_self_apply (tprod ((leftRegular k H).comp φ) (ρ.tprod (τ.comp φ)))
      g (MonoidAlgebra.single h 1 ⊗ₜ[k] (a ⊗ₜ[k] τ h b))

/-- `TauCeti.indProjectionInv` on generators. This is the only place the definition is unfolded;
every later proof rewrites with this rule instead. -/
theorem indProjectionInv_apply_mk (h : H) (a : A) (b : B) :
    indProjectionInv φ ρ τ (IndV.mk φ ρ h a ⊗ₜ[k] b)
      = IndV.mk φ (ρ.tprod (τ.comp φ)) h (a ⊗ₜ[k] τ h b) := by
  simp [indProjectionInv]

/-- The projection formula as a `k`-linear equivalence of the underlying modules: the two maps
above are mutually inverse because `τ h` and `τ h⁻¹` cancel. -/
noncomputable def indProjectionLEquiv :
    IndV φ (ρ.tprod (τ.comp φ)) ≃ₗ[k] IndV φ ρ ⊗[k] B :=
  LinearEquiv.ofLinearMap (indProjectionHom φ ρ τ) (indProjectionInv φ ρ τ)
    (by
      ext h a b
      exact (congrArg (indProjectionHom φ ρ τ) (indProjectionInv_apply_mk φ ρ τ h a b)).trans <|
        (indProjectionHom_apply_mk φ ρ τ h a (τ h b)).trans <| by simp)
    (by
      ext h a b
      exact (congrArg (indProjectionInv φ ρ τ) (indProjectionHom_apply_mk φ ρ τ h a b)).trans <|
        (indProjectionInv_apply_mk φ ρ τ h a (τ h⁻¹ b)).trans <| by simp)

/-- `TauCeti.indProjectionLEquiv` is `TauCeti.indProjectionHom` in the forward direction. -/
@[simp]
theorem indProjectionLEquiv_apply (x : IndV φ (ρ.tprod (τ.comp φ))) :
    indProjectionLEquiv φ ρ τ x = indProjectionHom φ ρ τ x := by
  simp [indProjectionLEquiv]

/-- The projection formula as an equivalence of representations. Equivariance is the computation
`(h h₁⁻¹)⁻¹ = h₁ h⁻¹`: translating the group coordinate on the induced side by `h₁⁻¹` on the right
is matched by acting with `h₁` on the second tensor factor. -/
noncomputable def indProjectionEquiv :
    (Representation.ind φ (ρ.tprod (τ.comp φ))).Equiv ((Representation.ind φ ρ).tprod τ) :=
  Representation.Equiv.mk (indProjectionLEquiv φ ρ τ) fun h₁ =>
    IndV.hom_ext φ _ fun h => TensorProduct.ext' fun a b => by
      conv_lhs => rw [LinearMap.comp_apply, LinearMap.comp_apply]
      conv_rhs => rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [LinearEquiv.coe_coe, indProjectionLEquiv_apply, indProjectionLEquiv_apply,
        Representation.tprod_apply, Representation.ind_mk, indProjectionHom_apply_mk,
        indProjectionHom_apply_mk, TensorProduct.map_tmul, Representation.ind_mk, mul_inv_rev,
        inv_inv, map_mul, Module.End.mul_apply]

end Linear

section Rep

variable {k : Type u} {G : Type v} {H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (X : Rep.{u} k G) (Y : Rep.{u} k H)

/-- **The projection formula** in `Rep k H`: inducing a representation tensored with a restricted
one is the induced representation tensored with the original,
`Ind_φ (X ⊗ Res_φ Y) ≅ (Ind_φ X) ⊗ Y`. -/
noncomputable def indProjection : Rep.ind φ (X ⊗ Rep.res φ Y) ≅ Rep.ind φ X ⊗ Y :=
  Rep.mkIso (indProjectionEquiv φ X.ρ Y.ρ)

/-- The forward direction of `TauCeti.indProjection` on generators. Not a `simp` lemma: `simp`
unfolds the reducible `Representation.IndV.mk`, so the left-hand side is not in `simp`-normal
form. -/
theorem indProjection_hom_hom_apply (h : H) (x : X) (y : Y) :
    (indProjection φ X Y).hom.hom (IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] y))
      = IndV.mk φ X.ρ h x ⊗ₜ[k] Y.ρ h⁻¹ y :=
  indProjectionHom_apply_mk φ X.ρ Y.ρ h x y

/-- The backward direction of `TauCeti.indProjection` on generators. -/
theorem indProjection_inv_hom_apply (h : H) (x : X) (y : Y) :
    (indProjection φ X Y).inv.hom (IndV.mk φ X.ρ h x ⊗ₜ[k] y)
      = IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] Y.ρ h y) :=
  indProjectionInv_apply_mk φ X.ρ Y.ρ h x y

/-- The projection formula is natural in the left tensor factor, the `Rep k G` argument. -/
theorem indProjection_hom_naturality_left {X X' : Rep.{u} k G} (f : X ⟶ X') (Y : Rep.{u} k H) :
    Rep.indMap φ (f ⊗ₘ 𝟙 (Rep.res φ Y)) ≫ (indProjection φ X' Y).hom
      = (indProjection φ X Y).hom ≫ (Rep.indMap φ f ⊗ₘ 𝟙 Y) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (IndV.hom_ext φ _ fun h =>
    TensorProduct.ext' fun x y => ?_))
  have hmap : (Rep.indMap φ (f ⊗ₘ 𝟙 (Rep.res φ Y))).hom
      (IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] y))
        = IndV.mk φ (X' ⊗ Rep.res φ Y).ρ h (f.hom x ⊗ₜ[k] y) := by
    simp [Rep.indMap]
  conv_lhs => rw [LinearMap.comp_apply]
  conv_rhs => rw [LinearMap.comp_apply]
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply, Rep.hom_comp, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.comp_apply,
    hmap, indProjection_hom_hom_apply, indProjection_hom_hom_apply]
  simp [Rep.indMap]

/-- The projection formula is natural in the right tensor factor, the `Rep k H` argument. -/
theorem indProjection_hom_naturality_right (X : Rep.{u} k G) {Y Y' : Rep.{u} k H} (g : Y ⟶ Y') :
    Rep.indMap φ (𝟙 X ⊗ₘ (Rep.resFunctor φ).map g) ≫ (indProjection φ X Y').hom
      = (indProjection φ X Y).hom ≫ (𝟙 (Rep.ind φ X) ⊗ₘ g) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (IndV.hom_ext φ _ fun h =>
    TensorProduct.ext' fun x y => ?_))
  have hmap : (Rep.indMap φ (𝟙 X ⊗ₘ (Rep.resFunctor φ).map g)).hom
      (IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] y))
        = IndV.mk φ (X ⊗ Rep.res φ Y').ρ h (x ⊗ₜ[k] g.hom y) := by
    simp [Rep.indMap]
  conv_lhs => rw [LinearMap.comp_apply]
  conv_rhs => rw [LinearMap.comp_apply]
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply, Rep.hom_comp, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.comp_apply,
    hmap, indProjection_hom_hom_apply, indProjection_hom_hom_apply]
  simp [← Rep.hom_comm_apply]

/-- The projection formula as a natural isomorphism in the left tensor factor: the functors
`X ↦ Ind_φ (X ⊗ Res_φ Y)` and `X ↦ (Ind_φ X) ⊗ Y` from `Rep k G` to `Rep k H` agree. -/
noncomputable def indProjectionNatIsoLeft (Y : Rep.{u} k H) :
    (curriedTensor (Rep.{u} k G)).flip.obj (Rep.res φ Y) ⋙ Rep.indFunctor k φ
      ≅ Rep.indFunctor k φ ⋙ (curriedTensor (Rep.{u} k H)).flip.obj Y :=
  NatIso.ofComponents (fun X => indProjection φ X Y) fun {_ _} f => by
    simpa using indProjection_hom_naturality_left φ f Y

/-- The projection formula as a natural isomorphism in the right tensor factor: the endofunctors
`Y ↦ Ind_φ (X ⊗ Res_φ Y)` and `Y ↦ (Ind_φ X) ⊗ Y` of `Rep k H` agree. This is the shape of
Mathlib's coinvariants version `Rep.coinvariantsTensorIndNatIso`. -/
noncomputable def indProjectionNatIsoRight (X : Rep.{u} k G) :
    Rep.resFunctor φ ⋙ (curriedTensor (Rep.{u} k G)).obj X ⋙ Rep.indFunctor k φ
      ≅ (curriedTensor (Rep.{u} k H)).obj (Rep.ind φ X) :=
  NatIso.ofComponents (indProjection φ X) fun {_ _} g => by
    simpa using indProjection_hom_naturality_right φ X g

end Rep

section Comparison

variable {k : Type u} {G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H)

/-- **The comparison with Mathlib's coinvariants shadow.** Applying `H`-coinvariants to
`TauCeti.indProjection` and composing with `Rep.coinvariantsTensorIndHom` sends the class of a
generator `⟦h ⊗ₜ z⟧` to `⟦z⟧`, with no trace of `h` left: the twist `Y.ρ h⁻¹` introduced by the
projection formula is absorbed by the coinvariants relation.

This computes that one composite on generators; it is not an equality of the two isomorphisms,
which do not have the same source and target: `Rep.coinvariantsTensorIndHom` runs from the
coinvariants of `(Ind_φ X) ⊗ Y` to the coinvariants of `X ⊗ Res_φ Y` downstairs, while
`TauCeti.indProjection` is an isomorphism in `Rep k H` upstairs. -/
theorem coinvariantsTensorIndHom_map_indProjection_mk (X : Rep k G) (Y : Rep k H)
    (h : H) (x : X) (y : Y) :
    (Rep.coinvariantsTensorIndHom φ X Y).hom
        (((Rep.coinvariantsFunctor k H).map (indProjection φ X Y).hom).hom
          (Coinvariants.mk _ (IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] y))))
      = Coinvariants.mk (X.ρ.tprod ((Rep.res φ Y).ρ)) (x ⊗ₜ[k] y) := by
  have key : (Rep.coinvariantsTensorIndHom φ X Y).hom
      (Rep.coinvariantsTensorMk (Rep.ind φ X) Y (IndV.mk φ X.ρ 1 x) y)
        = Coinvariants.mk (X.ρ.tprod ((Rep.res φ Y).ρ)) (x ⊗ₜ[k] y) := by
    simpa using Rep.coinvariantsTensorIndHom_mk_tmul_indVMk φ (1 : H) x y
  refine Eq.trans ?_ key
  refine congrArg (Rep.coinvariantsTensorIndHom φ X Y).hom ?_
  refine Eq.trans (congrArg (Coinvariants.mk _) (indProjection_hom_hom_apply φ X Y h x y)) ?_
  simp [Rep.coinvariantsTensorMk]

end Comparison

end TauCeti
