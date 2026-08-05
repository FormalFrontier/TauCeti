/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Induction.Permutation

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

The inverse `h⁻¹` is forced, not a convention. In Mathlib's model, `g : G` identifies
`h ⊗ₜ (a ⊗ₜ b)` with `φ(g)h ⊗ₜ (ρ_A(g) a ⊗ₜ ρ_B(φ g) b)`, so a twist `ρ_B(f h)` descends to the
coinvariants exactly when `f (φ(g) h) · φ(g) = f h` for all `g` and `h`, and `f h = h⁻¹` is the
solution. The same inverse makes the map `H`-equivariant, because `H` acts on `Ind_φ A` by
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
* `TauCeti.indResProjection`: for a subgroup `S ≤ G`, the classical corollary
  `Ind_S^G (Res_S^G Y) ≅ k[G ⧸ S] ⊗ Y`, obtained by feeding the trivial representation into the
  projection formula and identifying `Ind_S^G (trivial)` with the permutation representation
  through `TauCeti.indTrivialIso`.

## Main statements

* `TauCeti.indVMk_self_apply`: the generators of `Representation.IndV` satisfy
  `⟦φ(g) h ⊗ₜ ρ(g) a⟧ = ⟦h ⊗ₜ a⟧`. This single relation is what makes both directions of the
  projection formula descend to the coinvariants.
* `TauCeti.indProjection_hom_hom_apply`, `TauCeti.indProjection_inv_hom_apply`: the two directions
  on generators.
* `TauCeti.indProjection_hom_naturality_left`, `TauCeti.indProjection_hom_naturality_right`:
  naturality in each variable.
* `TauCeti.coinvariantsTensorIndHom_map_indProjection_mk`: the comparison with Mathlib's
  coinvariants shadow. Taking `H`-coinvariants of `indProjection` and following with Mathlib's
  `Rep.coinvariantsTensorIndHom` gives the map `⟦⟦h ⊗ₜ z⟧⟧ ↦ ⟦z⟧`, which no longer mentions `h`;
  so the two isomorphisms agree, and the coinvariants of an induced representation are the
  coinvariants downstairs.

## Implementation notes

`Representation.IndV.mk φ ρ h` is a reducible abbreviation for
`Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (MonoidAlgebra.single h 1)`, which `simp` unfolds.
The generator lemmas below are therefore stated with `IndV.mk`, the readable form, but are not
`simp` lemmas: their left-hand sides are not in `simp`-normal form and they never fire. This
matches Mathlib's own `Rep.coinvariantsTensorIndHom_mk_tmul_indVMk` and the sibling
`TauCeti.indTrivialEquiv_apply_mk`. Where a proof needs them after `simp` has normalized a goal,
it finishes with an explicit `Eq.trans`; the two naturality proofs instead unfold the definitions,
exactly as Mathlib does in `Rep.coinvariantsTensorIndIso`.

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

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H)
  {A B : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  (ρ : Representation k G A) (τ : Representation k H B)

/-- The defining relation of `Representation.IndV`: translating the group coordinate by `φ g` and
acting by `g` leaves a generator unchanged. This is `Representation.Coinvariants.mk_self_apply`
read on generators, and it is the only fact about the induced module that the projection formula
needs. -/
theorem indVMk_self_apply (g : G) (h : H) (a : A) :
    IndV.mk φ ρ (φ g * h) (ρ g a) = IndV.mk φ ρ h a := by
  simpa using Coinvariants.mk_self_apply (tprod ((leftRegular k H).comp φ) ρ) g
    (MonoidAlgebra.single h 1 ⊗ₜ[k] a)

/-- The forward map of the projection formula, `⟦h ⊗ₜ (a ⊗ₜ b)⟧ ↦ ⟦h ⊗ₜ a⟧ ⊗ₜ τ(h⁻¹) b`. The
twist by `τ h⁻¹` is what makes the expression independent of the representative: see
`TauCeti.indVMk_self_apply`. -/
noncomputable def indProjectionHom :
    IndV φ (ρ.tprod (τ.comp φ)) →ₗ[k] IndV φ ρ ⊗[k] B :=
  Coinvariants.lift _ (TensorProduct.lift <|
    (Finsupp.lift _ k H fun h => TensorProduct.map (IndV.mk φ ρ h) (τ h⁻¹)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by
    ext h a b
    simpa using congrArg (· ⊗ₜ[k] τ h⁻¹ b) (indVMk_self_apply φ ρ g h a)

theorem indProjectionHom_mk (h : H) (a : A) (b : B) :
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
    simpa using indVMk_self_apply φ (ρ.tprod (τ.comp φ)) g h (a ⊗ₜ[k] τ h b)

theorem indProjectionInv_mk (h : H) (a : A) (b : B) :
    indProjectionInv φ ρ τ (IndV.mk φ ρ h a ⊗ₜ[k] b)
      = IndV.mk φ (ρ.tprod (τ.comp φ)) h (a ⊗ₜ[k] τ h b) := by
  simp [indProjectionInv]

/-- The projection formula as a `k`-linear equivalence of the underlying modules: the two maps
above are mutually inverse because `τ h` and `τ h⁻¹` cancel. -/
noncomputable def indProjectionLEquiv :
    IndV φ (ρ.tprod (τ.comp φ)) ≃ₗ[k] IndV φ ρ ⊗[k] B :=
  LinearEquiv.ofLinear (indProjectionHom φ ρ τ) (indProjectionInv φ ρ τ)
    (by ext h a b; simp [indProjectionHom, indProjectionInv])
    (by ext h a b; simp [indProjectionHom, indProjectionInv])

/-- The projection formula as an equivalence of representations. Equivariance is the computation
`(h h₁⁻¹)⁻¹ = h₁ h⁻¹`: translating the group coordinate on the induced side by `h₁⁻¹` on the right
is matched by acting with `h₁` on the second tensor factor. -/
noncomputable def indProjectionEquiv :
    (Representation.ind φ (ρ.tprod (τ.comp φ))).Equiv ((Representation.ind φ ρ).tprod τ) :=
  Representation.Equiv.mk (indProjectionLEquiv φ ρ τ) fun h₁ => by
    ext h a b
    simp [indProjectionLEquiv, indProjectionHom, mul_inv_rev]

section Rep

variable (X : Rep k G) (Y : Rep k H)

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
  indProjectionHom_mk φ X.ρ Y.ρ h x y

/-- The backward direction of `TauCeti.indProjection` on generators. -/
theorem indProjection_inv_hom_apply (h : H) (x : X) (y : Y) :
    (indProjection φ X Y).inv.hom (IndV.mk φ X.ρ h x ⊗ₜ[k] y)
      = IndV.mk φ (X ⊗ Rep.res φ Y).ρ h (x ⊗ₜ[k] Y.ρ h y) :=
  indProjectionInv_mk φ X.ρ Y.ρ h x y

/-- The projection formula is natural in the left tensor factor, the `Rep k G` argument. -/
theorem indProjection_hom_naturality_left {X X' : Rep k G} (f : X ⟶ X') (Y : Rep k H) :
    Rep.indMap φ (f ⊗ₘ 𝟙 (Rep.res φ Y)) ≫ (indProjection φ X' Y).hom
      = (indProjection φ X Y).hom ≫ (Rep.indMap φ f ⊗ₘ 𝟙 Y) := by
  ext h x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Rep.indMap, indProjection, indProjectionEquiv, indProjectionLEquiv,
      indProjectionHom]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The projection formula is natural in the right tensor factor, the `Rep k H` argument. -/
theorem indProjection_hom_naturality_right (X : Rep k G) {Y Y' : Rep k H} (g : Y ⟶ Y') :
    Rep.indMap φ (𝟙 X ⊗ₘ (Rep.resFunctor φ).map g) ≫ (indProjection φ X Y').hom
      = (indProjection φ X Y).hom ≫ (𝟙 (Rep.ind φ X) ⊗ₘ g) := by
  ext h x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Rep.indMap, indProjection, indProjectionEquiv, indProjectionLEquiv,
      indProjectionHom, ← Rep.hom_comm_apply]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The projection formula as a natural isomorphism in the left tensor factor: the functors
`X ↦ Ind_φ (X ⊗ Res_φ Y)` and `X ↦ (Ind_φ X) ⊗ Y` from `Rep k G` to `Rep k H` agree. -/
noncomputable def indProjectionNatIsoLeft (Y : Rep k H) :
    (curriedTensor (Rep k G)).flip.obj (Rep.res φ Y) ⋙ Rep.indFunctor k φ
      ≅ Rep.indFunctor k φ ⋙ (curriedTensor (Rep k H)).flip.obj Y :=
  NatIso.ofComponents (fun X => indProjection φ X Y) fun {_ _} f => by
    simpa using indProjection_hom_naturality_left φ f Y

/-- The projection formula as a natural isomorphism in the right tensor factor: the endofunctors
`Y ↦ Ind_φ (X ⊗ Res_φ Y)` and `Y ↦ (Ind_φ X) ⊗ Y` of `Rep k H` agree. This is the shape of
Mathlib's coinvariants version `Rep.coinvariantsTensorIndNatIso`. -/
noncomputable def indProjectionNatIsoRight (X : Rep k G) :
    Rep.resFunctor φ ⋙ (curriedTensor (Rep k G)).obj X ⋙ Rep.indFunctor k φ
      ≅ (curriedTensor (Rep k H)).obj (Rep.ind φ X) :=
  NatIso.ofComponents (indProjection φ X) fun {_ _} g => by
    simpa using indProjection_hom_naturality_right φ X g

/-- **The comparison with Mathlib's coinvariants shadow.** Applying `H`-coinvariants to
`TauCeti.indProjection` and composing with `Rep.coinvariantsTensorIndHom` sends the class of a
generator `⟦h ⊗ₜ z⟧` to `⟦z⟧`, with no trace of `h` left: the two twists `Y.ρ h⁻¹` and `Y.ρ h`
cancel. So `Rep.coinvariantsTensorIndNatIso` is indeed the image of the projection formula under
coinvariants, and coinvariants of an induced representation are computed downstairs. -/
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
  simp [indProjection, indProjectionEquiv, indProjectionLEquiv, indProjectionHom]

end Rep

section Subgroup

variable {S : Subgroup G} (Y : Rep k G)

/-- **Induction of a restriction.** For a subgroup `S ≤ G`, restricting a `G`-representation to `S`
and inducing back up tensors it with the permutation representation on the cosets,
`Ind_S^G (Res_S^G Y) ≅ k[G ⧸ S] ⊗ Y`. This is the projection formula applied to the trivial
`S`-representation, followed by `TauCeti.indTrivialIso`. -/
noncomputable def indResProjection :
    Rep.ind S.subtype (Rep.res S.subtype Y) ≅ Rep.ofMulAction k G (G ⧸ S) ⊗ Y :=
  (Rep.indFunctor k S.subtype).mapIso (λ_ (Rep.res S.subtype Y)).symm ≪≫
    indProjection S.subtype (𝟙_ (Rep k S)) Y ≪≫
    (indTrivialIso k S ⊗ᵢ Iso.refl Y)

/-- `TauCeti.indResProjection` on generators: the coset orientation is the one inherited from
`TauCeti.indTrivialIso`, which sends `⟦x ⊗ₜ a⟧` to `single ⟦x⁻¹⟧ a`. -/
theorem indResProjection_hom_hom_apply (x : G) (y : Y) :
    (indResProjection Y).hom.hom (IndV.mk S.subtype (Rep.res S.subtype Y).ρ x y)
      = MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ S) (1 : k) ⊗ₜ[k] Y.ρ x⁻¹ y := by
  refine Eq.trans ?_ (congrArg (· ⊗ₜ[k] Y.ρ x⁻¹ y) (indTrivialIso_hom_hom_apply k S x 1))
  simp [indResProjection, indProjection, indProjectionEquiv, indProjectionLEquiv,
    indProjectionHom, Rep.indMap]

end Subgroup

end TauCeti
