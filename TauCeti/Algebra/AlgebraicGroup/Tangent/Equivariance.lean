/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Equivariance of the differential for the adjoint action

A morphism of affine group schemes intertwines conjugation. Differentiating at the identity says
that its differential intertwines the corresponding adjoint actions. In coordinate rings, a
bialgebra morphism `φ : A' →ₐc[R] A` acts on both points and tangent derivations by precomposition,
and the compatibility is

```text
dφ (Ad(g)(d)) = Ad(g ∘ φ)(dφ(d)).
```

This file proves that identity directly from functoriality of convolution and packages it as an
intertwining identity for the adjoint representations. It synchronizes the differential and
adjoint-action parts of Layer 2 of the ReductiveGroups roadmap; in particular, it is the
functoriality needed when tangent Lie algebras of closed subgroups are used inside an ambient
group.

## Main declarations

* `TauCeti.derivationComp_adDerivation`: the differential intertwines the adjoint action.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.
-/

public section

namespace TauCeti

open _root_.Coalgebra WithConv

universe u v w x

variable {R : Type u} {A : Type v} {A' : Type w} {B : Type x}
variable [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
variable [CommSemiring A'] [HopfAlgebra R A']
variable [CommSemiring B] [Algebra R B]

private lemma algEquivSelf_derivationComp_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A') :
    Bialgebra.CounitAlgebra.algEquivSelf R A' B
        (derivationComp (B := B) φ d a) =
      Bialgebra.CounitAlgebra.algEquivSelf R A B
        (d ((φ : A' →ₐ[R] A) a)) := by
  rw [derivationComp_apply]
  exact
    (Bialgebra.CounitAlgebra.algEquivSelf_apply R A' B
      -- Both counit algebras are definitionally copies of `B`; this `show` transports
      -- the value to the indexing expected by the `A'`-side equivalence.
      (show Bialgebra.CounitAlgebra R A' B from
        d ((φ : A' →ₐ[R] A) a))).trans
      (Bialgebra.CounitAlgebra.algEquivSelf_apply R A B
        (d ((φ : A' →ₐ[R] A) a))).symm

private lemma derivationComp_toLinearMap (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    (derivationComp (B := B) φ d :
        A' →ₗ[R] Bialgebra.CounitAlgebra R A' B) =
      (d : A →ₗ[R] Bialgebra.CounitAlgebra R A B).comp
        (φ : A' →ₐc[R] A).toLinearMap := by
  ext x
  -- The codomains are two exported synonyms for `B`; the pointwise API states exactly
  -- the equality after that identification.
  change derivationComp (B := B) φ d x = d ((φ : A' →ₐ[R] A) x)
  exact derivationComp_apply φ d x

private lemma convTriple_comp_apply (φ : A' →ₐc[R] A)
    (f g h : A →ₗ[R] Bialgebra.CounitAlgebra R A B) (a : A') :
    (toConv f * toConv g * toConv h).ofConv ((φ : A' →ₐ[R] A) a) =
      (toConv (f.comp (φ : A' →ₐc[R] A).toLinearMap) *
        toConv (g.comp (φ : A' →ₐc[R] A).toLinearMap) *
        toConv (h.comp (φ : A' →ₐc[R] A).toLinearMap)).ofConv a := by
  have houter := DFunLike.congr_fun
    (LinearMap.convMul_comp_coalgHom_distrib (toConv f * toConv g) (toConv h)
      (φ : A' →ₗc[R] A)) a
  have hinner := LinearMap.convMul_comp_coalgHom_distrib (toConv f) (toConv g)
    (φ : A' →ₗc[R] A)
  simp only [LinearMap.comp_apply] at houter
  rw [hinner] at houter
  exact houter

/-- **The differential of a Hopf-algebra morphism intertwines the adjoint actions.**

Contravariantly, `φ : A' →ₐc[R] A` represents a morphism `Spec A → Spec A'`.
Precomposing both a point and a tangent derivation with `φ` commutes with convolution
conjugation. -/
@[simp]
theorem derivationComp_adDerivation (φ : A' →ₐc[R] A)
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) φ (Derivation.adDerivation B g d) =
      Derivation.adDerivation B
        (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ g)
        (derivationComp (B := B) φ d) := by
  have mapDomain_inv :
      (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ g)⁻¹ =
        AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ (g⁻¹) :=
    ((AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ).map_inv g).symm
  apply Derivation.ext
  intro a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A' B).injective
  rw [algEquivSelf_derivationComp_apply, Derivation.adDerivation_apply,
    Derivation.adDerivation_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply, convTriple_comp_apply,
    mapDomain_inv, derivationComp_toLinearMap]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_toLinearMap]
  rfl

end TauCeti
