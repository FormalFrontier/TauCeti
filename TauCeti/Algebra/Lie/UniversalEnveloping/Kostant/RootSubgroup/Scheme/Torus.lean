/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.GeneralLinear
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

/-!
# The split maximal torus as a subgroup scheme of `GLₙ`

A weight basis `b` of a Kostant-stable lattice `M` presents the split torus `𝔾ₘ^κ` inside the
automorphisms of the base-changed lattice: a point `s : κ → Aˣ` scales the basis vector `b x` by
the value `∏ⱼ sⱼ ^ wt x j` of its weight character. That homomorphism of points is
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints`; this file upgrades it to an actual
morphism of affine group schemes over `ℤ`,

```text
𝔾ₘ^κ ⟶ GLₙ,
```

by reading the weights as characters of the split torus and taking the associated diagonal
representation. The two descriptions agree on points of every value ring, so all the pinning
equations proved for `kostantTorusPoints` — in particular
`kostantTorusPoints_conj_kostantRootSubgroupParam`, the conjugation formula
`t(s) xᵢ(u) t(s)⁻¹ = xᵢ(α(s) u)` — are statements about this morphism.

When the weights span the lattice of exponent vectors the representation is faithful, and the
torus is then a *closed* subgroup scheme of `GLₙ`, which is what makes it part of the data of a
pinning rather than an abstract subgroup. Simply connected Chevalley groups are the case a
consumer asks for first: there the weights of a faithful representation span the weight lattice.

Integral PBW must still supply the finite free admissible lattices used by the
Chevalley--Demazure construction; the results here apply once such a lattice and weight basis are
given. The representation carrier is universe-zero because the group-scheme reconstruction API
requires the base, coordinate Hopf algebra, and comodule to inhabit the same universe.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusScheme`: the split maximal torus as a morphism
  of affine group schemes `𝔾ₘ^κ ⟶ GLₙ`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantTorusClosedSubgroup`: the resulting closed subgroup
  scheme of `GLₙ`.

## Main results

* `pointToGeneralLinear_diagonalCoordinateMap_eq_kostantTorusPoints_apply`: on points, the
  represented torus is the original diagonal action `kostantTorusPoints`.
* `TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantTorusScheme`: spanning weights make
  it a closed immersion.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

variable {κ : Type} {M : Type} [AddCommMonoid M] [Module ℤ M]
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)
variable [Fintype κ]

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

/-- The split maximal torus of a weight basis, as a morphism of affine group schemes
`𝔾ₘ^κ ⟶ GLₙ` over `ℤ`.

It is the diagonal representation of the split torus whose weight characters are the weights of
the basis. -/
noncomputable def kostantTorusScheme :
    SplitTorus.groupScheme ℤ κ ⟶ GeneralLinear.groupScheme ℤ n :=
  DiagonalizableGroup.diagonalGroupSchemeHom (SplitTorus.characterGroup κ) b fun x =>
    SplitTorus.weightCharacter (wt x)

/-- **A weight basis whose weights span the lattice of exponent vectors presents the split torus
as a closed subgroup of `GLₙ`.** -/
theorem isClosedImmersion_kostantTorusScheme
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    IsClosedImmersion (kostantTorusScheme b wt).hom.hom.left :=
  DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom (SplitTorus.characterGroup κ) b _
    (SplitTorus.closure_range_weightCharacter_eq_top wt hwt)

/-- The split maximal torus of a weight basis with spanning weights, as a closed subgroup scheme
of `GLₙ`. -/
noncomputable def kostantTorusClosedSubgroup (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    ClosedSubgroupScheme (GeneralLinear.groupScheme ℤ n) :=
  haveI := isClosedImmersion_kostantTorusScheme b wt hwt
  ClosedSubgroupScheme.mk (kostantTorusScheme b wt)

section Points

variable {V : Type} [AddCommGroup V] [Module ℚ V] (L : AddSubgroup V)
variable (bL : Module.Basis (Fin n) ℤ L)

omit [Module ℚ V] in
/-- **On points, the represented split torus is the original diagonal action.** The matrix of the
point `q` of `𝔾ₘ^κ` in the basis `bL` is the matrix of `kostantTorusPoints` at the coordinate
family of `q`. -/
theorem pointToGeneralLinear_diagonalCoordinateMap_eq_kostantTorusPoints_apply
    (A : Type) [CommRing A]
    (q : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) (i j : Fin n) :
    (GeneralLinear.pointToGeneralLinear n
        (toConv (q.ofConv.comp
          (DiagonalizableGroup.diagonalCoordinateMap bL
            (fun x => SplitTorus.weightCharacter (wt x))).toAlgHom)) :
          Matrix (Fin n) (Fin n) A) i j =
      (bL.baseChange A).repr
        ((kostantTorusPoints L bL wt A (SplitTorus.pointsMulEquiv q)).val
          (bL.baseChange A j)) i := by
  classical
  have hmat := DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap bL
    (fun x => SplitTorus.weightCharacter (wt x)) q
  rw [congrFun (congrFun hmat i) j, Module.Basis.baseChange_apply,
    kostantTorusPoints_tmul_basis L bL wt _ 1 j, Module.Basis.baseChange_repr_tmul, bL.repr_self]
  rcases eq_or_ne i j with rfl | hij
  · simp [SplitTorus.charOfPoint_weightCharacter]
  · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]

end Points

end TauCeti.UniversalEnvelopingAlgebra
