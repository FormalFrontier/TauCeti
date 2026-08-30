/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.Algebra.Algebra.Pi

/-!
# Rational points of finite constant groups

Let `G` be a finite group and `k` a field. The `k`-valued points of the constant group attached
to `G` are canonically `G` itself. Indeed, every `k`-algebra homomorphism from the function
algebra `k^G` to `k` is evaluation at a unique element of `G`.

This identification turns a coordinate bialgebra morphism `k^G \to H` into a group homomorphism
from the `k`-valued points of `Spec H` to `G`. If `Spec H` is connected, that homomorphism is
trivial by `ConstantGroup.point_comp_eq_one_of_connected`.

The point-level formulation is the interface needed by the Lie--Kolchin argument. Its finite
permutation action is naturally stated as a homomorphism to a finite symmetric group, whereas
connectedness applies to the corresponding morphism of affine group schemes.

## Main declarations

* `TauCeti.ConstantGroup.pointsMulEquiv`: the canonical multiplicative equivalence between a
  finite group and the base-valued points of its constant group.
* `TauCeti.ConstantGroup.pointHom`: the homomorphism on base-valued points induced by a coordinate
  bialgebra morphism to a finite constant group.
* `TauCeti.ConstantGroup.pointHom_eq_one_of_connected`: connected affine groups have no nontrivial
  algebraic homomorphism to a finite constant group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.34.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.

This advances the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap.
-/

public section

open WithConv

namespace TauCeti.ConstantGroup

universe u v w

noncomputable section

variable {k : Type u} [Field k]

private theorem toPoints_surjective (G : Type v) [Group G] [Finite G] :
    Function.Surjective (toPoints k G) := by
  intro p
  obtain ⟨g, hg⟩ := (Pi.evalAlgHomEquiv k G).surjective
    (p.ofConv.comp (functionAlgEquiv k G).symm.toAlgHom)
  refine ⟨g, ?_⟩
  apply ofConv_injective
  rw [toPoints_apply]
  ext a
  rw [eval_apply]
  have ha := DFunLike.congr_fun hg (functionAlgEquiv k G a)
  rw [Pi.evalAlgHomEquiv_apply, Pi.evalAlgHom_apply, AlgHom.comp_apply] at ha
  exact ha.trans (congrArg p.ofConv ((functionAlgEquiv k G).symm_apply_apply a))

/-- The base-valued points of the constant group attached to a finite group `G` are canonically
`G` itself. -/
noncomputable def pointsMulEquiv (k : Type u) [Field k]
    (G : Type v) [Group G] [Finite G] :
    G ≃* WithConv (coordinateRing k G →ₐ[k] k) :=
  MulEquiv.ofBijective (toPoints k G)
    ⟨toPoints_injective k G, toPoints_surjective G⟩

/-- The canonical equivalence from a finite group to its constant-group points is evaluation. -/
@[simp]
theorem pointsMulEquiv_apply (G : Type v) [Group G] [Finite G] (g : G) :
    pointsMulEquiv k G g = toConv (eval k G g) := by
  apply ofConv_injective
  exact toPoints_apply k G g

variable {H : Type w} [CommRing H] [Bialgebra k H]

/-- A coordinate bialgebra morphism from the function algebra of a finite group to `H` induces
a homomorphism from the base-valued points of `Spec H` to that finite group. -/
noncomputable def pointHom {G : Type v} [Group G] [Finite G]
    (f : coordinateRing k G →ₐc[k] H) :
    WithConv (H →ₐ[k] k) →* G :=
  (pointsMulEquiv k G).symm.toMonoidHom.comp (AlgHom.mapDomain f)

/-- The point homomorphism induced by `f` is characterized by evaluation after precomposition
with `f`. -/
theorem pointsMulEquiv_pointHom {G : Type v} [Group G] [Finite G]
    (f : coordinateRing k G →ₐc[k] H)
    (p : WithConv (H →ₐ[k] k)) :
    pointsMulEquiv k G (pointHom f p) = AlgHom.mapDomain f p := by
  exact (pointsMulEquiv k G).apply_symm_apply (AlgHom.mapDomain f p)

/-- Pointwise, the coordinate map induced by `pointHom f p` is precomposition with `f`. -/
@[simp]
theorem eval_pointHom {G : Type v} [Group G] [Finite G]
    (f : coordinateRing k G →ₐc[k] H)
    (p : WithConv (H →ₐ[k] k)) :
    eval k G (pointHom f p) = p.ofConv.comp f.toAlgHom := by
  have h := congrArg ofConv (pointsMulEquiv_pointHom f p)
  simpa only [pointsMulEquiv_apply, ofConv_toConv, AlgHom.mapDomain_apply] using h

/-- A coordinate morphism induced contravariantly by a homomorphism of finite groups recovers
that homomorphism on base-valued points. -/
@[simp]
theorem pointHom_coordinateBialgHom
    {G : Type v} [Group G] [Finite G]
    {F : Type w} [Group F] [Finite F] (q : F →* G) :
    (pointHom (coordinateBialgHom k F G q)).comp (pointsMulEquiv k F) = q := by
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply]
  apply (pointsMulEquiv k G).injective
  rw [pointsMulEquiv_pointHom, pointsMulEquiv_apply]
  rw [AlgHom.mapDomain_apply]
  apply congrArg toConv
  have hx : (pointsMulEquiv k F x).ofConv = eval k F x :=
    congrArg ofConv (pointsMulEquiv_apply (k := k) F x)
  -- Normalize the `MulEquiv` coercion so that the pointwise equality `hx` can rewrite.
  change (pointsMulEquiv k F x).ofConv.comp (coordinateBialgHom k F G q).toAlgHom =
    eval k G (q x)
  rw [hx]
  simpa only [coordinateBialgHom_toAlgHom] using
    eval_comp_coordinateMap k F G q x

/-- Pointwise, the morphism on points induced by a finite-group homomorphism is that
homomorphism. -/
@[simp]
theorem pointHom_coordinateBialgHom_apply
    {G : Type v} [Group G] [Finite G]
    {F : Type w} [Group F] [Finite F] (q : F →* G) (x : F) :
    pointHom (coordinateBialgHom k F G q) (toConv (eval k F x)) = q x := by
  rw [← pointsMulEquiv_apply]
  convert DFunLike.congr_fun (pointHom_coordinateBialgHom (k := k) q) x using 1
  rfl

/-- A connected affine group's homomorphism to a finite constant group is trivial on base-valued
points. -/
theorem pointHom_eq_one_of_connected {G : Type v} [Group G] [Finite G]
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : coordinateRing k G →ₐc[k] H) :
    pointHom f = 1 := by
  apply MonoidHom.ext
  intro p
  apply (pointsMulEquiv k G).injective
  rw [pointsMulEquiv_pointHom, MonoidHom.one_apply, map_one]
  exact point_comp_eq_one_of_connected G hconnected f p.ofConv

end

end TauCeti.ConstantGroup
