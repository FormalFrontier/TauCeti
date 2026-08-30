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
variable (G : Type v) [Group G] [Finite G]

private theorem toPoints_surjective :
    Function.Surjective (toPoints k G) := by
  intro p
  let e := functionAlgEquiv k G
  obtain ⟨g, hg⟩ := (Pi.evalAlgHomEquiv k G).surjective (p.ofConv.comp e.symm.toAlgHom)
  refine ⟨g, ?_⟩
  apply ofConv_injective
  rw [toPoints_apply]
  ext a
  rw [eval_apply]
  have ha := DFunLike.congr_fun hg (e a)
  change e a g = p.ofConv a
  rw [Pi.evalAlgHomEquiv_apply, Pi.evalAlgHom_apply, AlgHom.comp_apply] at ha
  change e a g = p.ofConv (e.symm (e a)) at ha
  rw [e.symm_apply_apply] at ha
  exact ha

/-- The base-valued points of the constant group attached to a finite group `G` are canonically
`G` itself. -/
noncomputable def pointsMulEquiv :
    G ≃* WithConv (coordinateRing k G →ₐ[k] k) :=
  MulEquiv.ofBijective (toPoints k G)
    ⟨toPoints_injective k G, toPoints_surjective G⟩

/-- The canonical equivalence from a finite group to its constant-group points is evaluation. -/
@[simp]
theorem pointsMulEquiv_apply (g : G) :
    pointsMulEquiv (k := k) G g = toConv (eval k G g) := by
  change toPoints k G g = toConv (eval k G g)
  apply ofConv_injective
  rw [toPoints_apply]

/-- The inverse point equivalence sends evaluation at `g` back to `g`. -/
@[simp]
theorem pointsMulEquiv_symm_apply_eval (g : G) :
    (pointsMulEquiv (k := k) G).symm (toConv (eval k G g)) = g := by
  rw [← pointsMulEquiv_apply]
  exact (pointsMulEquiv (k := k) G).symm_apply_apply g

variable {H : Type w} [CommRing H] [Bialgebra k H]

/-- A coordinate bialgebra morphism from the function algebra of a finite group to `H` induces
a homomorphism from the base-valued points of `Spec H` to that finite group. -/
noncomputable def pointHom (f : coordinateRing k G →ₐc[k] H) :
    WithConv (H →ₐ[k] k) →* G :=
  (pointsMulEquiv (k := k) G).symm.toMonoidHom.comp (AlgHom.mapDomain f)

/-- The point homomorphism induced by `f` is characterized by evaluation after precomposition
with `f`. -/
theorem pointsMulEquiv_pointHom (f : coordinateRing k G →ₐc[k] H)
    (p : WithConv (H →ₐ[k] k)) :
    pointsMulEquiv (k := k) G (pointHom G f p) = AlgHom.mapDomain f p := by
  exact (pointsMulEquiv (k := k) G).apply_symm_apply (AlgHom.mapDomain f p)

/-- Pointwise, the coordinate map induced by `pointHom f p` is precomposition with `f`. -/
theorem eval_pointHom (f : coordinateRing k G →ₐc[k] H)
    (p : WithConv (H →ₐ[k] k)) :
    eval k G (pointHom G f p) = p.ofConv.comp f.toAlgHom := by
  have h := congrArg ofConv (pointsMulEquiv_pointHom G f p)
  simpa only [pointsMulEquiv_apply, ofConv_toConv, AlgHom.mapDomain_apply] using h

/-- A coordinate morphism induced contravariantly by a homomorphism of finite groups recovers
that homomorphism on base-valued points. -/
@[simp]
theorem pointHom_coordinateBialgHom
    {F : Type w} [Group F] [Finite F] (q : F →* G) :
    (pointHom G (coordinateBialgHom k F G q)).comp
      (pointsMulEquiv (k := k) F) = q := by
  apply MonoidHom.ext
  intro x
  rw [MonoidHom.comp_apply]
  apply (pointsMulEquiv (k := k) G).injective
  rw [pointsMulEquiv_pointHom, pointsMulEquiv_apply]
  change AlgHom.mapDomain (coordinateBialgHom k F G q)
    (pointsMulEquiv (k := k) F x) = toConv (eval k G (q x))
  rw [pointsMulEquiv_apply, AlgHom.mapDomain_apply]
  apply ofConv_injective
  simpa only [ofConv_toConv, coordinateBialgHom_toAlgHom] using
    eval_comp_coordinateMap k F G q x

/-- A connected affine group's homomorphism to a finite constant group is trivial on base-valued
points. -/
theorem pointHom_eq_one_of_connected
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : coordinateRing k G →ₐc[k] H) :
    pointHom G f = 1 := by
  apply MonoidHom.ext
  intro p
  apply (pointsMulEquiv (k := k) G).injective
  rw [pointsMulEquiv_pointHom, MonoidHom.one_apply, map_one]
  exact point_comp_eq_one_of_connected G hconnected f p.ofConv

/-- Pointwise form of `pointHom_eq_one_of_connected`. -/
theorem pointHom_apply_eq_one_of_connected
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : coordinateRing k G →ₐc[k] H)
    (p : WithConv (H →ₐ[k] k)) :
    pointHom G f p = 1 := by
  rw [pointHom_eq_one_of_connected G hconnected f, MonoidHom.one_apply]

end

end TauCeti.ConstantGroup
