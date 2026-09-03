/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Functoriality
import TauCeti.Algebra.Algebra.Pi

/-!
# Constant finite groups

Let `G` be a finite group and `R` a commutative ring. The coordinate ring of the constant
`R`-group associated to `G` is the function algebra `G → R`. We construct it intrinsically as
the finite Hopf dual of the group algebra `R[G]`. This supplies its Hopf structure without making
choices and proves that its underlying algebra is finite étale over `R`.

The formulas below identify multiplication, comultiplication, counit, and antipode with the usual
pointwise product, group multiplication, identity, and inversion. Evaluation at a group element is
then an algebra point, and these evaluations multiply exactly as the elements of `G` do.

## Main declarations

* `TauCeti.ConstantGroup.coordinateRing`: the Hopf algebra of functions on a finite group.
* `TauCeti.ConstantGroup.functionAlgEquiv`: its canonical equivalence with `G → R`.
* `TauCeti.ConstantGroup.eval`: evaluation at a group element as an algebra homomorphism.
* `TauCeti.ConstantGroup.toPoints`: the group homomorphism from `G` to its algebra points.
* `TauCeti.ConstantGroup.coordinateBialgHom`: contravariant pullback along a group homomorphism.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConstantGroup

universe u v w

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [Finite G]

/-- The coordinate ring of the constant group attached to a finite group `G` over `R`.

It is defined as the finite Hopf dual of the group algebra. -/
abbrev coordinateRing := ConvolutionDual R (MonoidAlgebra R G)

omit [Group G] in
/-- The underlying linear equivalence between the coordinate ring and the algebra of functions
on `G`. -/
noncomputable def functionLinearEquiv : coordinateRing R G ≃ₗ[R] (G → R) := by
  classical
  exact (WithConv.linearEquiv R _).trans (MonoidAlgebra.basis G R).dualBasis.equivFun

omit [Group G] in
@[simp]
theorem functionLinearEquiv_apply (f : coordinateRing R G) (g : G) :
    functionLinearEquiv R G f g = f.ofConv (MonoidAlgebra.single g 1) := by
  classical
  exact (MonoidAlgebra.basis G R).dualBasis_equivFun f.ofConv g

omit [Group G] in
private theorem functionLinearEquiv_map_one :
    functionLinearEquiv R G (1 : coordinateRing R G) = 1 := by
  ext g
  simp [functionLinearEquiv_apply, LinearMap.convOne_apply]

omit [Group G] in
private theorem functionLinearEquiv_map_mul (f h : coordinateRing R G) :
    functionLinearEquiv R G (f * h) = functionLinearEquiv R G f * functionLinearEquiv R G h := by
  ext g
  rw [Pi.mul_apply]
  simp [functionLinearEquiv_apply, LinearMap.convMul_apply]

omit [Group G] in
/-- The coordinate ring of a finite constant group is canonically the function algebra `G → R`.
-/
noncomputable def functionAlgEquiv : coordinateRing R G ≃ₐ[R] (G → R) :=
  AlgEquiv.ofLinearEquiv (functionLinearEquiv R G) (functionLinearEquiv_map_one R G)
    (functionLinearEquiv_map_mul R G)

omit [Group G] in
@[simp]
theorem functionAlgEquiv_apply (f : coordinateRing R G) (g : G) :
    functionAlgEquiv R G f g = f.ofConv (MonoidAlgebra.single g 1) := by
  simp [functionAlgEquiv, functionLinearEquiv_apply]

omit [Group G] in
/-- The coordinate ring of a finite constant group is finite étale over the base ring. -/
noncomputable instance instEtale : Algebra.Etale R (coordinateRing R G) :=
  Algebra.Etale.of_equiv (functionAlgEquiv R G).symm

omit [Group G] in
/-- Evaluation at a group element, regarded as an algebra point of the constant group. -/
noncomputable def eval (g : G) : coordinateRing R G →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : G ↦ R) g).comp (functionAlgEquiv R G).toAlgHom

omit [Group G] in
@[simp]
theorem eval_apply (g : G) (f : coordinateRing R G) :
    eval R G g f = functionAlgEquiv R G f g := by
  simp [eval]

/-- Comultiplication on the coordinate ring is dual to multiplication in `G`. -/
theorem comul_apply (f : coordinateRing R G) (g h : G) :
    ConvolutionDual.dualDistribEquiv R (MonoidAlgebra R G) (Coalgebra.comul f)
        (MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single h 1) =
      functionAlgEquiv R G f (g * h) := by
  rw [ConvolutionDual.dualDistribEquiv_comul_apply, functionAlgEquiv_apply]
  simp

/-- The counit of the coordinate ring is evaluation at the identity of `G`. -/
theorem counit_apply (f : coordinateRing R G) :
    Coalgebra.counit (R := R) f = functionAlgEquiv R G f 1 := by
  rw [ConvolutionDual.counit_apply, functionAlgEquiv_apply]
  rw [MonoidAlgebra.one_def]

/-- The antipode of the coordinate ring sends a function `f` to `g ↦ f (g⁻¹)`. -/
theorem antipode_apply (f : coordinateRing R G) (g : G) :
    functionAlgEquiv R G (HopfAlgebra.antipode R f) g = functionAlgEquiv R G f g⁻¹ := by
  rw [functionAlgEquiv_apply, ConvolutionDual.antipode_apply,
    MonoidAlgebra.antipode_single, functionAlgEquiv_apply]
  simp

private theorem dualDistribEquiv_apply_single
    (w : coordinateRing R G ⊗[R] coordinateRing R G) (g h : G) :
    ConvolutionDual.dualDistribEquiv R (MonoidAlgebra R G) w
        (MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single h 1) =
      Algebra.TensorProduct.lift (eval R G g) (eval R G h) (fun _ _ ↦ .all _ _) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (fun a b ↦ a + b) hx hy
  | tmul f k =>
      rw [ConvolutionDual.dualDistribEquiv_tmul_apply]
      simp [eval_apply]

/-- Evaluation points multiply according to multiplication in `G`. -/
theorem eval_mul (g h : G) :
    WithConv.toConv (eval R G (g * h)) =
      WithConv.toConv (eval R G g) * WithConv.toConv (eval R G h) := by
  symm
  apply WithConv.ofConv_injective
  ext f
  rw [AlgHom.convMul_apply, eval_apply]
  rw [← dualDistribEquiv_apply_single R G]
  simpa only [functionAlgEquiv_apply] using comul_apply R G f g h

/-- Evaluation at the identity is the identity element among algebra points. -/
theorem eval_one : WithConv.toConv (eval R G (1 : G)) = 1 := by
  apply WithConv.ofConv_injective
  ext f
  rw [eval_apply, AlgHom.convOne_apply]
  simpa using (counit_apply R G f).symm

/-- A finite group maps canonically to the group of algebra points of its constant group. -/
noncomputable def toPoints : G →* WithConv (coordinateRing R G →ₐ[R] R) where
  toFun g := WithConv.toConv (eval R G g)
  map_one' := eval_one R G
  map_mul' g h := eval_mul R G g h

@[simp]
theorem toPoints_apply (g : G) : (toPoints R G g).ofConv = eval R G g := by
  simp [toPoints]

/-- Over a nontrivial base ring, evaluation distinguishes the elements of the constant group. -/
theorem toPoints_injective [Nontrivial R] : Function.Injective (toPoints R G) := by
  intro g h hgh
  have hmaps := congrArg WithConv.ofConv hgh
  rw [toPoints_apply, toPoints_apply] at hmaps
  apply Pi.evalAlgHom_injective R G
  ext f
  obtain ⟨x, rfl⟩ := (functionAlgEquiv R G).surjective f
  simpa only [eval_apply, Pi.evalAlgHom_apply] using DFunLike.congr_fun hmaps x

section Functoriality

variable (H : Type w) [Group H] [Finite H]

omit [Group G] [Finite G] [Group H] [Finite H] in
/-- Pull functions back along a map of types. -/
def functionPullback (f : G → H) : (H → R) →ₐ[R] (G → R) where
  toFun a := a ∘ f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Group G] [Finite G] [Group H] [Finite H] in
@[simp]
theorem functionPullback_apply (f : G → H) (a : H → R) (g : G) :
    functionPullback R G H f a g = a (f g) := by
  unfold functionPullback
  rfl

/-- A group homomorphism induces a contravariant bialgebra morphism of constant-group coordinate
rings. -/
noncomputable def coordinateBialgHom (f : G →* H) :
    coordinateRing R H →ₐc[R] coordinateRing R G :=
  ConvolutionDual.map R (MonoidAlgebra.mapDomainBialgHom R f)

/-- The underlying algebra homomorphism of `coordinateBialgHom`. -/
noncomputable def coordinateMap (f : G →* H) : coordinateRing R H →ₐ[R] coordinateRing R G :=
  (coordinateBialgHom R G H f).toAlgHom

/-- The algebra homomorphism underlying `coordinateBialgHom` is `coordinateMap`. -/
@[simp]
theorem coordinateBialgHom_toAlgHom (f : G →* H) :
    (coordinateBialgHom R G H f).toAlgHom = coordinateMap R G H f := by
  unfold coordinateMap
  rfl

/-- Under `functionAlgEquiv`, the coordinate map is precomposition by the group homomorphism. -/
theorem functionAlgEquiv_coordinateMap_apply (f : G →* H) (a : coordinateRing R H) (g : G) :
    functionAlgEquiv R G (coordinateMap R G H f a) g = functionAlgEquiv R H a (f g) := by
  simp [coordinateMap, coordinateBialgHom, functionAlgEquiv_apply]

/-- The coordinate map induced by the identity group homomorphism is the identity. -/
@[simp]
theorem coordinateMap_id :
    coordinateMap R G G (MonoidHom.id G) = AlgHom.id R (coordinateRing R G) := by
  apply DFunLike.ext
  intro a
  apply (functionAlgEquiv R G).injective
  ext g
  rw [functionAlgEquiv_coordinateMap_apply]
  rfl

/-- Coordinate maps reverse composition of group homomorphisms. -/
@[simp]
theorem coordinateMap_comp (K : Type*) [Group K] [Finite K]
    (f : G →* H) (q : H →* K) :
    coordinateMap R G K (q.comp f) =
      (coordinateMap R G H f).comp (coordinateMap R H K q) := by
  apply DFunLike.ext
  intro a
  apply (functionAlgEquiv R G).injective
  ext g
  rw [AlgHom.comp_apply, functionAlgEquiv_coordinateMap_apply,
    functionAlgEquiv_coordinateMap_apply,
    functionAlgEquiv_coordinateMap_apply]
  rfl

/-- Evaluation is natural with respect to the coordinate map induced by a group homomorphism. -/
@[simp]
theorem eval_comp_coordinateMap (f : G →* H) (g : G) :
    (eval R G g).comp (coordinateMap R G H f) = eval R H (f g) := by
  ext a
  rw [AlgHom.comp_apply, eval_apply, functionAlgEquiv_coordinateMap_apply, eval_apply]

end Functoriality

end TauCeti.ConstantGroup
