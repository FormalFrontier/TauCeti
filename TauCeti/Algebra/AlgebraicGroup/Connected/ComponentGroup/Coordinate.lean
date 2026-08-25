/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Group
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.Coalgebra.Convolution
public import TauCeti.RingTheory.Idempotents.Connected.Components
import Mathlib.Algebra.BigOperators.Pi
import TauCeti.AlgebraicGeometry.AugmentationPoint.ConnectedComponent

/-!
# The coordinate map to the component group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically closed
field. The connected components of `Spec H` form a finite group. This file constructs the
algebra map from the functions on that finite group to `H`: a function `f` is sent to

```text
  ∑ C, f(C) e_C,
```

where `e_C` is the canonical idempotent selecting the component `C`. Evaluation at a rational
point `g` recovers `f` on the component of `g`. In particular, the map is injective and represents
the surjective rational component homomorphism.

The compatibility of this algebra map with comultiplication and counit, and hence its upgrade to
the coordinate bialgebra morphism of the component group, is developed in the remainder of this
file.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentFunctionAlgHom`: the algebra map from component-indexed
  functions to the coordinate ring.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentCoordinateMap`: the same map on the canonical
  constant-group coordinate ring.
* `TauCeti.FiniteTypeCommHopfAlgCat.eval_componentCoordinateMap`: evaluation of the coordinate map
  at a rational point is evaluation at its connected component.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom`: the coordinate bialgebra
  morphism of the component map.
* `TauCeti.FiniteTypeCommHopfAlgCat.kernelHopfIdeal_componentCoordinateHom`: its scheme-theoretic
  kernel is the identity component.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

This advances Layer 3, "Identity component `G°` and component group `π₀(G)`", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The finite instance on the connected components of a finite-type affine scheme. -/
noncomputable local instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Fintype (ConnectedComponents (PrimeSpectrum H)) :=
  Fintype.ofFinite _

/-- Classical decidable equality on the finite connected-component group. -/
noncomputable local instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    DecidableEq (ConnectedComponents (PrimeSpectrum H)) :=
  Classical.decEq _

/-- The idempotent-weighted algebra map underlying `componentFunctionAlgHom`. -/
private noncomputable def componentFunctionAlgHomAux
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (ConnectedComponents (PrimeSpectrum H) → k) →ₐ[k] H := by
  classical
  let e : ConnectedComponents (PrimeSpectrum H) → H :=
    PrimeSpectrum.connectedComponentsIdempotent
  let he : CompleteOrthogonalIdempotents e :=
    PrimeSpectrum.completeOrthogonalIdempotents_connectedComponentsIdempotent
  refine
    { toFun := fun f ↦ ∑ C, algebraMap k H (f C) * e C
      map_zero' := by simp
      map_add' := fun f g ↦ by
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_one' := by
        simp only [Pi.one_apply, map_one, one_mul, he.complete]
      map_mul' := fun f g ↦ ?_
      commutes' := fun a ↦ ?_ }
  · rw [Finset.sum_mul_sum]
    symm
    calc
      ∑ x, ∑ y, algebraMap k H (f x) * e x * (algebraMap k H (g y) * e y) =
          ∑ x, algebraMap k H (f x * g x) * e x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single x]
        · calc
            algebraMap k H (f x) * e x * (algebraMap k H (g x) * e x) =
                (algebraMap k H (f x) * algebraMap k H (g x)) * (e x * e x) := by
              ring
            _ = algebraMap k H (f x * g x) * e x := by rw [map_mul, he.idem]
        · intro y _ hyx
          calc
            algebraMap k H (f x) * e x * (algebraMap k H (g y) * e y) =
                (algebraMap k H (f x) * algebraMap k H (g y)) * (e x * e y) := by
              ring
            _ = 0 := by rw [he.ortho hyx.symm, mul_zero]
        · simp
      _ = ∑ x, algebraMap k H ((f * g) x) * e x := by rfl
  · simp only [Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [← Finset.mul_sum, he.complete, mul_one]

/-- The algebra map from functions on the connected-component group to the coordinate ring.

A function `f` is sent to the sum `∑ C, f(C) e_C`, where `e_C` is the canonical idempotent
selecting the connected component `C`. -/
noncomputable def componentFunctionAlgHom (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (ConnectedComponents (PrimeSpectrum H) → k) →ₐ[k] H :=
  componentFunctionAlgHomAux H

omit [IsAlgClosed k] in
/-- The component function algebra map is the idempotent-weighted sum over connected components.
-/
theorem componentFunctionAlgHom_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (f : ConnectedComponents (PrimeSpectrum H) → k) :
    componentFunctionAlgHom H f =
      ∑ C, algebraMap k H (f C) * PrimeSpectrum.connectedComponentsIdempotent C := by
  rfl

/-- A rational point evaluates the idempotent of its connected component to one. -/
theorem map_connectedComponentsIdempotent_eq_one
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    {C : ConnectedComponents (PrimeSpectrum H)} (hC : rationalComponentMap H g = C) :
    g.ofConv (PrimeSpectrum.connectedComponentsIdempotent C) = 1 := by
  rw [rationalComponentMap_apply] at hC
  rw [← hC, PrimeSpectrum.connectedComponentsIdempotent_mk]
  exact TauCeti.AlgHom.map_connectedComponentIdempotent_kernelPoint_eq_one g.ofConv

/-- A rational point evaluates every other component idempotent to zero. -/
theorem map_connectedComponentsIdempotent_eq_zero
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    {C : ConnectedComponents (PrimeSpectrum H)} (hC : rationalComponentMap H g ≠ C) :
    g.ofConv (PrimeSpectrum.connectedComponentsIdempotent C) = 0 := by
  have hidem : IsIdempotentElem
      (g.ofConv (PrimeSpectrum.connectedComponentsIdempotent C)) :=
    (PrimeSpectrum.isIdempotentElem_connectedComponentsIdempotent C).map g.ofConv
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with hzero | hone
  · exact hzero
  · exfalso
    apply hC
    rw [rationalComponentMap_apply]
    apply (PrimeSpectrum.mem_basicOpen_connectedComponentsIdempotent C
      (rationalKernelPoint H g)).mp
    rw [PrimeSpectrum.mem_basicOpen]
    intro hmem
    have : g.ofConv (PrimeSpectrum.connectedComponentsIdempotent C) = 0 := by
      simpa [RingHom.mem_ker] using hmem
    exact zero_ne_one (this.symm.trans hone)

/-- Evaluation of a component-indexed function at a rational point is evaluation at the
connected component containing that point. -/
@[simp]
theorem eval_componentFunctionAlgHom (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (f : ConnectedComponents (PrimeSpectrum H) → k) :
    g.ofConv (componentFunctionAlgHom H f) = f (rationalComponentMap H g) := by
  classical
  rw [componentFunctionAlgHom_apply, map_sum]
  simp only [map_mul, AlgHom.commutes]
  rw [Finset.sum_eq_single (rationalComponentMap H g)]
  · rw [map_connectedComponentsIdempotent_eq_one H g rfl, mul_one,
      Algebra.algebraMap_self_apply]
  · intro C _ hC
    rw [map_connectedComponentsIdempotent_eq_zero H g hC.symm, mul_zero]
  · simp

/-- The component function algebra embeds in the coordinate ring. -/
theorem componentFunctionAlgHom_injective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Injective (componentFunctionAlgHom H) := by
  intro f g hfg
  funext C
  obtain ⟨x, hx⟩ := rationalComponentMap_surjective H C
  rw [← hx, ← eval_componentFunctionAlgHom H x f,
    ← eval_componentFunctionAlgHom H x g, hfg]

/-- The coordinate algebra map representing projection to the finite constant group of connected
components. -/
noncomputable def componentCoordinateMap (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)) →ₐ[k] H :=
  (componentFunctionAlgHom H).comp
    (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).toAlgHom

omit [IsAlgClosed k] in
/-- The component coordinate map is the idempotent-weighted sum of the values of a coordinate
function on each component. -/
theorem componentCoordinateMap_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) :
    componentCoordinateMap H x = ∑ C,
      algebraMap k H (x.ofConv (MonoidAlgebra.single C 1)) *
        PrimeSpectrum.connectedComponentsIdempotent C := by
  classical
  calc
    componentCoordinateMap H x = componentFunctionAlgHom H
        (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H)) x) := rfl
    _ = ∑ C, algebraMap k H
        (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H)) x C) *
          PrimeSpectrum.connectedComponentsIdempotent C := componentFunctionAlgHom_apply H _
    _ = ∑ C, algebraMap k H (x.ofConv (MonoidAlgebra.single C 1)) *
        PrimeSpectrum.connectedComponentsIdempotent C := by
      apply Finset.sum_congr rfl
      intro C _
      exact congrArg
        (fun a ↦ algebraMap k H a * PrimeSpectrum.connectedComponentsIdempotent C)
        (ConstantGroup.functionAlgEquiv_apply k _ x C)

omit [IsAlgClosed k] in
/-- The component coordinate map sends the indicator of a component to its canonical component
idempotent. -/
@[simp]
theorem componentCoordinateMap_indicator (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (C : ConnectedComponents (PrimeSpectrum H)) :
    componentCoordinateMap H
        ((ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).symm
          (Pi.single C 1)) = PrimeSpectrum.connectedComponentsIdempotent C := by
  classical
  have happ :=
    (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).apply_symm_apply
      (Pi.single C 1)
  calc
    componentCoordinateMap H
        ((ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).symm
          (Pi.single C 1)) = componentFunctionAlgHom H (Pi.single C 1) :=
      congrArg (componentFunctionAlgHom H) happ
    _ = PrimeSpectrum.connectedComponentsIdempotent C := by
      rw [componentFunctionAlgHom_apply]
      rw [Finset.sum_eq_single C]
      · simp
      · intro D _ hDC
        rw [Pi.single_eq_of_ne hDC]
        simp
      · simp

/-- The component coordinate map is injective. -/
theorem componentCoordinateMap_injective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Injective (componentCoordinateMap H) :=
  (componentFunctionAlgHom_injective H).comp
    (ConstantGroup.functionAlgEquiv k (ConnectedComponents (PrimeSpectrum H))).injective

/-- Pulling the component coordinate map back along a rational point is evaluation at that
point's connected component. -/
@[simp]
theorem eval_componentCoordinateMap (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    g.ofConv.comp (componentCoordinateMap H) =
      ConstantGroup.eval k (ConnectedComponents (PrimeSpectrum H)) (rationalComponentMap H g) := by
  ext f
  rw [AlgHom.comp_apply, componentCoordinateMap, AlgHom.comp_apply,
    eval_componentFunctionAlgHom, ConstantGroup.eval_apply]
  rfl

private theorem counitAlgHom_comp_componentCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (Bialgebra.counitAlgHom k H).comp (componentCoordinateMap H) =
      Bialgebra.counitAlgHom k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) := by
  ext f
  have h := AlgHom.congr_fun
    (eval_componentCoordinateMap H
      (1 : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))) f
  rw [map_one] at h
  calc
    ((Bialgebra.counitAlgHom k H).comp (componentCoordinateMap H)) f =
        (1 : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)).ofConv
          (componentCoordinateMap H f) := by
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, AlgHom.convOne_apply,
        Algebra.algebraMap_self_apply]
    _ = ConstantGroup.eval k (ConnectedComponents (PrimeSpectrum H)) 1 f := h
    _ = Bialgebra.counitAlgHom k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) f := by
      rw [Bialgebra.counitAlgHom_apply, ConstantGroup.counit_apply,
        ConstantGroup.eval_apply]

private theorem map_comp_comulAlgHom_componentCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (Algebra.TensorProduct.map (componentCoordinateMap H) (componentCoordinateMap H)).comp
        (Bialgebra.comulAlgHom k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) =
      (Bialgebra.comulAlgHom k H).comp (componentCoordinateMap H) := by
  classical
  let C := ConnectedComponents (PrimeSpectrum H)
  let _ : Algebra.FiniteType k (TensorProduct k H H) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := TensorProduct k H H)
      inferInstance inferInstance
  let delta : C → ConstantGroup.coordinateRing k C :=
    fun D ↦ (ConstantGroup.functionAlgEquiv k C).symm (Pi.single D 1)
  -- It suffices to check the coalgebra law on the delta-function basis. Each side sends a delta
  -- function to an idempotent, so algebraically closed points separate the two images even though
  -- the tensor square of `H` need not be reduced.
  have hdelta (D : C) :
      ((Algebra.TensorProduct.map (componentCoordinateMap H) (componentCoordinateMap H)).comp
          (Bialgebra.comulAlgHom k (ConstantGroup.coordinateRing k C))) (delta D) =
        ((Bialgebra.comulAlgHom k H).comp (componentCoordinateMap H)) (delta D) := by
    have hsingle : IsIdempotentElem (Pi.single D 1 : C → k) :=
      (CompleteOrthogonalIdempotents.single (fun _ : C ↦ k)).idem D
    have hdelta_idem : IsIdempotentElem (delta D) :=
      hsingle.map (ConstantGroup.functionAlgEquiv k C).symm.toRingHom
    apply TauCeti.eq_of_isIdempotentElem_of_forall_algHom_apply_eq
      (k := k) (K := k)
      (hdelta_idem.map
        ((Algebra.TensorProduct.map (componentCoordinateMap H) (componentCoordinateMap H)).comp
          (Bialgebra.comulAlgHom k (ConstantGroup.coordinateRing k C))).toRingHom)
      (hdelta_idem.map
        ((Bialgebra.comulAlgHom k H).comp (componentCoordinateMap H)).toRingHom)
    intro f
    -- Restrict a point of the tensor square to its two factors. Comultiplication evaluates as
    -- convolution on both the constant component group and `H`.
    let g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) :=
      toConv (f.comp (Bialgebra.TensorProduct.includeLeft
        (R := k) (H₁ := H) (H₂ := H)).toAlgHom)
    let h : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) :=
      toConv (f.comp (Bialgebra.TensorProduct.includeRight
        (R := k) (H₁ := H) (H₂ := H)).toAlgHom)
    let q :=
      f.comp (Algebra.TensorProduct.map (componentCoordinateMap H) (componentCoordinateMap H))
    have hqleft :
        q.comp (Bialgebra.TensorProduct.includeLeft (R := k)
          (H₁ := ConstantGroup.coordinateRing k C)
          (H₂ := ConstantGroup.coordinateRing k C)).toAlgHom =
          g.ofConv.comp (componentCoordinateMap H) := by
      simp [q, g, AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft]
    have hqright :
        q.comp (Bialgebra.TensorProduct.includeRight (R := k)
          (H₁ := ConstantGroup.coordinateRing k C)
          (H₂ := ConstantGroup.coordinateRing k C)).toAlgHom =
          h.ofConv.comp (componentCoordinateMap H) := by
      simp [q, h, AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight]
    have hsource :
        q.comp (Bialgebra.comulAlgHom k (ConstantGroup.coordinateRing k C)) =
          ConstantGroup.eval k C (rationalComponentMap H g * rationalComponentMap H h) := by
      apply WithConv.toConv_injective
      rw [Bialgebra.toConv_comp_comulAlgHom, hqleft, hqright,
        eval_componentCoordinateMap, eval_componentCoordinateMap]
      exact (ConstantGroup.eval_mul k C _ _).symm
    have htarget :
        f.comp (Bialgebra.comulAlgHom k H) = (g * h).ofConv := by
      apply WithConv.toConv_injective
      rw [Bialgebra.toConv_comp_comulAlgHom]
    calc
      f (((Algebra.TensorProduct.map (componentCoordinateMap H) (componentCoordinateMap H)).comp
          (Bialgebra.comulAlgHom k (ConstantGroup.coordinateRing k C))) (delta D)) =
          (q.comp (Bialgebra.comulAlgHom k (ConstantGroup.coordinateRing k C))) (delta D) := rfl
      _ = ConstantGroup.eval k C
          (rationalComponentMap H g * rationalComponentMap H h) (delta D) :=
        AlgHom.congr_fun hsource (delta D)
      _ = ConstantGroup.eval k C (rationalComponentMap H (g * h)) (delta D) := by
        rw [map_mul]
      _ = (g * h).ofConv (componentCoordinateMap H (delta D)) :=
        (AlgHom.congr_fun (eval_componentCoordinateMap H (g * h)) (delta D)).symm
      _ = (f.comp (Bialgebra.comulAlgHom k H)) (componentCoordinateMap H (delta D)) := by
        rw [htarget]
      _ = f (((Bialgebra.comulAlgHom k H).comp (componentCoordinateMap H)) (delta D)) := rfl
  apply AlgHom.toLinearMap_injective
  apply LinearMap.ext
  intro a
  have ha : a = ∑ D, (ConstantGroup.functionAlgEquiv k C a D) • delta D := by
    apply (ConstantGroup.functionAlgEquiv k C).injective
    simpa only [map_sum, map_smul, delta, AlgEquiv.apply_symm_apply] using
      (pi_eq_sum_univ' (ConstantGroup.functionAlgEquiv k C a))
  rw [ha, map_sum, map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl fun D _ ↦ congrArg ((ConstantGroup.functionAlgEquiv k C a D) • ·)
    (hdelta D)

/-- The coordinate bialgebra morphism representing projection to the finite constant group of
connected components. -/
noncomputable def componentCoordinateBialgHom (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)) →ₐc[k] H :=
  BialgHom.ofAlgHom (componentCoordinateMap H)
    (counitAlgHom_comp_componentCoordinateMap H)
    (map_comp_comulAlgHom_componentCoordinateMap H)

/-- The algebra homomorphism underlying the component coordinate bialgebra morphism is the
component coordinate map. -/
@[simp]
theorem componentCoordinateBialgHom_toAlgHom (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentCoordinateBialgHom H).toAlgHom = componentCoordinateMap H := by
  rfl

/-- The component coordinate bialgebra morphism agrees pointwise with its underlying algebra
map. -/
@[simp]
theorem componentCoordinateBialgHom_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) :
    componentCoordinateBialgHom H x = componentCoordinateMap H x := by
  rfl

/-- The component coordinate bialgebra morphism is injective. -/
theorem componentCoordinateBialgHom_injective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Injective (componentCoordinateBialgHom H) :=
  componentCoordinateMap_injective H

/-- The component coordinate morphism in the category of commutative Hopf algebras. Relative
spectrum reverses it to the canonical morphism from the affine group to the finite constant group
of connected components. -/
noncomputable def componentCoordinateHom (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.of k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) ⟶ H.obj :=
  CommHopfAlgCat.ofHom (componentCoordinateBialgHom H)

/-- The component coordinate morphism agrees pointwise with the component coordinate map. -/
@[simp]
theorem componentCoordinateHom_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) :
    (componentCoordinateHom H).hom x = componentCoordinateMap H x := by
  rfl

/-- The scheme-theoretic kernel of the component morphism is the identity component: the kernel
Hopf ideal generated by the augmentation ideal of the constant component group is precisely the
identity-component Hopf ideal. -/
theorem kernelHopfIdeal_componentCoordinateHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.kernelHopfIdeal (componentCoordinateHom H) =
      HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) := by
  classical
  let C := ConnectedComponents (PrimeSpectrum H)
  let z : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  have he_one : PrimeSpectrum.connectedComponentsIdempotent
      (1 : ConnectedComponents (PrimeSpectrum H)) =
      PrimeSpectrum.connectedComponentIdempotent z := by
    calc
      PrimeSpectrum.connectedComponentsIdempotent
          (1 : ConnectedComponents (PrimeSpectrum H)) =
          PrimeSpectrum.connectedComponentsIdempotent
            (z : ConnectedComponents (PrimeSpectrum H)) := by
        apply congrArg PrimeSpectrum.connectedComponentsIdempotent
        simpa only [z] using (rationalKernelPoint_one_component H).symm
      _ = PrimeSpectrum.connectedComponentIdempotent z :=
        PrimeSpectrum.connectedComponentsIdempotent_mk z
  apply le_antisymm
  · rw [CommHopfAlgCat.kernelHopfIdeal_def]
    apply (HopfIdeal.map_le_iff).mpr
    intro x hx
    rw [HopfIdeal.mem_augmentation, ConstantGroup.counit_apply] at hx
    rw [ConstantGroup.functionAlgEquiv_apply] at hx
    rw [HopfAlgebra.mem_identityComponentHopfIdeal]
    -- The bundled finite-type object and its coordinate ring are definitionally the same here;
    -- exposing that carrier lets the component-ideal API apply.
    change (componentCoordinateHom H).hom x ∈ PrimeSpectrum.connectedComponentIdeal z
    rw [componentCoordinateHom, CommHopfAlgCat.hom_ofHom]
    -- The categorical morphism was constructed from this algebra map, so its value reduces to the
    -- explicit idempotent-weighted formula.
    change componentCoordinateMap H x ∈ _
    rw [componentCoordinateMap_apply]
    apply Ideal.sum_mem
    intro D _
    by_cases hD : D = 1
    · subst D
      have hcoeff : algebraMap k H
          (x.ofConv (MonoidAlgebra.single 1 1)) = 0 := by
        rw [hx, map_zero]
      rw [hcoeff, zero_mul]
      exact Ideal.zero_mem _
    · rw [PrimeSpectrum.mem_connectedComponentIdeal_iff]
      refine ⟨algebraMap k H
        (x.ofConv (MonoidAlgebra.single D 1)) *
          PrimeSpectrum.connectedComponentsIdempotent D, ?_⟩
      rw [← he_one, mul_sub, mul_one, mul_assoc]
      rw [(PrimeSpectrum.orthogonalIdempotents_connectedComponentsIdempotent).ortho hD,
        mul_zero, sub_zero]
  · rw [← HopfIdeal.toIdeal_le_toIdeal,
      HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    intro y hy
    -- Rewrite the bundled identity-component ideal at its underlying prime-spectrum point.
    change y ∈ PrimeSpectrum.connectedComponentIdeal z at hy
    rw [PrimeSpectrum.mem_connectedComponentIdeal_iff] at hy
    obtain ⟨a, rfl⟩ := hy
    let deltaOne : ConstantGroup.coordinateRing k C :=
      (ConstantGroup.functionAlgEquiv k C).symm (Pi.single 1 1)
    have hdelta_counit : Coalgebra.counit (R := k) deltaOne = 1 := by
      rw [ConstantGroup.counit_apply]
      have happ := congrFun
        ((ConstantGroup.functionAlgEquiv k C).apply_symm_apply (Pi.single 1 1)) (1 : C)
      simpa only [deltaOne, Pi.single_eq_same] using happ
    have haug : Coalgebra.counit (R := k) (1 - deltaOne) = 0 := by
      rw [← Bialgebra.counitAlgHom_apply, map_sub, map_one,
        Bialgebra.counitAlgHom_apply, hdelta_counit, sub_self]
    have hmem := CommHopfAlgCat.mem_kernelHopfIdeal_of_mem_augmentation
      (componentCoordinateHom H) haug
    have hgen : 1 - PrimeSpectrum.connectedComponentIdempotent z ∈
        CommHopfAlgCat.kernelHopfIdeal (componentCoordinateHom H) := by
      convert hmem using 1
      rw [map_sub, map_one, componentCoordinateHom_apply,
        componentCoordinateMap_indicator, he_one]
    exact Ideal.mul_mem_left _ a (HopfIdeal.mem_toIdeal.mpr hgen)

end TauCeti.FiniteTypeCommHopfAlgCat
