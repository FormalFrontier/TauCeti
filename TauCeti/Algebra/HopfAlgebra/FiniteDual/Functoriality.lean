/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic

/-!
# Functoriality and reflexivity of the finite Hopf dual

Dualizing a bialgebra morphism between finite-dimensional bialgebras gives a morphism in the
opposite direction between their convolution duals. Evaluation identifies a finite-dimensional
bialgebra with its double convolution dual, compatibly with multiplication, comultiplication,
unit, and counit.

These are the algebraic functoriality and involutivity statements needed to promote the finite
Hopf dual constructed in `TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic` to Cartier duality. The
scheme-level duality, and finite locally free duality over a general base, remain separate steps.

## Main declarations

* `TauCeti.ConvolutionDual.map`: the contravariant map on finite-dimensional bialgebras.
* `TauCeti.ConvolutionDual.map_id` and `TauCeti.ConvolutionDual.map_comp`: its functoriality laws.
* `TauCeti.ConvolutionDual.mapEquiv`: the contravariant equivalence induced by a bialgebra
  equivalence.
* `TauCeti.ConvolutionDual.evalBialgEquiv`: evaluation as a bialgebra equivalence with the double
  convolution dual.
* `TauCeti.ConvolutionDual.evalBialgEquiv_naturality`: naturality of evaluation.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This advances Layer 4, "Cartier duality", of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConvolutionDual

universe u v w

section Map

variable (k : Type u) [Field k]
variable {H : Type v} {K : Type w}
variable [Semiring H] [Bialgebra k H]
variable [Semiring K] [Bialgebra k K]

/-- The linear dual of a bialgebra morphism, with convolution wrappers on its source and target. -/
private noncomputable def mapLinear (f : H →ₐc[k] K) :
    ConvolutionDual k K →ₗ[k] ConvolutionDual k H :=
  (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ
    f.toLinearMap.dualMap ∘ₗ (WithConv.linearEquiv k _).toLinearMap

private theorem mapLinear_apply_apply (f : H →ₐc[k] K)
    (phi : ConvolutionDual k K) (x : H) :
    (mapLinear k f phi).ofConv x = phi.ofConv (f x) :=
  rfl

/-- Precomposition by a bialgebra morphism as an algebra morphism between convolution duals. -/
private noncomputable def mapAlgHom (f : H →ₐc[k] K) :
    ConvolutionDual k K →ₐ[k] ConvolutionDual k H where
  toFun := mapLinear k f
  map_zero' := map_zero (mapLinear k f)
  map_add' := map_add (mapLinear k f)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext x
    simp [mapLinear_apply_apply]
  map_one' := by
    apply WithConv.ofConv_injective
    ext x
    simp [mapLinear_apply_apply, LinearMap.convOne_apply]
  map_mul' phi psi := by
    apply WithConv.ofConv_injective
    exact LinearMap.convMul_comp_coalgHom_distrib phi psi f.toCoalgHom

@[simp]
private theorem mapAlgHom_apply_apply (f : H →ₐc[k] K)
    (phi : ConvolutionDual k K) (x : H) :
    (mapAlgHom k f phi).ofConv x = phi.ofConv (f x) :=
  rfl

variable [Module.Finite k H] [Module.Finite k K]

private theorem dualDistribEquiv_tensor_map_apply (f : H →ₐc[k] K)
    (z : ConvolutionDual k K ⊗[k] ConvolutionDual k K) (x y : H) :
    dualDistribEquiv k H
        (Algebra.TensorProduct.map (mapAlgHom k f) (mapAlgHom k f) z) (x ⊗ₜ[k] y) =
      dualDistribEquiv k K z (f x ⊗ₜ[k] f y) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (fun a b => a + b) hz₁ hz₂
  | tmul phi psi => simp

/-- **The finite dual is contravariantly functorial.** A bialgebra morphism `H → K` induces
the bialgebra morphism `K* → H*` given by precomposition. -/
noncomputable def map (f : H →ₐc[k] K) :
    ConvolutionDual k K →ₐc[k] ConvolutionDual k H :=
  BialgHom.ofAlgHom (mapAlgHom k f)
    (by
      ext phi
      simp [mapAlgHom_apply_apply, counit_apply])
    (by
      ext phi
      apply (dualDistribEquiv k H).injective
      apply LinearMap.ext
      intro xy
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add xy₁ xy₂ hxy₁ hxy₂ =>
          simpa only [map_add, LinearMap.add_apply] using
            congrArg₂ (fun a b => a + b) hxy₁ hxy₂
      | tmul x y =>
          simp only [AlgHom.comp_apply]
          simp only [Bialgebra.comulAlgHom, AlgHom.ofLinearMap_apply]
          rw [dualDistribEquiv_tensor_map_apply,
            dualDistribEquiv_comul_apply, dualDistribEquiv_comul_apply,
            mapAlgHom_apply_apply]
          exact congrArg phi.ofConv (f.map_mul x y).symm)

/-- The dual morphism evaluates by precomposition. -/
@[simp, grind =]
theorem map_apply_apply (f : H →ₐc[k] K) (phi : ConvolutionDual k K) (x : H) :
    (map k f phi).ofConv x = phi.ofConv (f x) :=
  mapAlgHom_apply_apply k f phi x

/-- Dualizing the identity bialgebra morphism gives the identity. -/
@[simp]
theorem map_id :
    map k (BialgHom.id k H) = BialgHom.id k (ConvolutionDual k H) := by
  ext phi x
  simp

/-- Dualizing a composite reverses the order of the dual morphisms. -/
@[simp]
theorem map_comp {L : Type*} [Semiring L] [Bialgebra k L]
    [Module.Finite k L] (g : K →ₐc[k] L) (f : H →ₐc[k] K) :
    map k (g.comp f) = (map k f).comp (map k g) := by
  ext phi x
  simp

/-- A bialgebra equivalence induces a bialgebra equivalence of finite duals in the opposite
direction. -/
noncomputable def mapEquiv (e : H ≃ₐc[k] K) :
    ConvolutionDual k K ≃ₐc[k] ConvolutionDual k H :=
  BialgEquiv.ofBialgHom (map k e) (map k e.symm)
    (by rw [← map_comp, BialgEquiv.symm_comp, map_id])
    (by rw [← map_comp, BialgEquiv.comp_symm, map_id])

/-- The forward map of the dual equivalence is the dual morphism. -/
@[simp]
theorem mapEquiv_apply (e : H ≃ₐc[k] K) (phi : ConvolutionDual k K) :
    mapEquiv k e phi = map k e phi :=
  (rfl)

/-- The inverse of the dual equivalence is induced by the inverse bialgebra equivalence. -/
@[simp]
theorem mapEquiv_symm (e : H ≃ₐc[k] K) :
    (mapEquiv k e).symm = mapEquiv k e.symm := by
  apply BialgEquiv.ext
  intro phi
  apply (mapEquiv k e).injective
  calc
    mapEquiv k e ((mapEquiv k e).symm phi) = phi := BialgEquiv.apply_symm_apply _ _
    _ = mapEquiv k e (mapEquiv k e.symm phi) := by
      ext x
      simp

end Map

section Evaluation

variable (k : Type u) [Field k]
variable (H : Type v) [Semiring H] [Bialgebra k H] [Module.Finite k H]

/-- Evaluation into the double convolution dual as a linear equivalence. -/
private noncomputable def evalLinearEquiv :
    H ≃ₗ[k] ConvolutionDual k (ConvolutionDual k H) := by
  letI : Ring H := Algebra.semiringToRing k
  exact
    (Module.evalEquiv k H).trans
      ((WithConv.linearEquiv k (Module.Dual k H)).dualMap.trans
        (WithConv.linearEquiv k (Module.Dual k (ConvolutionDual k H))).symm)

private theorem evalLinearEquiv_apply_apply (x : H) (phi : ConvolutionDual k H) :
    (evalLinearEquiv k H x).ofConv phi = phi.ofConv x :=
  by
    let _ : Ring H := Algebra.semiringToRing k
    rfl

/-- Evaluation into the double finite dual as an algebra morphism. -/
private noncomputable def evalAlgHom :
    H →ₐ[k] ConvolutionDual k (ConvolutionDual k H) where
  toFun := evalLinearEquiv k H
  map_zero' := map_zero (evalLinearEquiv k H)
  map_add' := map_add (evalLinearEquiv k H)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext phi
    rw [evalLinearEquiv_apply_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    simp [Algebra.algebraMap_eq_smul_one, counit_apply]
  map_one' := by
    apply WithConv.ofConv_injective
    ext phi
    simp [evalLinearEquiv_apply_apply, counit_apply]
  map_mul' x y := by
    apply WithConv.ofConv_injective
    ext phi
    rw [evalLinearEquiv_apply_apply]
    symm
    calc
      ((evalLinearEquiv k H x) * (evalLinearEquiv k H y)).ofConv phi =
          dualDistribEquiv k H (Coalgebra.comul phi) (x ⊗ₜ[k] y) := by
        rw [LinearMap.convMul_apply]
        generalize Coalgebra.comul (R := k) phi = z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z₁ z₂ hz₁ hz₂ =>
            simpa only [map_add, LinearMap.add_apply] using
              congrArg₂ (fun a b => a + b) hz₁ hz₂
        | tmul a b => simp [evalLinearEquiv_apply_apply]
      _ = phi.ofConv (x * y) := dualDistribEquiv_comul_apply k H phi x y

@[simp]
private theorem evalAlgHom_apply_apply (x : H) (phi : ConvolutionDual k H) :
    (evalAlgHom k H x).ofConv phi = phi.ofConv x :=
  by
    let _ : Ring H := Algebra.semiringToRing k
    rfl

private theorem convMul_apply_eq_dualDistribEquiv
    (phi psi : ConvolutionDual k H) (x : H) :
    (phi * psi).ofConv x =
      dualDistribEquiv k H (phi ⊗ₜ[k] psi) (Coalgebra.comul x) := by
  rw [LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := k) x = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, LinearMap.add_apply] using
        congrArg₂ (fun a b => a + b) hz₁ hz₂
  | tmul a b => simp

private theorem dualDistribEquiv_tensor_eval_apply
    (z : H ⊗[k] H) (phi psi : ConvolutionDual k H) :
    dualDistribEquiv k (ConvolutionDual k H)
        (TensorProduct.map (evalAlgHom k H).toLinearMap
          (evalAlgHom k H).toLinearMap z)
          (phi ⊗ₜ[k] psi) =
      dualDistribEquiv k H (phi ⊗ₜ[k] psi) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, LinearMap.add_apply, WithConv.ofConv_add] using
        congrArg₂ (fun a b => a + b) hz₁ hz₂
  | tmul x y => simp [evalAlgHom_apply_apply]

/-- Evaluation into the double finite dual as a coalgebra morphism. -/
private noncomputable def evalCoalgHom :
    H →ₗc[k] ConvolutionDual k (ConvolutionDual k H) where
  __ := (evalAlgHom k H).toLinearMap
  counit_comp := by
    ext x
    simp [counit_apply, evalAlgHom_apply_apply, LinearMap.convOne_apply]
  map_comp_comul := by
    ext x
    apply (dualDistribEquiv k (ConvolutionDual k H)).injective
    apply LinearMap.ext
    intro phipsi
    induction phipsi using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ hz₁ hz₂ =>
        simpa only [map_add, LinearMap.add_apply] using
          congrArg₂ (fun a b => a + b) hz₁ hz₂
    | tmul phi psi =>
        simp only [LinearMap.comp_apply]
        calc
          _ = dualDistribEquiv k H (phi ⊗ₜ[k] psi) (Coalgebra.comul x) := by
            exact dualDistribEquiv_tensor_eval_apply k H (Coalgebra.comul x) phi psi
          _ = (phi * psi).ofConv x :=
            (convMul_apply_eq_dualDistribEquiv k H phi psi x).symm
          _ = _ := (evalAlgHom_apply_apply k H x (phi * psi)).symm.trans
            (dualDistribEquiv_comul_apply
              k (ConvolutionDual k H) (evalAlgHom k H x) phi psi).symm

/-- Evaluation into the double finite dual as a bialgebra morphism. -/
private noncomputable def evalBialgHom :
    H →ₐc[k] ConvolutionDual k (ConvolutionDual k H) :=
  { evalCoalgHom k H, evalAlgHom k H with }

/-- **A finite-dimensional bialgebra is canonically isomorphic to its double finite dual.**

The equivalence sends `x` to evaluation at `x`. -/
noncomputable def evalBialgEquiv :
    H ≃ₐc[k] ConvolutionDual k (ConvolutionDual k H) := by
  let bH : Bialgebra k H := inferInstance
  let bHH : Bialgebra k (ConvolutionDual k (ConvolutionDual k H)) := inferInstance
  -- `ofBijective` selects coalgebra structures through these bialgebra parent instances.
  -- Make the definitionally equal structures explicit to avoid the finite-dual instance diamond.
  change @BialgEquiv k _ H (ConvolutionDual k (ConvolutionDual k H)) _ _
    bH.toAlgebra bHH.toAlgebra bH.toCoalgebra.toCoalgebraStruct
      bHH.toCoalgebra.toCoalgebraStruct
  have hbij : Function.Bijective (evalBialgHom k H) := by
    change Function.Bijective (evalLinearEquiv k H)
    exact (evalLinearEquiv k H).bijective
  exact @BialgEquiv.ofBijective k H (ConvolutionDual k (ConvolutionDual k H)) _ _ _
    bH bHH (evalBialgHom k H) hbij

private theorem evalBialgEquiv_apply (x : H) :
    evalBialgEquiv k H x = evalBialgHom k H x := by
  simp only [evalBialgEquiv, id_eq, BialgEquiv.ofBijective_apply]

/-- The double-dual equivalence evaluates a functional at the original element. -/
@[simp, grind =]
theorem evalBialgEquiv_apply_apply (x : H) (phi : ConvolutionDual k H) :
    (evalBialgEquiv k H x).ofConv phi = phi.ofConv x :=
  by
    rw [evalBialgEquiv_apply]
    exact evalAlgHom_apply_apply k H x phi

/-- The inverse double-dual equivalence is characterized by evaluation. -/
@[simp, grind =]
theorem evalBialgEquiv_symm_apply_apply
    (Phi : ConvolutionDual k (ConvolutionDual k H)) (phi : ConvolutionDual k H) :
    phi.ofConv ((evalBialgEquiv k H).symm Phi) = Phi.ofConv phi := by
  rw [← evalBialgEquiv_apply_apply]
  simp

/-- Evaluation into the double dual is natural in finite-dimensional bialgebras. -/
theorem evalBialgEquiv_naturality {K : Type w} [Semiring K] [Bialgebra k K]
    [Module.Finite k K] (f : H →ₐc[k] K) :
    (evalBialgEquiv k K : K →ₐc[k] ConvolutionDual k (ConvolutionDual k K)).comp f =
      (map k (map k f)).comp (evalBialgEquiv k H) := by
  ext x phi
  simp

end Evaluation

end TauCeti.ConvolutionDual
