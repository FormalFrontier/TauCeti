/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal

/-!
# Local functionals from tensor automorphisms

Let `H` be a Hopf algebra over a field `k`, and let `A` be a commutative `k`-algebra. A tensor
automorphism `η` of scalar extension on the finite-dimensional `H`-comodules acts, in particular,
on every finite subcomodule `N` of the regular comodule `H`. Applying that component to
`1 ⊗ n` and then applying the counit to the `N`-factor gives a linear functional

```text
g_{η,N} : N → A.
```

Naturality of `η` under inclusions of finite subcomodules makes these functionals compatible.
They therefore form exactly the local data needed to reconstruct one linear map `H → A` from
the directed union of the finite subcomodules. The separate directed-union construction can then
glue them; tensor and unit compatibility will supply the algebra-map laws.

## Main declarations

* `TauCeti.Tannaka.scalarExtensionComponent`: a tensor-automorphism component on an arbitrary
  finite comodule, transported to an explicit scalar-extension tensor product.
* `TauCeti.Tannaka.scalarExtensionComponent_tensor`: the elementwise tensor law for those
  transported components.
* `TauCeti.Tannaka.localFunctional`: the functional extracted from one finite subcomodule.
* `TauCeti.Tannaka.localFunctional_eq_comp_inclusion`: compatibility under inclusion.
* `TauCeti.Tannaka.localFunctional_fgPointTensorIso`: a point recovers its restriction to every
  finite subcomodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- A finite subcomodule of the regular comodule, bundled as an object of the finite comodule
category. -/
noncomputable abbrev finiteRegularObject
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    FGComoduleCat.{u, u, u} k H :=
  ⟨ComoduleCat.of k H N.1, Subcomodule.mem_finiteSubcomodules.mp N.2⟩

/-- Inclusion of finite regular subcomodules as a morphism in the finite comodule category. -/
noncomputable def regularInclusion
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) :
    finiteRegularObject k H N ⟶ finiteRegularObject k H Q := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  letI : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  refine FGComoduleCat.ofHom (R := k) (C := H)
    { toLinearMap := Submodule.inclusion hNQ
      map_coact := ?_ }
  apply LinearMap.ext
  intro n
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (SMulMemClass.subtype Q.1) Subtype.val_injective
  have hcomp : (SMulMemClass.subtype Q.1).comp (Submodule.inclusion hNQ) =
      SMulMemClass.subtype N.1 := by
    ext
    rfl
  calc
    (SMulMemClass.subtype Q.1).rTensor H
        (TensorProduct.map (Submodule.inclusion hNQ) LinearMap.id
          (Comodule.coact (R := k) (C := H) (M := N.1) n)) =
        (SMulMemClass.subtype N.1).rTensor H
          (Comodule.coact (R := k) (C := H) (M := N.1) n) := by
      rw [LinearMap.rTensor_def, LinearMap.rTensor_def, TensorProduct.map_map,
        LinearMap.comp_id, hcomp]
    _ = Comodule.coact (R := k) (C := H) (M := H) n :=
      Subcomodule.subtype_rTensor_coact N.1 n
    _ = (SMulMemClass.subtype Q.1).rTensor H
        (Comodule.coact (R := k) (C := H) (M := Q.1)
          (Submodule.inclusion hNQ n)) :=
      (Subcomodule.subtype_rTensor_coact Q.1 (Submodule.inclusion hNQ n)).symm

/-- The inclusion of finite regular subcomodules is the ordinary subtype inclusion. -/
@[simp]
theorem regularInclusion_apply
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) (n : N.1) :
    regularInclusion k H hNQ n = ⟨n, hNQ n.2⟩ :=
  by
    unfold regularInclusion
    rfl

/-- The linear map underlying inclusion of finite regular subcomodules is the ordinary submodule
inclusion. -/
@[simp]
theorem regularInclusion_toLinearMap
    {N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)}
    (hNQ : N.1 ≤ Q.1) :
    (regularInclusion k H hNQ).hom.toLinearMap = Submodule.inclusion hNQ := by
  unfold regularInclusion
  rfl

/-- The component of a tensor automorphism, transported from the object chosen by the
scalar-extension functor to the explicit tensor product `A ⊗[k] M`. -/
noncomputable def scalarExtensionComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (M : FGComoduleCat.{u, u, u} k H) :
    A ⊗[k] M →ₗ[A] A ⊗[k] M := by
  exact (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
      M).symm ≫
    η.hom.hom.app M ≫
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
        M)).hom

/-- Naturality of the explicitly transported components of a tensor automorphism. -/
theorem scalarExtensionComponent_natural
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    {M N : FGComoduleCat.{u, u, u} k H} (f : M ⟶ N) :
    f.hom.toLinearMap.baseChange A ∘ₗ scalarExtensionComponent k H A η M =
      scalarExtensionComponent k H A η N ∘ₗ f.hom.toLinearMap.baseChange A := by
  let aM : (FGComoduleCat.scalarExtensionFunctor k H A).obj M ⟶
      (FGComoduleCat.scalarExtensionFunctor k H A).obj M :=
    η.hom.hom.app M
  let aN : (FGComoduleCat.scalarExtensionFunctor k H A).obj N ⟶
      (FGComoduleCat.scalarExtensionFunctor k H A).obj N :=
    η.hom.hom.app N
  have hnat :
      (FGComoduleCat.scalarExtensionFunctor k H A).map f ≫ aN =
        aM ≫ (FGComoduleCat.scalarExtensionFunctor k H A).map f :=
    η.hom.hom.naturality f
  let hM := FGComoduleCat.scalarExtensionFunctor_obj k H A M
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A N
  let iM := eqToIso hM
  let iN := eqToIso hN
  let bmap := SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A)
  have hfmap :
      (FGComoduleCat.scalarExtensionFunctor k H A).map f =
        iM.hom ≫ bmap ≫ iN.inv := by
    simpa only [hM, hN, iM, iN, bmap, eqToIso.hom, eqToIso.inv] using
      FGComoduleCat.scalarExtensionFunctor_map k H A f
  rw [hfmap] at hnat
  have hcat :
      (iM.inv ≫ aM ≫ iM.hom) ≫ bmap =
        bmap ≫ (iN.inv ≫ aN ≫ iN.hom) := by
    rw [← cancel_epi iM.hom]
    rw [← cancel_mono iN.inv]
    slice_lhs 1 2 => rw [iM.hom_inv_id]
    slice_rhs 4 6 => rw [iN.hom_inv_id, Category.comp_id]
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hnat.symm
  change bmap.hom ∘ₗ
      (iM.inv ≫ aM ≫ iM.hom).hom =
    (iN.inv ≫ aN ≫ iN.hom).hom ∘ₗ bmap.hom
  simpa only [SemimoduleCat.hom_comp] using congrArg SemimoduleCat.Hom.hom hcat

/-- Tensor compatibility of the explicitly transported components of a tensor automorphism. -/
theorem scalarExtensionComponent_tensor
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (M N : FGComoduleCat.{u, u, u} k H) (x : A ⊗[k] M) (y : A ⊗[k] N) :
    scalarExtensionComponent k H A η (M ⊗ N : FGComoduleCat k H)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange k A M N).symm
          (x ⊗ₜ[A] y)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange k A M N).symm
        (scalarExtensionComponent k H A η M x ⊗ₜ[A]
          scalarExtensionComponent k H A η N y) := by
  let aM : (FGComoduleCat.scalarExtensionFunctor k H A).obj M ⟶
      (FGComoduleCat.scalarExtensionFunctor k H A).obj M :=
    η.hom.hom.app M
  let aN : (FGComoduleCat.scalarExtensionFunctor k H A).obj N ⟶
      (FGComoduleCat.scalarExtensionFunctor k H A).obj N :=
    η.hom.hom.app N
  let aMN : (FGComoduleCat.scalarExtensionFunctor k H A).obj
      (M ⊗ N : FGComoduleCat k H) ⟶
      (FGComoduleCat.scalarExtensionFunctor k H A).obj
        (M ⊗ N : FGComoduleCat k H) :=
    η.hom.hom.app (M ⊗ N : FGComoduleCat k H)
  have htensor := NatTrans.IsMonoidal.tensor (τ := η.hom.hom) M N
  change Functor.LaxMonoidal.μ (FGComoduleCat.scalarExtensionFunctor k H A) M N ≫ aMN =
    (aM ⊗ₘ aN) ≫
      Functor.LaxMonoidal.μ (FGComoduleCat.scalarExtensionFunctor k H A) M N at htensor
  rw [FGComoduleCat.scalarExtensionFunctor_μ] at htensor
  let iM := eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H A M)
  let iN := eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H A N)
  let iMN := eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H A
    (M ⊗ N : FGComoduleCat k H))
  let d :
      (SemimoduleCat.of A (A ⊗[k] M) ⊗ SemimoduleCat.of A (A ⊗[k] N)) ⟶
        SemimoduleCat.of A (A ⊗[k] (M ⊗[k] N)) :=
    SemimoduleCat.ofHom
      (TensorProduct.AlgebraTensorModule.distribBaseChange k A M N).symm.toLinearMap
  have hmon :
      (((iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv) ≫ aMN) =
        (aM ⊗ₘ aN) ≫ ((iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv) := by
    simpa only [iM, iN, iMN, d, eqToIso.hom, eqToIso.inv] using htensor
  have he :
      (iM.hom ⊗ₘ iN.hom) ≫
          ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)) =
        ((aM ≫ iM.hom) ⊗ₘ (aN ≫ iN.hom)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id_assoc]
  have he' :
      (aM ⊗ₘ aN) ≫ (iM.hom ⊗ₘ iN.hom) =
        ((aM ≫ iM.hom) ⊗ₘ (aN ≫ iN.hom)) :=
    MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  have hcat :
      d ≫ (iMN.inv ≫ aMN ≫ iMN.hom) =
        ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)) ≫ d := by
    rw [← cancel_epi (iM.hom ⊗ₘ iN.hom)]
    rw [← cancel_mono iMN.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    conv_rhs => rw [← Category.assoc]
    rw [he, ← he']
    simpa only [Category.assoc] using hmon
  have hlin := congrArg SemimoduleCat.Hom.hom hcat
  change (iMN.inv ≫ aMN ≫ iMN.hom).hom.comp d.hom =
      d.hom.comp
        ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)).hom at hlin
  rw [SemimoduleCat.hom_tensorHom] at hlin
  have happ := LinearMap.congr_fun hlin (x ⊗ₜ[A] y)
  change (iMN.inv ≫ aMN ≫ iMN.hom).hom (d.hom (x ⊗ₜ[A] y)) =
      d.hom (TensorProduct.map
        (iM.inv ≫ aM ≫ iM.hom).hom
        (iN.inv ≫ aN ≫ iN.hom).hom (x ⊗ₜ[A] y)) at happ
  rw [TensorProduct.map_tmul] at happ
  change scalarExtensionComponent k H A η (M ⊗ N : FGComoduleCat k H)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange k A M N).symm
        (x ⊗ₜ[A] y)) =
    (TensorProduct.AlgebraTensorModule.distribBaseChange k A M N).symm
      (scalarExtensionComponent k H A η M x ⊗ₜ[A]
        scalarExtensionComponent k H A η N y) at happ
  exact happ

/-- The component of a tensor automorphism on a finite regular subcomodule, transported from the
object chosen by the scalar-extension functor to the explicit tensor product `A ⊗[k] N`. -/
@[expose] noncomputable def finiteRegularComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    A ⊗[k] N.1 →ₗ[A] A ⊗[k] N.1 :=
  scalarExtensionComponent k H A η (finiteRegularObject k H N)

/-- Evaluation formula for the transported component of a tensor automorphism on a finite
regular subcomodule. -/
theorem finiteRegularComponent_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (x : A ⊗[k] N.1) :
    finiteRegularComponent k H A η N x =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
          (finiteRegularObject k H N))
        (η.hom.hom.app (finiteRegularObject k H N)
          (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
            (finiteRegularObject k H N)).symm x)) := by
  unfold finiteRegularComponent
  rfl

/-- Naturality of a tensor automorphism on an inclusion of finite regular subcomodules. -/
theorem finiteRegularComponent_natural
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hNQ : N.1 ≤ Q.1) :
    (Submodule.inclusion hNQ).baseChange A ∘ₗ finiteRegularComponent k H A η N =
      finiteRegularComponent k H A η Q ∘ₗ (Submodule.inclusion hNQ).baseChange A := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  let _ : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  simpa only [finiteRegularComponent, regularInclusion_toLinearMap] using
    scalarExtensionComponent_natural k H A η (regularInclusion k H hNQ)

/-- The linear functional on a finite subcomodule of the regular comodule extracted from a
tensor automorphism. It applies the automorphism to `1 ⊗ n` and then evaluates the regular
coordinate by the counit. -/
noncomputable def localFunctional
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    N.1 →ₗ[k] A := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  exact ((TauCeti.Module.Dual.baseChangeEvaluation (R := k) (M := N.1) (A := A)
    (1 ⊗ₜ[k] ((Coalgebra.counit (R := k) (A := H)).comp
      (SMulMemClass.subtype N.1)))).restrictScalars k).comp <|
    ((finiteRegularComponent k H A η N).restrictScalars k).comp
      (TensorProduct.mk k A N.1 (1 : A))

/-- Evaluation formula for the functional extracted from a finite regular subcomodule. -/
@[simp]
theorem localFunctional_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A η N n =
      TauCeti.Module.Dual.baseChangeEvaluation (R := k) (M := N.1) (A := A)
        (1 ⊗ₜ[k] ((Coalgebra.counit (R := k) (A := H)).comp
          (SMulMemClass.subtype N.1)))
        (finiteRegularComponent k H A η N (1 ⊗ₜ[k] n)) :=
  by
    unfold localFunctional
    rfl

/-- The local functionals extracted from a tensor automorphism agree under inclusion of finite
subcomodules. -/
theorem localFunctional_eq_comp_inclusion
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hNQ : N.1 ≤ Q.1) :
    localFunctional k H A η N =
      (localFunctional k H A η Q).comp (Submodule.inclusion hNQ) := by
  apply LinearMap.ext
  intro n
  rw [LinearMap.comp_apply, localFunctional_apply, localFunctional_apply]
  have happ := LinearMap.congr_fun (finiteRegularComponent_natural k H A η N Q hNQ)
    (1 ⊗ₜ[k] n)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at happ
  rw [← happ]
  induction finiteRegularComponent k H A η N (1 ⊗ₜ[k] n) using
    TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a m =>
      simp only [LinearMap.baseChange_tmul,
        TauCeti.Module.Dual.baseChangeEvaluation_tmul, LinearMap.comp_apply,
        SMulMemClass.subtype_apply, one_mul]
      rfl

/-- The finite regular component of the tensor automorphism induced by a point is the usual
point action on that finite subcomodule. -/
@[simp]
theorem finiteRegularComponent_fgPointTensorIso
    (g : WithConv (H →ₐ[k] A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    finiteRegularComponent k H A (fgPointTensorIso k H A g) N =
      (Comodule.pointsAction N.1 g).toLinearMap := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  apply LinearMap.ext
  intro x
  unfold finiteRegularComponent scalarExtensionComponent
  rw [fgPointTensorIso_hom_hom, fgPointNatIsoHom_hom_app]
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H N)
  -- After rewriting the point-induced component, the only remaining wrappers are the
  -- transports along `hN`.  There is no carrier-level rewrite theorem for this object
  -- equality; displaying the four `eqToHom`s lets the category simp lemmas cancel them.
  change (eqToHom hN.symm ≫
      (eqToHom hN ≫ (Comodule.pointsAction N.1 g).toModuleIsoₛ.hom ≫
        eqToHom hN.symm) ≫ eqToHom hN) x = _
  simp

/-- For a tensor automorphism induced by an algebra-valued point `g`, the local functional is
the restriction of `g` to the chosen finite subcomodule of the regular comodule. -/
@[simp]
theorem localFunctional_fgPointTensorIso
    (g : WithConv (H →ₐ[k] A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A (fgPointTensorIso k H A g) N n = g.ofConv n := by
  rw [← fgPointTensorIsoHom_apply]
  rw [localFunctional_apply, fgPointTensorIsoHom_apply,
    finiteRegularComponent_fgPointTensorIso]
  rw [Comodule.pointsAction_toLinearMap]
  let φ : Module.Dual k N.1 :=
    (Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N.1)
  have hcoeff : Comodule.matrixCoefficient (R := k) (C := H) φ n = (n : H) := by
    simpa only [φ] using Comodule.matrixCoefficient_counit_comp_subtype
      (R := k) (C := H) N.1 n
  simpa only [φ, one_mul, hcoeff] using
    Comodule.baseChangeEvaluation_endOfPoint_tmul g.ofConv (1 : A) (1 : A) φ n

end TauCeti.Tannaka
