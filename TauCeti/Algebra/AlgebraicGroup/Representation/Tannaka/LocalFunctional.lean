/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

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

* `TauCeti.Tannaka.localFunctional`: the functional extracted from one finite subcomodule.
* `TauCeti.Tannaka.localFunctional_mono`: compatibility under inclusion.
* `TauCeti.Tannaka.localFunctional_fgPointTensorIso`: a point recovers its restriction to every
  finite subcomodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory
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

/-- Apply the coalgebra counit to the second factor of a scalar-extended finite regular
subcomodule. -/
noncomputable def counitEvaluation
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    A ⊗[k] N.1 →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp <|
    TensorProduct.map LinearMap.id
      ((Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N.1))

/-- Evaluation by the counit on a pure tensor. -/
@[simp]
theorem counitEvaluation_tmul
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (a : A) (n : N.1) :
    counitEvaluation k H A N (a ⊗ₜ[k] n) =
      Coalgebra.counit (R := k) (n : H) • a := by
  simp [counitEvaluation]

/-- The component of a tensor automorphism on a finite regular subcomodule, transported from the
object chosen by the scalar-extension functor to the explicit tensor product `A ⊗[k] N`. -/
noncomputable def finiteRegularComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    A ⊗[k] N.1 →ₗ[A] A ⊗[k] N.1 := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  exact (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
      (finiteRegularObject k H N)).symm ≫
    η.hom.hom.app (finiteRegularObject k H N) ≫
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
        (finiteRegularObject k H N))).hom

/-- Naturality of a tensor automorphism on an inclusion of finite regular subcomodules. -/
theorem finiteRegularComponent_natural
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hNQ : N.1 ≤ Q.1) :
    (Submodule.inclusion hNQ).baseChange A ∘ₗ finiteRegularComponent k H A η N =
      finiteRegularComponent k H A η Q ∘ₗ (Submodule.inclusion hNQ).baseChange A := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  let _ : Module.Finite k Q.1 := Subcomodule.mem_finiteSubcomodules.mp Q.2
  let aN : (FGComoduleCat.scalarExtensionFunctor k H A).obj
      (finiteRegularObject k H N) ⟶
        (FGComoduleCat.scalarExtensionFunctor k H A).obj (finiteRegularObject k H N) :=
    η.hom.hom.app (finiteRegularObject k H N)
  let aQ : (FGComoduleCat.scalarExtensionFunctor k H A).obj
      (finiteRegularObject k H Q) ⟶
        (FGComoduleCat.scalarExtensionFunctor k H A).obj (finiteRegularObject k H Q) :=
    η.hom.hom.app (finiteRegularObject k H Q)
  have hnat := η.hom.hom.naturality (regularInclusion k H hNQ)
  change (FGComoduleCat.scalarExtensionFunctor k H A).map (regularInclusion k H hNQ) ≫
      aQ =
    aN ≫
      (FGComoduleCat.scalarExtensionFunctor k H A).map (regularInclusion k H hNQ) at hnat
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H N)
  let hQ := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H Q)
  let iN := eqToIso hN
  let iQ := eqToIso hQ
  let bmap := SemimoduleCat.ofHom ((Submodule.inclusion hNQ).baseChange A)
  have hfmap :
      (FGComoduleCat.scalarExtensionFunctor k H A).map (regularInclusion k H hNQ) =
        iN.hom ≫ bmap ≫ iQ.inv := by
    simpa only [hN, hQ, iN, iQ, bmap, eqToIso.hom, eqToIso.inv,
      regularInclusion_toLinearMap] using
      FGComoduleCat.scalarExtensionFunctor_map k H A (regularInclusion k H hNQ)
  rw [hfmap] at hnat
  have hcat :
      (iN.inv ≫ aN ≫ iN.hom) ≫ bmap =
        bmap ≫ (iQ.inv ≫ aQ ≫ iQ.hom) := by
    rw [← cancel_epi iN.hom]
    rw [← cancel_mono iQ.inv]
    slice_lhs 1 2 => rw [iN.hom_inv_id]
    slice_rhs 4 6 => rw [iQ.hom_inv_id, Category.comp_id]
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hnat.symm
  change bmap.hom ∘ₗ
      (iN.inv ≫ aN ≫ iN.hom).hom =
    (iQ.inv ≫ aQ ≫ iQ.hom).hom ∘ₗ bmap.hom
  simpa only [SemimoduleCat.hom_comp] using congrArg SemimoduleCat.Hom.hom hcat

/-- Applying the counit after scalar-extending an inclusion of finite regular subcomodules does
not depend on the chosen ambient subcomodule. -/
theorem counitEvaluation_baseChange
    (N Q : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hNQ : N.1 ≤ Q.1) (x : A ⊗[k] N.1) :
    counitEvaluation k H A Q ((Submodule.inclusion hNQ).baseChange A x) =
      counitEvaluation k H A N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a n => simp [counitEvaluation]

/-- Counit evaluation is scalar-extended evaluation against the restriction of the counit. -/
theorem counitEvaluation_eq_baseChangeEvaluation
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (x : A ⊗[k] N.1) :
    counitEvaluation k H A N x =
      TauCeti.Module.Dual.baseChangeEvaluation (R := k) (M := N.1) (A := A)
        (1 ⊗ₜ[k] ((Coalgebra.counit (R := k) (A := H)).comp
          (SMulMemClass.subtype N.1))) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a n =>
      simp only [counitEvaluation_tmul,
        TauCeti.Module.Dual.baseChangeEvaluation_tmul, LinearMap.comp_apply,
        SMulMemClass.subtype_apply, one_mul]
      rw [Algebra.smul_def, mul_comm]

/-- The linear functional on a finite subcomodule of the regular comodule extracted from a
tensor automorphism. It applies the automorphism to `1 ⊗ n` and then evaluates the regular
coordinate by the counit. -/
noncomputable def localFunctional
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    N.1 →ₗ[k] A := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  exact (counitEvaluation k H A N).comp <|
    ((finiteRegularComponent k H A η N).restrictScalars k).comp
      (TensorProduct.mk k A N.1 (1 : A))

/-- Evaluation formula for the functional extracted from a finite regular subcomodule. -/
theorem localFunctional_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A η N n =
      counitEvaluation k H A N
        (finiteRegularComponent k H A η N (1 ⊗ₜ[k] n)) :=
  by
    unfold localFunctional
    rfl

/-- The local functionals extracted from a tensor automorphism agree under inclusion of finite
subcomodules. -/
theorem localFunctional_mono
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
  rw [← counitEvaluation_baseChange k H A N Q hNQ, happ]

/-- The finite regular component of the tensor automorphism induced by a point is the usual
point action on that finite subcomodule. -/
theorem finiteRegularComponent_fgPointTensorIso
    (g : WithConv (H →ₐ[k] A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) :
    finiteRegularComponent k H A (fgPointTensorIsoHom k H A g) N =
      (Comodule.pointsAction N.1 g).toLinearMap := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  apply LinearMap.ext
  intro x
  unfold finiteRegularComponent
  rw [fgPointTensorIsoHom_apply, fgPointTensorIso_hom_hom,
    fgPointNatIsoHom_hom_app]
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H N)
  change (eqToHom hN.symm ≫
      (eqToHom hN ≫ (Comodule.pointsAction N.1 g).toModuleIsoₛ.hom ≫
        eqToHom hN.symm) ≫ eqToHom hN) x = _
  simp

/-- For a tensor automorphism induced by an algebra-valued point `g`, the local functional is
the restriction of `g` to the chosen finite subcomodule of the regular comodule. -/
theorem localFunctional_fgPointTensorIso
    (g : WithConv (H →ₐ[k] A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H)) (n : N.1) :
    localFunctional k H A (fgPointTensorIsoHom k H A g) N n = g.ofConv n := by
  rw [localFunctional_apply, finiteRegularComponent_fgPointTensorIso]
  rw [Comodule.pointsAction_toLinearMap]
  rw [counitEvaluation_eq_baseChangeEvaluation]
  let φ : Module.Dual k N.1 :=
    (Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N.1)
  have hcoeff : Comodule.matrixCoefficient (R := k) (C := H) φ n = (n : H) := by
    have hφ : φ = (Coalgebra.counit (R := k) (A := H)).comp
        (Subcomodule.subtype N.1).toLinearMap := by
      unfold φ
      rw [Subcomodule.subtype_toLinearMap]
    rw [hφ]
    rw [← Comodule.matrixCoefficient_map (Subcomodule.subtype N.1)
      (Coalgebra.counit (R := k) (A := H)) n]
    simp
  simpa only [φ, one_mul, hcoeff] using
    Comodule.baseChangeEvaluation_endOfPoint_tmul g.ofConv (1 : A) (1 : A) φ n

end TauCeti.Tannaka
