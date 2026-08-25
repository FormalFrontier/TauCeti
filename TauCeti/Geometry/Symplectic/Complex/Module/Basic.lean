/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Almost complex structures as complex module structures

A pointwise almost complex structure `J` on a real module `V` (a real-linear endomorphism with
`J ∘ J = -1`, from `TauCeti.AlmostComplexStructure`) is the same data as a complex vector space
structure on `V` extending the real one: scalar multiplication by `a + b·i` is `a • v + b • J v`,
and conversely multiplication by `i` recovers `J`. This file makes that classical correspondence
(McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1) precise.

The forward direction `AlmostComplexStructure.complexModule` turns `J` into a `Module ℂ V`; it is
deliberately a `def`, not an instance, because the complex structure depends on the chosen `J` and
is not canonical. The backward direction `AlmostComplexStructure.ofComplexModule` reads an almost
complex structure off any complex module structure compatible with the real scalars. The round-trip
lemmas say that `ofComplexModule` applied to `complexModule J` returns `J`, and that the module
structure induced from `ofComplexModule` recovers the original complex scalar action.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexModule`: the `Module ℂ V` with
  `(a + b·i) • v = a • v + b • J v`.
* `TauCeti.AlmostComplexStructure.complexModule_smul_def`: the defining scalar action.
* `TauCeti.AlmostComplexStructure.complexModule_I_smul`: `i • v = J v` in the induced module.
* `TauCeti.AlmostComplexStructure.complexModule_ofReal_smul`: the induced action restricts to the
  original real action.
* `TauCeti.AlmostComplexStructure.complexModule_isScalarTower`: `ℝ`, `ℂ`, `V` form a scalar tower.
* `TauCeti.AlmostComplexStructure.ofComplexModule`: the almost complex structure `v ↦ i • v` on a
  complex module.
* `TauCeti.AlmostComplexStructure.ofComplexModule_complexModule`: the round trip recovers `J`.
* `TauCeti.AlmostComplexStructure.complexModule_ofComplexModule_smul`: the opposite round trip
  recovers the original complex scalar action.
-/

public section

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*}

section ToComplex

variable [AddCommGroup V] [Module ℝ V]

private lemma module_compHom_smul_def {R S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] (f : S →+* R) (s : S) (m : M) :
    letI : Module S M := Module.compHom M f
    s • m = f s • m :=
  rfl

private lemma toLinearMap_mul_toLinearMap (J : AlmostComplexStructure V) :
    J.toLinearMap * J.toLinearMap = -1 := by
  ext v
  simp [Module.End.mul_apply, J.apply_apply]

private lemma liftAux_toRingHom_apply (J : AlmostComplexStructure V)
    (hJ : J.toLinearMap * J.toLinearMap = -1) (z : ℂ) (v : V) :
    ((Complex.liftAux J.toLinearMap hJ).toRingHom z) v = z.re • v + z.im • J v := by
  exact congrArg (fun f : Module.End ℝ V => f v) (Complex.liftAux_apply J.toLinearMap hJ z)

/-- The complex vector space structure on a real module `V` induced by an almost complex
structure `J`: the scalar `a + b·i` acts as `a • v + b • J v`.

This is a `def` rather than an instance because the complex structure is not canonical: it depends
on the chosen `J`. Restricted to the real scalars it is the original `Module ℝ V`
(`complexModule_isScalarTower`, `complexModule_ofReal_smul`). -/
@[implicit_reducible]
def complexModule (J : AlmostComplexStructure V) : Module ℂ V where
  __ := Module.compHom V (Complex.liftAux J.toLinearMap J.toLinearMap_mul_toLinearMap).toRingHom

/-- The defining formula for the complex action induced by an almost complex structure. -/
@[simp]
lemma complexModule_smul_def (J : AlmostComplexStructure V) (z : ℂ) (v : V) :
    letI := J.complexModule
    z • v = z.re • v + z.im • J v :=
  by
  let := J.complexModule
  rw [module_compHom_smul_def, Module.End.smul_def]
  exact liftAux_toRingHom_apply J J.toLinearMap_mul_toLinearMap z v

/-- In the induced complex structure, multiplication by `i` is `J`. -/
lemma complexModule_I_smul (J : AlmostComplexStructure V) (v : V) :
    letI := J.complexModule
    (Complex.I) • v = J v := by
  let := J.complexModule
  rw [complexModule_smul_def, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_add]

/-- The induced complex action restricts along `ℝ → ℂ` to the original real action. -/
lemma complexModule_ofReal_smul (J : AlmostComplexStructure V) (r : ℝ) (v : V) :
    letI := J.complexModule
    (r : ℂ) • v = r • v := by
  let := J.complexModule
  rw [complexModule_smul_def, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- `ℝ`, `ℂ`, and `V` form a scalar tower for the induced complex structure: the real scalars act
the same whether through `ℝ` or through `ℂ`. -/
lemma complexModule_isScalarTower (J : AlmostComplexStructure V) :
    letI := J.complexModule
    IsScalarTower ℝ ℂ V := by
  let := J.complexModule
  refine ⟨fun a b v => ?_⟩
  rw [complexModule_smul_def, complexModule_smul_def, Complex.smul_re, Complex.smul_im]
  simp only [smul_eq_mul]
  module

end ToComplex

section OfComplex

variable [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- The almost complex structure `v ↦ i • v` on a complex module whose real scalars are compatible
with the ambient real structure. This is the inverse construction to `complexModule`. -/
@[expose]
def ofComplexModule (V : Type*) [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    AlmostComplexStructure V where
  toLinearMap := (LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ
  square_neg := by
    ext v
    simp [smul_smul, Complex.I_mul_I]

/-- The almost complex structure read from a complex module acts by multiplication by `i`. -/
@[simp]
lemma ofComplexModule_apply (v : V) : ofComplexModule V v = Complex.I • v :=
  rfl

end OfComplex

/-- Reading the almost complex structure back off the induced complex module recovers `J`. -/
@[simp]
lemma ofComplexModule_complexModule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : AlmostComplexStructure V) :
    letI := J.complexModule
    letI := J.complexModule_isScalarTower
    ofComplexModule V = J := by
  let := J.complexModule
  let := J.complexModule_isScalarTower
  refine AlmostComplexStructure.ext fun v => ?_
  rw [ofComplexModule_apply, complexModule_I_smul]

/-- Decompose a complex scalar action into its real and imaginary parts, when the real scalar
action is the one induced by the complex scalar action. -/
@[simp]
lemma re_smul_add_im_smul_I_eq_complex_smul {V : Type*}
    [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    z.re • v + z.im • (Complex.I • v) = z • v := by
  conv_rhs =>
    rw [← Complex.re_add_im z, add_smul, mul_smul]
  rw [← IsScalarTower.algebraMap_smul ℂ z.re v,
    ← IsScalarTower.algebraMap_smul ℂ z.im (Complex.I • v)]
  rw [Complex.coe_algebraMap]

/-- The complex module induced by `ofComplexModule` has the original complex scalar action. -/
lemma complexModule_ofComplexModule_smul {V : Type*}
    [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (z : ℂ) (v : V) :
    let smul₀ : ℂ → V → V := (· • ·)
    letI := (ofComplexModule V).complexModule
    z • v = smul₀ z v := by
  let smul₀ : ℂ → V → V := (· • ·)
  have ofComplexModule_smul (w : V) : ofComplexModule V w = smul₀ Complex.I w := by
    rw [ofComplexModule_apply]
  have hdecomp : z.re • v + z.im • smul₀ Complex.I v = smul₀ z v := by
    exact re_smul_add_im_smul_I_eq_complex_smul z v
  let := (ofComplexModule V).complexModule
  rw [complexModule_smul_def]
  rw [ofComplexModule_smul]
  exact hdecomp

end AlmostComplexStructure

end TauCeti
