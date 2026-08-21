/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear

/-!
# Bilinear forms from functionals on the second symmetric and exterior powers

A functional on `Sym²V` becomes a bilinear form on `V` by composing with the universal multilinear
map, and the form it produces is symmetric because the symmetric square does not see the order of
its two arguments; a functional on `⋀²V` becomes a form in the same way, and that form is
alternating because a repeated argument wedges to zero.  Both assignments are injective: the pure
tensors span the symmetric square, and on the exterior side the passage from a functional to an
alternating map is Mathlib's universal property, an equivalence.

Nothing here is representation theory: this is the dictionary that
`TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Trichotomy` runs the invariants of the
two squares through to reach invariant forms.  The symmetric side is available over a commutative
semiring, the exterior side over a commutative ring, which is where Mathlib's exterior power lives.

## Main definitions

* `TauCeti.BilinForm.ofSymmetricSquareDual` and `TauCeti.BilinForm.ofExteriorSquareDual`: a
  functional on the second symmetric or exterior power, read as a bilinear form on `V`.

## Main results

* `TauCeti.BilinForm.isSymm_ofSymmetricSquareDual` and
  `TauCeti.BilinForm.isAlt_ofExteriorSquareDual`: the two forms are symmetric, respectively
  alternating.
* `TauCeti.BilinForm.ofSymmetricSquareDual_injective` and
  `TauCeti.BilinForm.ofExteriorSquareDual_injective`: a functional on either square is determined
  by the form it gives.

## Implementation notes

The two maps are built as plain linear maps rather than as equivalences onto the symmetric and the
alternating forms.  On the exterior side that equivalence is available: `ofExteriorSquareDual` is
`exteriorPower.alternatingMapLinearEquiv`, the universal property of the exterior power, followed
by `TauCeti.MultilinearMap.toBilinForm`, and its injectivity is the injectivity of that
equivalence.  On the symmetric side Mathlib has no universal property of the symmetric power -- it
is an explicit TODO of `Mathlib/LinearAlgebra/TensorPower/Symmetric.lean` -- so surjectivity onto
the symmetric forms is not proved here; injectivity is read off the pure tensors spanning instead,
and is all the downstream counting needs.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

variable {V : Type*}

section CommSemiring

/- `Sym[k] ι M` asks for `k` and `ι` in the same universe, so the symmetric side -- and only it --
is stated for a base ring in `Type`. -/
variable {k : Type} [CommSemiring k] [AddCommMonoid V] [Module k V]

/-- A functional on the second symmetric power of `V`, read as a bilinear form on `V`. -/
noncomputable def ofSymmetricSquareDual :
    Module.Dual k (Sym[k]^2V) →ₗ[k] BilinForm k V where
  toFun ψ :=
    MultilinearMap.toBilinForm
      (ψ.compMultilinearMap (SymmetricPower.tprod k (ι := Fin 2) (M := V)))
  map_add' ψ φ := by ext x y; simp
  map_smul' c ψ := by ext x y; simp

@[simp]
theorem ofSymmetricSquareDual_apply (ψ : Module.Dual k (Sym[k]^2V)) (x y : V) :
    ofSymmetricSquareDual ψ x y = ψ (SymmetricPower.tprod k ![x, y]) := by
  simp [ofSymmetricSquareDual]

/-- The form of a functional on the symmetric square is symmetric: the symmetric square does not
see the order of the two arguments. -/
theorem isSymm_ofSymmetricSquareDual (ψ : Module.Dual k (Sym[k]^2V)) :
    (ofSymmetricSquareDual ψ).IsSymm :=
  MultilinearMap.isSymm_toBilinForm fun x y => by
    have hswap : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by simp
    simp only [LinearMap.compMultilinearMap_apply, ← hswap]
    exact congrArg ψ (SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) ![x, y])

/-- **A functional on the symmetric square is determined by the form it gives.** The pure tensors
`tprod ![x, y]` span the symmetric square, and the values of the form are exactly the values of the
functional on those, so two functionals with the same form agree on a spanning set. -/
theorem ofSymmetricSquareDual_injective :
    Function.Injective (ofSymmetricSquareDual (k := k) (V := V)) := by
  intro ψ φ hψφ
  have h : ψ.compMultilinearMap (SymmetricPower.tprod k (ι := Fin 2) (M := V)) =
      φ.compMultilinearMap (SymmetricPower.tprod k (ι := Fin 2) (M := V)) :=
    MultilinearMap.toBilinForm_injective hψφ
  refine LinearMap.ext_on (SymmetricPower.span_tprod_eq_top k (Fin 2) V) ?_
  rintro _ ⟨f, rfl⟩
  simpa using DFunLike.congr_fun h f

end CommSemiring

section CommRing

variable {k : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- A functional on the second exterior power of `V`, read as a bilinear form on `V`.  It is the
alternating map the universal property of `⋀[k]^2 V` attaches to the functional, read as a form. -/
noncomputable def ofExteriorSquareDual :
    Module.Dual k (⋀[k]^2 V) →ₗ[k] BilinForm k V where
  toFun ψ :=
    MultilinearMap.toBilinForm
      (exteriorPower.alternatingMapLinearEquiv.symm ψ).toMultilinearMap
  map_add' ψ φ := by ext x y; simp
  map_smul' c ψ := by ext x y; simp

@[simp]
theorem ofExteriorSquareDual_apply (ψ : Module.Dual k (⋀[k]^2 V)) (x y : V) :
    ofExteriorSquareDual ψ x y = ψ (exteriorPower.ιMulti k 2 ![x, y]) := by
  simp [ofExteriorSquareDual]

/-- The form of a functional on the exterior square is alternating: a repeated argument wedges
to zero. -/
theorem isAlt_ofExteriorSquareDual (ψ : Module.Dual k (⋀[k]^2 V)) :
    (ofExteriorSquareDual ψ).IsAlt :=
  MultilinearMap.isAlt_toBilinForm fun x =>
    (exteriorPower.alternatingMapLinearEquiv.symm ψ).map_eq_zero_of_eq ![x, x]
      (i := 0) (j := 1) (by simp) (by decide)

/-- **A functional on the exterior square is determined by the form it gives.** A functional is
the alternating map the universal property attaches to it, and that map is the form. -/
theorem ofExteriorSquareDual_injective :
    Function.Injective (ofExteriorSquareDual (k := k) (V := V)) := fun _ _ hψφ =>
  exteriorPower.alternatingMapLinearEquiv.symm.injective
    (AlternatingMap.coe_multilinearMap_injective (MultilinearMap.toBilinForm_injective hψφ))

end CommRing

end BilinForm

end TauCeti
