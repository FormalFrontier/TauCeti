/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear

/-!
# Bilinear forms from functionals on the second symmetric and exterior powers

A functional on `Sym²V` becomes a bilinear form on `V` by composing with the universal multilinear
map, and the form it produces is symmetric because the symmetric square does not see the order of
its two arguments; a functional on `⋀²V` becomes an alternating form the same way.  Both
assignments are injective, because the pure tensors span their square.

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
alternating forms: their images are not all of those subspaces in general, and identifying them
would need the universal property of the symmetric square, which is not in Mathlib.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

variable {k : Type} {V : Type*}

section CommSemiring

variable [CommSemiring k] [AddCommMonoid V] [Module k V]

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
    (ofSymmetricSquareDual ψ).IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hswap : (fun i => ![x, y] (Equiv.swap 0 1 i)) = ![y, x] := by
    funext i; fin_cases i <;> simp
  simp only [ofSymmetricSquareDual_apply]
  rw [← SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) ![x, y], hswap]

/-- **A functional on the symmetric square is determined by the form it gives.** The pure tensors
`tprod ![x, y]` span the symmetric square, and the values of the form are exactly the values of the
functional on those, so two functionals with the same form agree on a spanning set. -/
theorem ofSymmetricSquareDual_injective :
    Function.Injective (ofSymmetricSquareDual (k := k) (V := V)) := by
  intro ψ φ hψφ
  refine LinearMap.ext_on (SymmetricPower.span_tprod_eq_top k (Fin 2) V) ?_
  rintro _ ⟨f, rfl⟩
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
  have := congrArg (fun B : BilinForm k V => B (f 0) (f 1)) hψφ
  simpa [hf.symm] using this

end CommSemiring

section CommRing

variable [CommRing k] [AddCommGroup V] [Module k V]

/-- A functional on the second exterior power of `V`, read as a bilinear form on `V`. -/
noncomputable def ofExteriorSquareDual :
    Module.Dual k (⋀[k]^2 V) →ₗ[k] BilinForm k V where
  toFun ψ :=
    MultilinearMap.toBilinForm
      (ψ.compMultilinearMap (exteriorPower.ιMulti k 2 (M := V)).toMultilinearMap)
  map_add' ψ φ := by ext x y; simp
  map_smul' c ψ := by ext x y; simp

@[simp]
theorem ofExteriorSquareDual_apply (ψ : Module.Dual k (⋀[k]^2 V)) (x y : V) :
    ofExteriorSquareDual ψ x y = ψ (exteriorPower.ιMulti k 2 ![x, y]) := by
  simp [ofExteriorSquareDual]

/-- The form of a functional on the exterior square is alternating: a repeated argument wedges
to zero. -/
theorem isAlt_ofExteriorSquareDual (ψ : Module.Dual k (⋀[k]^2 V)) :
    (ofExteriorSquareDual ψ).IsAlt := by
  intro x
  have hzero : exteriorPower.ιMulti k 2 ![x, x] = 0 :=
    (exteriorPower.ιMulti k 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) (by simp) (by decide)
  simp [hzero]

/-- **A functional on the exterior square is determined by the form it gives.** The wedges
`ιMulti ![x, y]` span the exterior square, and the values of the form are exactly the values of the
functional on those, so two functionals with the same form agree on a spanning set. -/
theorem ofExteriorSquareDual_injective :
    Function.Injective (ofExteriorSquareDual (k := k) (V := V)) := by
  intro ψ φ hψφ
  refine LinearMap.ext_on (exteriorPower.ιMulti_span k 2 V) ?_
  rintro _ ⟨f, rfl⟩
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
  have := congrArg (fun B : BilinForm k V => B (f 0) (f 1)) hψφ
  simpa [hf.symm] using this

end CommRing

end BilinForm

end TauCeti
