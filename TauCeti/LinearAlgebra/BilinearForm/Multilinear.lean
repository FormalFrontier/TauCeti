/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Bilinear forms read off multilinear maps in two variables

A multilinear map on the constant family `fun _ : Fin 2 => V` and a bilinear form on `V` carry the
same data.  This file records the direction that is used downstream:
`TauCeti.MultilinearMap.toBilinForm` reads a multilinear map `m` as the bilinear form
`(x, y) ↦ m ![x, y]`, and two recognition lemmas say when that form is symmetric or alternating.

The point of the construction is that the maps out of a second symmetric or exterior power are
multilinear in exactly this sense, so a functional on `Sym²V` or on `⋀²V` becomes a bilinear form
on `V` by composing with the universal multilinear map.  That is what
`TauCeti/LinearAlgebra/BilinearForm/Squares.lean` builds on this file.

## Main definitions

* `TauCeti.MultilinearMap.toBilinForm`: the bilinear form `(x, y) ↦ m ![x, y]` of a multilinear
  map `m` in two variables.

## Main results

* `TauCeti.MultilinearMap.isSymm_toBilinForm`: the form is symmetric when `m` is unchanged by
  swapping its two arguments.
* `TauCeti.MultilinearMap.isAlt_toBilinForm`: the form is alternating when `m` vanishes on a
  repeated argument.

## Implementation notes

Bilinearity is read off `MultilinearMap.map_update_add` and `MultilinearMap.map_update_smul` at the
two indices of `Fin 2`, which is why the two private lemmas identifying `Function.update` on a
two-element vector come first: they are what turn an update at `0` or at `1` back into the
`![·, ·]` notation the statements are phrased in.  Feeding those four facts to `LinearMap.mk₂`
keeps the four linearity goals stated in that notation, so none of them has to be massaged into
the nested form a bare `LinearMap` constructor would present.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace MultilinearMap

private theorem update_two_zero {V : Type*} (x y z : V) :
    Function.update ![z, y] 0 x = ![x, y] := by
  funext i
  fin_cases i <;> simp

private theorem update_two_one {V : Type*} (x y z : V) :
    Function.update ![x, z] 1 y = ![x, y] := by
  funext i
  fin_cases i <;> simp

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The bilinear form `(x, y) ↦ m ![x, y]` of a multilinear map `m` in two variables. -/
def toBilinForm (m : MultilinearMap R (fun _ : Fin 2 => V) R) : BilinForm R V :=
  LinearMap.mk₂ R (fun x y => m ![x, y])
    (fun x x' y => by simpa only [update_two_zero] using m.map_update_add ![x, y] 0 x x')
    (fun c x y => by simpa only [update_two_zero] using m.map_update_smul ![x, y] 0 c x)
    (fun x y y' => by simpa only [update_two_one] using m.map_update_add ![x, y] 1 y y')
    (fun c x y => by simpa only [update_two_one] using m.map_update_smul ![x, y] 1 c y)

@[simp]
theorem toBilinForm_apply (m : MultilinearMap R (fun _ : Fin 2 => V) R) (x y : V) :
    toBilinForm m x y = m ![x, y] :=
  (rfl)

/-- The form of a multilinear map that is unchanged by swapping its two arguments is symmetric. -/
theorem isSymm_toBilinForm {m : MultilinearMap R (fun _ : Fin 2 => V) R}
    (h : ∀ x y : V, m ![y, x] = m ![x, y]) : (toBilinForm m).IsSymm :=
  ⟨fun x y => (h x y).symm⟩

/-- The form of a multilinear map that vanishes on a repeated argument is alternating. -/
theorem isAlt_toBilinForm {m : MultilinearMap R (fun _ : Fin 2 => V) R}
    (h : ∀ x : V, m ![x, x] = 0) : (toBilinForm m).IsAlt :=
  h

end MultilinearMap

end TauCeti
