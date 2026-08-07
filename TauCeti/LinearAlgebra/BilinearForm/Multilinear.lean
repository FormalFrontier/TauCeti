/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
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
* `TauCeti.MultilinearMap.toBilinForm_injective`: the other half of "the same data" -- the form
  determines the multilinear map.

## Implementation notes

Bilinearity is Mathlib's `MultilinearMap.cons_add` and `cons_smul` at the first argument and
`MultilinearMap.snoc_add` and `snoc_smul` at the second, since `![x, y]` is both `Fin.cons x ![y]`
and `Fin.snoc ![x] y`.  Feeding those four facts to `LinearMap.mk₂` keeps the four linearity goals
stated in the `![·, ·]` notation, so none of them has to be massaged into the nested form a bare
`LinearMap` constructor would present.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace MultilinearMap

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The bilinear form `(x, y) ↦ m ![x, y]` of a multilinear map `m` in two variables. -/
def toBilinForm (m : MultilinearMap R (fun _ : Fin 2 => V) R) : BilinForm R V :=
  LinearMap.mk₂ R (fun x y => m ![x, y])
    (fun x x' y => m.cons_add ![y] x x')
    (fun c x y => m.cons_smul ![y] c x)
    (fun x y y' => by simpa using m.snoc_add ![x] y y')
    (fun c x y => by simpa using m.snoc_smul ![x] c y)

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
  fun x => (toBilinForm_apply m x x).trans (h x)

/-- **A multilinear map in two variables is determined by its bilinear form.**  Every argument of
`m` is a `![x, y]`, and the form records the value of `m` there. -/
theorem toBilinForm_injective : Function.Injective (toBilinForm (R := R) (V := V)) := by
  intro m n h
  ext f
  have hf : f = ![f 0, f 1] := (FinVec.etaExpand_eq f).symm
  have := congrArg (fun B : BilinForm R V => B (f 0) (f 1)) h
  simpa [hf.symm] using this

end MultilinearMap

end TauCeti
