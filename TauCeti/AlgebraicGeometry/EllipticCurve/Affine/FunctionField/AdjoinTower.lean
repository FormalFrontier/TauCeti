/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.FieldTheory.IntermediateField.ExtendRight

/-!
# The tower `K⟮g⟯ ⊆ K(x) ⊆ K(W)` over an arbitrary generator

For a rational function `g`, the subfield `K⟮g⟯` of `K(x)` has a copy inside the function field
`K(W)` of a Weierstrass curve. This file computes the two degrees of the resulting tower in terms
of the single input `[K(x) : K⟮g⟯]`: the inner storey contributes that degree, the outer storey
contributes two, and an embedding of function fields carrying the affine coordinate to `g` has
image of index exactly `[K(x) : K⟮g⟯]`.

Everything here is generator-agnostic. A caller supplies `g` together with a theorem computing
`Module.finrank K⟮g⟯ (RatFunc K)`, and gets the whole tower back; `PowerTower.lean` does this for
`g = X ^ n`, where that degree is `n`.

The copy of `K⟮g⟯` inside `K(W)` is Mathlib's `IntermediateField.extendRight`, written
`(IntermediateField.adjoin K {g}).extendRight W.FunctionField`; this file adds the degree lemmas
for it in this tower and no new object. Its membership and order API is generic and lives in
`TauCeti.FieldTheory.IntermediateField.ExtendRight`.

## Main results

* `WeierstrassCurve.Affine.relfinrank_extendRight`: `[K(x) : F]`, read inside `K(W)`.
* `WeierstrassCurve.Affine.finrank_extendRight`: `[K(W) : F] = 2 · [K(x) : F]`.
* `WeierstrassCurve.Affine.extendRight_adjoin_eq_map_ratFuncRange` and
  `WeierstrassCurve.Affine.finrank_fieldRange_of_apply_X_eq`: for any embedding
  `f : K(W') → K(W)` of function fields sending the affine coordinate of `W'` to `g`, the copy of
  `K⟮g⟯` is the image of `K(x')`, and `[K(W) : f(K(W'))] = [K(x) : K⟮g⟯]`.

No result needs `W` to be elliptic: the Weierstrass equation alone gives the power basis, through
`finrank_ratFuncRange`.

The Frobenius degree computation is a specialisation of this tower, through `PowerTower.lean`.

## Provenance

The argument, naming scheme and proof shapes are `Affine/FunctionField/PowerTower.lean`'s, stated
here for an arbitrary generator instead of `X ^ n`. The finite-field ancestor of both is the AINTLIB
`HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned at
`513e83879e2f8cbc626eb9e04d660e92be16ccba`), `HasseWeil/FrobeniusIsogeny.lean`, private
declarations `frobFracRange`, `frobFracRange_le_frobRange`, `finrank_frobFracRange_functionField`
and `finrank_over_frobenius_image`, where the exponent is the cardinality of a finite field.
-/

public section

open Polynomial IntermediateField

open scoped RatFunc

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

/-- Any subfield of `K(x)` sits inside `K(x)`, both read inside `K(W)`. -/
theorem extendRight_le_ratFuncRange (F : IntermediateField K (RatFunc K)) :
    F.extendRight W.FunctionField ≤ ratFuncRange W := by
  rw [ratFuncRange_eq_map, IntermediateField.extendRight_eq_map]
  exact IntermediateField.map_mono _ le_top

/-- **`[K(x) : F]`, read inside `K(W)`**, is the degree it has inside `K(x)` itself. -/
@[simp]
theorem relfinrank_extendRight (F : IntermediateField K (RatFunc K)) :
    relfinrank (F.extendRight W.FunctionField) (ratFuncRange W) =
      Module.finrank F (RatFunc K) := by
  rw [ratFuncRange_eq_map, IntermediateField.extendRight_eq_map, relfinrank_map_map,
    relfinrank_top_right]

/-- **`[K(W) : F] = 2 · [K(x) : F]`**: the inner storey contributes the degree of `F` and the
outer one contributes two. When `K(x)` is infinite-dimensional over `F` both sides are `0`,
`Module.finrank`'s value there. -/
@[simp]
theorem finrank_extendRight (F : IntermediateField K (RatFunc K)) :
    Module.finrank (F.extendRight W.FunctionField) W.FunctionField =
      2 * Module.finrank F (RatFunc K) := by
  rw [← relfinrank_mul_finrank_top (extendRight_le_ratFuncRange W F),
    relfinrank_extendRight, finrank_ratFuncRange, Nat.mul_comm]

/-- If an intermediate field has relative degree two over the copy of `F`, the degree of `K(W)`
over it is `[K(x) : F]`. This is the final tower step of `finrank_fieldRange_of_apply_X_eq`. -/
private theorem finrank_of_relfinrank_extendRight {F : IntermediateField K (RatFunc K)}
    {L : IntermediateField K W.FunctionField} (hle : F.extendRight W.FunctionField ≤ L)
    (h : relfinrank (F.extendRight W.FunctionField) L = 2) :
    Module.finrank L W.FunctionField = Module.finrank F (RatFunc K) := by
  have htower := relfinrank_mul_finrank_top hle
  rw [h, finrank_extendRight] at htower
  exact Nat.eq_of_mul_eq_mul_left two_pos htower

/-- **The copy of `K⟮g⟯` inside `K(W)` is the image of the rational function field of `W'`**, for
any embedding `f : K(W') → K(W)` of function fields carrying the affine coordinate of `W'` to `g`.
This is the field the degree tower below is anchored at, in its two descriptions. -/
theorem extendRight_adjoin_eq_map_ratFuncRange {W' : WeierstrassCurve.Affine K} {g : RatFunc K}
    (f : W'.FunctionField →ₐ[K] W.FunctionField)
    (hf : f (algebraMap K[X] W'.FunctionField X) = algebraMap (RatFunc K) W.FunctionField g) :
    (adjoin K {g}).extendRight W.FunctionField = (ratFuncRange W').map f := by
  rw [IntermediateField.extendRight_eq_map, ratFuncRange_eq_map,
    IntermediateField.map_map, ← RatFunc.adjoin_X]
  simp only [IntermediateField.adjoin_map, Set.image_singleton, AlgHom.coe_comp,
    Function.comp_apply, toAlgHom_ratFuncX, hf]
  rw [IsScalarTower.coe_toAlgHom']

/-- **`[K(W) : f(K(W'))] = [K(x) : K⟮g⟯]`** for an embedding `f : K(W') → K(W)` of function fields
carrying the affine coordinate of `W'` to `g`. Both `K(x)` and the image of `K(W')` lie between
`K⟮g⟯` and `K(W)`, of relative degrees `[K(x) : K⟮g⟯]` and `2` over it; since `[K(W) : K(x)] = 2`
as well, the two towers give `2 · [K(W) : f(K(W'))] = 2 · [K(x) : K⟮g⟯]`. -/
theorem finrank_fieldRange_of_apply_X_eq {W' : WeierstrassCurve.Affine K} {g : RatFunc K}
    (f : W'.FunctionField →ₐ[K] W.FunctionField)
    (hf : f (algebraMap K[X] W'.FunctionField X) = algebraMap (RatFunc K) W.FunctionField g) :
    Module.finrank f.fieldRange W.FunctionField = Module.finrank (adjoin K {g}) (RatFunc K) := by
  have h := extendRight_adjoin_eq_map_ratFuncRange W f hf
  refine finrank_of_relfinrank_extendRight W ?_ ?_
  · rw [h, AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono _ le_top
  · rw [h, relfinrank_map_ratFuncRange_fieldRange]

end WeierstrassCurve.Affine

end
