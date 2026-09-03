/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Injectivity of tensor-product algebra morphisms

This file transfers injectivity of two algebra morphisms over a field to their tensor-product
algebra morphism.

## Main declarations

* `TauCeti.Algebra.TensorProduct.map_injective_of_injective`: over a field, tensoring two
  injective algebra morphisms gives an injective tensor-product algebra morphism.

## References

The result is the algebra-morphism form of Mathlib's
`TensorProduct.map_injective_of_flat_flat`.
-/

public section

namespace TauCeti.Algebra.TensorProduct

universe u v w x y

variable {k : Type u} [Field k]

/-- Over a field, the tensor-product algebra morphism induced by two injective algebra morphisms
is injective. -/
theorem map_injective_of_injective {A : Type v} {B : Type w} {C : Type x} {D : Type y}
    [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] B) (g : C →ₐ[k] D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (_root_.Algebra.TensorProduct.map f g) := by
  -- Expose the underlying linear map so the named tensor-product map lemmas can rewrite it.
  change Function.Injective (_root_.Algebra.TensorProduct.map f g).toLinearMap
  rw [_root_.Algebra.TensorProduct.toLinearMap_map,
    _root_.TensorProduct.AlgebraTensorModule.map_eq]
  exact _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

end TauCeti.Algebra.TensorProduct
