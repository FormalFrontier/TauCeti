/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Cocommutative coalgebras

This file records transport results for cocommutative coalgebras.

## Main declarations

* `TauCeti.Coalgebra.IsCocomm.of_bialgEquiv`: cocommutativity transfers across a bialgebra
  equivalence.
-/

public section

namespace TauCeti.Coalgebra.IsCocomm

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [_root_.Bialgebra R A] [_root_.Bialgebra R B]

/-- Cocommutativity transfers across a bialgebra equivalence. -/
theorem of_bialgEquiv (e : A ≃ₐc[R] B) [hA : _root_.Coalgebra.IsCocomm R A] :
    _root_.Coalgebra.IsCocomm R B := by
  constructor
  ext b
  apply (TensorProduct.map_bijective e.symm.bijective e.symm.bijective).injective
  simp only [LinearMap.comp_apply]
  -- Applying the tensor map to the composite with `TensorProduct.comm` unfolds to this
  -- expression. There is no propositional compatibility lemma for that coercion-level step;
  -- the subsequent `TensorProduct.map_comm` is the structural identity used by the proof.
  change TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
      (TensorProduct.comm R B B (Coalgebra.comul (R := R) b)) = _
  rw [TensorProduct.map_comm]
  have hm :
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
          (Coalgebra.comul (R := R) b) =
        Coalgebra.comul (R := R) (e.symm b) :=
    CoalgHomClass.map_comp_comul_apply e.symm b
  rw [hm, Coalgebra.comm_comul]

end TauCeti.Coalgebra.IsCocomm
