/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The Frobenius trace pairing on the dual numbers

This file equips the dual numbers over a commutative semiring with the perfect symmetric
associative bilinear form obtained by taking the infinitesimal coefficient of a product.

## Main results

* `TauCeti.dualNumberTracePairing`: the Frobenius trace pairing on the dual numbers.
* `TauCeti.dualNumberTracePairing_isPerfPair`: the trace pairing is perfect.
* `TauCeti.dualNumberTracePairing_isSymm`: the trace pairing is symmetric.
* `TauCeti.dualNumberTracePairing_mul_assoc`: the trace pairing is associative.
-/

public section

namespace TauCeti

universe w

variable (k : Type w) [CommSemiring k]

-- The coordinatewise module structure used by `DualNumber` is compatible with multiplication,
-- but Mathlib does not provide this scalar-tower instance for `TrivSqZeroExt`.
local instance dualNumberIsScalarTower :
    IsScalarTower k (DualNumber k) (DualNumber k) where
  smul_assoc r x y := by
    ext <;> simp [mul_add, mul_assoc, mul_comm, mul_left_comm, add_comm]

/-- The Frobenius pairing on the dual numbers, obtained by taking the infinitesimal coefficient
of a product. -/
noncomputable def dualNumberTracePairing : LinearMap.BilinForm k (DualNumber k) :=
  (LinearMap.mul k (DualNumber k)).compr₂ (TrivSqZeroExt.sndHom k k)

/-- Evaluation of the dual-number Frobenius pairing in scalar and infinitesimal coordinates. -/
@[simp]
theorem dualNumberTracePairing_apply (x y : DualNumber k) :
    dualNumberTracePairing k x y = x.fst * y.snd + x.snd * y.fst := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.mul_apply',
    TrivSqZeroExt.sndHom_apply, DualNumber.snd_mul]

/-- The Frobenius trace pairing on the dual numbers is symmetric. -/
theorem dualNumberTracePairing_isSymm : (dualNumberTracePairing k).IsSymm :=
  ⟨fun x y => by simp only [dualNumberTracePairing_apply]; ring⟩

/-- The Frobenius trace pairing on the dual numbers is perfect. -/
instance dualNumberTracePairing_isPerfPair : (dualNumberTracePairing k).IsPerfPair := by
  have hbij : Function.Bijective (dualNumberTracePairing k) := by
    constructor
    · intro x y h
      apply TrivSqZeroExt.ext
      · have he := LinearMap.congr_fun h DualNumber.eps
        simpa using he
      · have h1 := LinearMap.congr_fun h 1
        simpa using h1
    · intro f
      let d : DualNumber k := ⟨f DualNumber.eps, f 1⟩
      refine ⟨d, ?_⟩
      apply LinearMap.ext
      intro y
      calc
        dualNumberTracePairing k d y =
            y.snd * f DualNumber.eps + y.fst * f 1 := by
          rw [dualNumberTracePairing_apply]
          dsimp only [d, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
          ring
        _ = f (y.snd • DualNumber.eps + y.fst • (1 : DualNumber k)) := by
          rw [map_add, map_smul, map_smul]
          ring
        _ = f y := by
          congr 1
          apply TrivSqZeroExt.ext <;> simp
  refine ⟨hbij, ?_⟩
  constructor
  · intro x y h
    apply hbij.injective
    apply LinearMap.ext
    intro z
    rw [(dualNumberTracePairing_isSymm k).eq x z,
      (dualNumberTracePairing_isSymm k).eq y z]
    simpa only [LinearMap.flip_apply] using LinearMap.congr_fun h z
  · intro f
    obtain ⟨x, hx⟩ := hbij.surjective f
    refine ⟨x, LinearMap.ext fun z => ?_⟩
    simp only [LinearMap.flip_apply]
    rw [(dualNumberTracePairing_isSymm k).eq z x]
    exact LinearMap.congr_fun hx z

/-- The Frobenius trace pairing on the dual numbers is associative with multiplication. -/
theorem dualNumberTracePairing_mul_assoc (x y z : DualNumber k) :
    dualNumberTracePairing k (x * y) z = dualNumberTracePairing k x (y * z) := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', mul_assoc]

end TauCeti
