/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

/-!
# Cyclic finite quadratic modules

A `ℚ/ℤ`-valued quadratic map on `ℤ/m` is determined by its value on the generator `1`, and a
value `a` occurs exactly when `m²a = 0` and `2ma = 0`.  This file makes that presentation
available as a construction: given `a : ℚ/ℤ` satisfying those two torsion conditions,
`TauCeti.FiniteQuadraticModule.cyclic` is the finite quadratic module on `ZMod m` with

```text
q(k) = k²a,   b(j, k) = 2jk·a.
```

The construction is a quotient, not a formula in `ZMod.val`: the parameter defines the honest
`ℤ`-bilinear map `(x, y) ↦ xy·a` on `ℤ`, its associated quadratic map `x ↦ x²a` has the kernel of
the reduction `ℤ → ℤ/m` inside its radical exactly under the two torsion hypotheses, and
`QuadraticMap.liftOfSurjective` descends it.  The hypotheses are therefore not technical:
`m²a = 0` is the statement that the quadratic value of the generator is well defined modulo `m`,
and `2ma = 0` the corresponding statement for the pairing.  Neither implies the other: for `m = 1`
and `a = 1/2` the second holds (`2a = 0`) and the first fails (`a = 1/2`), while for `m = 3` and
`a = 1/9` the first holds (`9a = 0`) and the second fails (`6a = 2/3`).  No witness of the latter
kind has `m = 2`, where the two coefficients `m² = 4` and `2m = 4` agree.

The companion `TauCeti.FiniteQuadraticModule.cyclicIsometryOfGenerator` turns an additive
equivalence `ℤ/m ≃+ A` matching the single generator value into an isometry onto `A`, which is how
a cyclic discriminant form is identified.  It needs no hypothesis beyond that one value, because
an additive equivalence out of a cyclic group is determined by the image of the generator.

The rank-two analogue, presenting a form on the Klein four-group by its three nonzero values, is
`TauCeti.FiniteQuadraticModule.kleinFour` in
`TauCeti.LinearAlgebra.FiniteBilinearModule.KleinFour`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.cyclicMap`: the quadratic map on `ZMod m` whose generator has the
  prescribed value.
* `TauCeti.FiniteQuadraticModule.cyclic`: the resulting finite quadratic module.
* `TauCeti.FiniteQuadraticModule.cyclicIsometryOfGenerator`: an additive equivalence matching the
  generator value is an isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1 for
  discriminant forms and §1.8 for the cyclic forms written `q_θ^{(p)}` in the full-norm
  convention.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is part of Layer 3 of `TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteQuadraticModule

variable (m : ℕ) (a : AddCircle (1 : ℚ))

/-! ## The presenting quadratic map on `ℤ` -/

/-- The bilinear map `(x, y) ↦ xy·a` on `ℤ`: multiplication followed by the linear map sending
`1` to `a`. -/
private def cyclicBilin : LinearMap.BilinMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  (LinearMap.mul ℤ ℤ).compr₂ (LinearMap.toSpanSingleton ℤ (AddCircle (1 : ℚ)) a)

private theorem cyclicBilin_apply (x y : ℤ) : cyclicBilin a x y = (x * y) • a := (rfl)

/-- The quadratic map `x ↦ x²a` on `ℤ`. -/
private def cyclicAux : QuadraticMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  (cyclicBilin a).toQuadraticMap

private theorem cyclicAux_apply (x : ℤ) : cyclicAux a x = (x * x) • a := by
  rw [cyclicAux, LinearMap.BilinMap.toQuadraticMap_apply, cyclicBilin_apply]

private theorem polar_cyclicAux (x y : ℤ) :
    QuadraticMap.polar (cyclicAux a) x y = (2 * (x * y)) • a := by
  rw [cyclicAux, LinearMap.BilinMap.polar_toQuadraticMap, cyclicBilin_apply, cyclicBilin_apply,
    ← add_smul]
  congr 1
  ring

/-! ## Reduction modulo `m` -/

/-- Reduction `ℤ → ℤ/m`. -/
private def zmodProj : ℤ →ₗ[ℤ] ZMod m :=
  (Int.castAddHom (ZMod m)).toIntLinearMap

private theorem zmodProj_apply (k : ℤ) : zmodProj m k = (k : ZMod m) := (rfl)

private theorem zmodProj_surjective : Function.Surjective (zmodProj m) :=
  ZMod.intCast_surjective

private theorem mem_ker_zmodProj_iff (k : ℤ) :
    k ∈ LinearMap.ker (zmodProj m) ↔ (m : ℤ) ∣ k := by
  rw [LinearMap.mem_ker, zmodProj_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Under the two torsion hypotheses the kernel of reduction modulo `m` lies in the radical,
which is what lets the quadratic map descend. -/
private theorem ker_zmodProj_le_radical (hq : ((m : ℤ) * m) • a = 0)
    (hp : (2 * (m : ℤ)) • a = 0) :
    LinearMap.ker (zmodProj m) ≤ (cyclicAux a).radical := by
  intro x hx
  obtain ⟨k, rfl⟩ := (mem_ker_zmodProj_iff m x).mp hx
  constructor
  · rw [cyclicAux_apply]
    have e : ((m : ℤ) * k * ((m : ℤ) * k)) = (k * k) * ((m : ℤ) * m) := by ring
    rw [e, mul_smul, hq, smul_zero]
  · refine LinearMap.ext fun y ↦ ?_
    rw [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply, polar_cyclicAux]
    have e : (2 * ((m : ℤ) * k * y)) = (k * y) * (2 * (m : ℤ)) := by ring
    rw [e, mul_smul, hp, smul_zero]

/-! ## The quadratic module -/

variable (hq : ((m : ℤ) * m) • a = 0) (hp : (2 * (m : ℤ)) • a = 0)

include hq hp

/-- The quadratic map on `ℤ/m` sending the generator `1` to `a`. -/
noncomputable def cyclicMap : QuadraticMap ℤ (ZMod m) (AddCircle (1 : ℚ)) :=
  QuadraticMap.liftOfSurjective (cyclicAux a) (zmodProj m) (zmodProj_surjective m)
    (ker_zmodProj_le_radical m a hq hp)

/-- The value of `cyclicMap` on the reduction of an integer. -/
theorem cyclicMap_intCast (k : ℤ) :
    cyclicMap m a hq hp (k : ZMod m) = (k * k) • a := by
  rw [cyclicMap, ← zmodProj_apply m k, QuadraticMap.liftOfSurjective_apply, cyclicAux_apply]

@[simp]
theorem cyclicMap_one : cyclicMap m a hq hp 1 = a := by
  simpa using cyclicMap_intCast m a hq hp 1

/-- The pairing of two reductions of integers. -/
theorem polar_cyclicMap_intCast (j k : ℤ) :
    QuadraticMap.polar (cyclicMap m a hq hp) (j : ZMod m) (k : ZMod m) = (2 * (j * k)) • a := by
  rw [QuadraticMap.polar, ← Int.cast_add, cyclicMap_intCast, cyclicMap_intCast, cyclicMap_intCast]
  have e : ((j + k) * (j + k) : ℤ) = j * j + (k * k + 2 * (j * k)) := by ring
  rw [e, add_smul, add_smul]
  abel

/-- **The finite quadratic module on `ℤ/m` whose generator has value `a`.** -/
@[expose] noncomputable def cyclic [NeZero m] : FiniteQuadraticModule :=
  ofQuadraticMap (cyclicMap m a hq hp)

@[simp]
theorem cyclic_quadratic [NeZero m] (x : ZMod m) :
    (cyclic m a hq hp).quadratic x = cyclicMap m a hq hp x := (rfl)

@[simp]
theorem cyclic_pairing [NeZero m] (x y : ZMod m) :
    (cyclic m a hq hp).toFiniteBilinearModule.pairing x y =
      QuadraticMap.polar (cyclicMap m a hq hp) x y := (rfl)

omit hq hp in
/-- **An additive equivalence from `ℤ/m` matching the generator value is an isometry.**

No hypothesis beyond that single value is needed.  Both forms are stated as bare quadratic maps so
that the construction applies before either is packaged as a finite quadratic module. -/
noncomputable def cyclicIsometryOfGenerator {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod m) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod m ≃+ A)
    (h : r (e 1) = q 1) : q.IsometryEquiv r where
  toLinearEquiv := e.toIntLinearEquiv
  map_app' x := by
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    -- The linear and additive equivalences have definitionally equal coercions, so the named
    -- reflexive theorem `AddEquiv.coe_toIntLinearEquiv` gives `simp` no rewrite step here.
    change r (e (k : ZMod m)) = q (k : ZMod m)
    rw [← zsmul_one, map_zsmul, r.map_smul, q.map_smul, h]

omit hq hp in
/-- The underlying additive equivalence of `cyclicIsometryOfGenerator` is the given one. -/
@[simp]
theorem cyclicIsometryOfGenerator_toAddEquiv {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod m) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod m ≃+ A)
    (h : r (e 1) = q 1) :
    (cyclicIsometryOfGenerator m q r e h).toAddEquiv = e := (rfl)

omit hq hp in
@[simp]
theorem cyclicIsometryOfGenerator_apply {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod m) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod m ≃+ A)
    (h : r (e 1) = q 1) (x : ZMod m) :
    cyclicIsometryOfGenerator m q r e h x = e x := (rfl)

end FiniteQuadraticModule

end TauCeti
