/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Exterior powers of representations

This file equips each exterior power of a representation with the induced diagonal action.
Intertwining maps and equivalences pass functorially to exterior powers, and the zeroth and first
exterior powers recover the trivial and original representations.

## Main definitions

* `Representation.exteriorPower` is the induced action on `⋀[R]^d M`.
* `IntertwiningMap.exteriorPower` is the induced map between exterior-power representations.
* `Representation.Equiv.exteriorPower` is the induced equivalence.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.

The functorial exterior-power API transported here — `exteriorPower.map`, its identity and
composition laws, and the equivalences `exteriorPower.zeroEquiv` and `exteriorPower.oneEquiv` —
is Mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Basic`, by Sophie Morel and Joël Riou.
-/

public section

open scoped TensorProduct

universe u v w w'

variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The action induced by a representation on its `d`th exterior power. -/
noncomputable def exteriorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⋀[R]^d M) where
  toFun g := _root_.exteriorPower.map d (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, _root_.exteriorPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (_root_.exteriorPower.map_comp (n := d) (ρ h) (ρ g))

/-- The action on an exterior power is induced by the action on the original representation. -/
@[simp]
theorem exteriorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.exteriorPower d g = _root_.exteriorPower.map d (ρ g) :=
  (rfl)

/-- The exterior-power action applies the original action to every factor of a pure wedge.

This is intentionally not a simp lemma: `exteriorPower_apply` followed by Mathlib's
`exteriorPower.map_apply_ιMulti` already performs this simplification. -/
theorem exteriorPower_apply_ιMulti (ρ : Representation R G M) (d : ℕ) (g : G) (m : Fin d → M) :
    ρ.exteriorPower d g (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (ρ g ∘ m) := by
  rw [exteriorPower_apply, _root_.exteriorPower.map_apply_ιMulti]

/-- The zeroth exterior power is equivalent to the trivial representation on the scalars. -/
noncomputable def exteriorPowerZeroEquiv (ρ : Representation R G M) :
    (ρ.exteriorPower 0).Equiv (trivial R G R) :=
  .mk (_root_.exteriorPower.zeroEquiv R M) fun g => by
    rw [exteriorPower_apply, _root_.exteriorPower.zeroEquiv_naturality]
    simp

/-- The underlying linear equivalence is Mathlib's identification of the zeroth exterior power
with the scalars. -/
@[simp]
theorem exteriorPowerZeroEquiv_toLinearEquiv (ρ : Representation R G M) :
    ρ.exteriorPowerZeroEquiv.toLinearEquiv = _root_.exteriorPower.zeroEquiv R M :=
  (rfl)

/-- The first exterior power is equivalent to the original representation. -/
noncomputable def exteriorPowerOneEquiv (ρ : Representation R G M) : (ρ.exteriorPower 1).Equiv ρ :=
  .mk (_root_.exteriorPower.oneEquiv R M) fun g =>
    _root_.exteriorPower.oneEquiv_naturality (ρ g)

/-- The underlying linear equivalence is Mathlib's identification of the first exterior power
with the module itself. -/
@[simp]
theorem exteriorPowerOneEquiv_toLinearEquiv (ρ : Representation R G M) :
    ρ.exteriorPowerOneEquiv.toLinearEquiv = _root_.exteriorPower.oneEquiv R M :=
  (rfl)

end CommRing

end Representation

namespace Representation.IntertwiningMap

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An intertwining map induces an intertwining map on every exterior power. -/
noncomputable def exteriorPower (f : IntertwiningMap ρ σ) (d : ℕ) :
    IntertwiningMap (ρ.exteriorPower d) (σ.exteriorPower d) where
  toLinearMap := _root_.exteriorPower.map d f.toLinearMap
  isIntertwining' g := by
    rw [Representation.exteriorPower_apply, Representation.exteriorPower_apply,
      ← _root_.exteriorPower.map_comp, ← _root_.exteriorPower.map_comp,
      f.isIntertwining']

/-- The underlying linear map is the usual map induced on exterior powers. -/
@[simp]
theorem exteriorPower_toLinearMap (f : IntertwiningMap ρ σ) (d : ℕ) :
    (f.exteriorPower d).toLinearMap = _root_.exteriorPower.map d f.toLinearMap :=
  (rfl)

/-- The induced map sends a pure wedge to the wedge of the images of its factors. -/
@[simp]
theorem exteriorPower_apply_ιMulti (f : IntertwiningMap ρ σ) (d : ℕ) (m : Fin d → M) :
    f.exteriorPower d (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (f ∘ m) :=
  _root_.exteriorPower.map_apply_ιMulti f.toLinearMap m

/-- Exterior powers preserve identity intertwining maps. -/
@[simp]
theorem exteriorPower_id (d : ℕ) :
    (IntertwiningMap.id ρ).exteriorPower d = IntertwiningMap.id (ρ.exteriorPower d) := by
  apply IntertwiningMap.ext
  simp

/-- Exterior powers preserve composition of intertwining maps. -/
@[simp]
theorem exteriorPower_comp {P : Type*} [AddCommGroup P] [Module R P]
    {τ : Representation R G P} (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) (d : ℕ) :
    (g.comp f).exteriorPower d = (g.exteriorPower d).comp (f.exteriorPower d) := by
  apply IntertwiningMap.ext
  exact _root_.exteriorPower.map_comp f.toLinearMap g.toLinearMap

end CommRing

end Representation.IntertwiningMap

namespace Representation.Equiv

section CommRing

variable [CommRing R] [Monoid G]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- The linear equivalence induced on `d`th exterior powers by an equivalence of representations.

This is built from the explicit inverse `exteriorPower.map d e.symm.toLinearMap` rather than from
bijectivity of `exteriorPower.map d e.toLinearMap`, so that the inverse is *definitionally* the
map induced by `e.symm`; that is what makes `exteriorPowerLinearEquiv_symm_toLinearMap`, and hence
`exteriorPower_symm`, hold. Mathlib builds `TensorProduct.congr` the same way. -/
private noncomputable def exteriorPowerLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (⋀[R]^d M) ≃ₗ[R] (⋀[R]^d N) :=
  LinearEquiv.ofLinear
    (_root_.exteriorPower.map d e.toLinearMap)
    (_root_.exteriorPower.map d e.symm.toLinearMap)
    (by
      rw [← _root_.exteriorPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.comp_symm, _root_.exteriorPower.map_id])
    (by
      rw [← _root_.exteriorPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.symm_comp, _root_.exteriorPower.map_id])

private theorem exteriorPowerLinearEquiv_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (exteriorPowerLinearEquiv e d).toLinearMap =
      _root_.exteriorPower.map d e.toLinearMap :=
  LinearEquiv.ofLinear_toLinearMap ..

private theorem exteriorPowerLinearEquiv_symm_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (exteriorPowerLinearEquiv e d).symm.toLinearMap =
      _root_.exteriorPower.map d e.symm.toLinearMap :=
  LinearEquiv.ofLinear_symm_toLinearMap ..

/-- An equivalence of representations induces an equivalence of every exterior power. -/
noncomputable def exteriorPower (e : ρ.Equiv σ) (d : ℕ) :
    (ρ.exteriorPower d).Equiv (σ.exteriorPower d) :=
  .mk (exteriorPowerLinearEquiv e d) fun g => by
    rw [exteriorPowerLinearEquiv_toLinearMap]
    exact (e.toIntertwiningMap.exteriorPower d).isIntertwining' g

private theorem exteriorPower_toLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (e.exteriorPower d).toLinearEquiv = exteriorPowerLinearEquiv e d :=
  toLinearEquiv_mk' _

/-- The underlying linear map is the usual map induced on exterior powers. -/
@[simp]
theorem exteriorPower_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (e.exteriorPower d).toLinearMap = _root_.exteriorPower.map d e.toLinearMap :=
  (rfl)

/-- The induced equivalence sends a pure wedge to the wedge of the images of its factors. -/
@[simp]
theorem exteriorPower_apply_ιMulti (e : ρ.Equiv σ) (d : ℕ) (m : Fin d → M) :
    e.exteriorPower d (_root_.exteriorPower.ιMulti R d m) =
      _root_.exteriorPower.ιMulti R d (e ∘ m) :=
  _root_.exteriorPower.map_apply_ιMulti e.toLinearMap m

/-- Exterior powers preserve identity equivalences. -/
@[simp]
theorem exteriorPower_refl (d : ℕ) :
    (Equiv.refl ρ).exteriorPower d = .refl (ρ.exteriorPower d) := by
  have h : ((Equiv.refl ρ).exteriorPower d).toLinearMap =
      (Equiv.refl (ρ.exteriorPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Exterior powers preserve inverses of equivalences. -/
@[simp]
theorem exteriorPower_symm (e : ρ.Equiv σ) (d : ℕ) :
    e.symm.exteriorPower d = (e.exteriorPower d).symm := by
  have h : (e.symm.exteriorPower d).toLinearMap =
      ((e.exteriorPower d).symm).toLinearMap := by
    rw [exteriorPower_toLinearMap, toLinearMap_symm (e.exteriorPower d),
      exteriorPower_toLinearEquiv, exteriorPowerLinearEquiv_symm_toLinearMap]
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Exterior powers preserve composition of equivalences. -/
@[simp]
theorem exteriorPower_trans {P : Type*} [AddCommGroup P] [Module R P]
    {τ : Representation R G P} (e : ρ.Equiv σ) (f : σ.Equiv τ) (d : ℕ) :
    (e.trans f).exteriorPower d = (e.exteriorPower d).trans (f.exteriorPower d) := by
  have h : ((e.trans f).exteriorPower d).toLinearMap =
      ((e.exteriorPower d).trans (f.exteriorPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

end CommRing

end Representation.Equiv
