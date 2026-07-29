/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.SymmetricPower

/-!
# Symmetric powers of representations

This file equips each symmetric power of a representation with the induced diagonal action.
Intertwining maps and equivalences pass functorially to symmetric powers.

## Main definitions

* `Representation.symmetricPower` is the induced action on `Sym[R]^d M`.
* `IntertwiningMap.symmetricPower` is the induced map between symmetric-power representations.
* `Representation.Equiv.symmetricPower` is the induced equivalence.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
-/

public section

open scoped TensorProduct

universe v w w'

variable {R : Type} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M]

/-- The action induced by a representation on its `d`th symmetric power. -/
noncomputable def symmetricPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (Sym[R]^d M) where
  toFun g := SymmetricPower.map (ι := Fin d) (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (SymmetricPower.map_comp (ι := Fin d) (ρ h) (ρ g))

/-- The action on a symmetric power is induced by the action on the original representation. -/
@[simp]
theorem symmetricPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  (rfl)

/-- The symmetric-power action applies the original action to every factor of a pure tensor.

This is intentionally not a simp lemma: `symmetricPower_apply` followed by
`SymmetricPower.map_tprod` already performs this simplification. -/
theorem symmetricPower_apply_tprod (ρ : Representation R G M) (d : ℕ) (g : G)
    (m : Fin d → M) :
    ρ.symmetricPower d g (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, ρ g (m i) := by
  rw [symmetricPower_apply, SymmetricPower.map_tprod]

end CommSemiring

end Representation

namespace Representation.IntertwiningMap

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An intertwining map induces an intertwining map on every symmetric power. -/
noncomputable def symmetricPower (f : IntertwiningMap ρ σ) (d : ℕ) :
    IntertwiningMap (ρ.symmetricPower d) (σ.symmetricPower d) where
  toLinearMap := SymmetricPower.map (ι := Fin d) f.toLinearMap
  isIntertwining' g := by
    rw [Representation.symmetricPower_apply, Representation.symmetricPower_apply,
      ← SymmetricPower.map_comp, ← SymmetricPower.map_comp, f.isIntertwining']

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (f : IntertwiningMap ρ σ) (d : ℕ) :
    (f.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) f.toLinearMap :=
  (rfl)

/-- The induced map sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (f : IntertwiningMap ρ σ) (d : ℕ) (m : Fin d → M) :
    f.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) :=
  SymmetricPower.map_tprod f.toLinearMap m

/-- Symmetric powers preserve identity intertwining maps. -/
@[simp]
theorem symmetricPower_id (d : ℕ) :
    (IntertwiningMap.id ρ).symmetricPower d =
      IntertwiningMap.id (ρ.symmetricPower d) := by
  apply IntertwiningMap.ext
  simp

/-- Symmetric powers preserve composition of intertwining maps. -/
@[simp]
theorem symmetricPower_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) (d : ℕ) :
    (g.comp f).symmetricPower d =
      (g.symmetricPower d).comp (f.symmetricPower d) := by
  apply IntertwiningMap.ext
  exact SymmetricPower.map_comp f.toLinearMap g.toLinearMap

end CommSemiring

end Representation.IntertwiningMap

namespace Representation.Equiv

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- The linear equivalence induced on `d`th symmetric powers by an equivalence of
representations. -/
private noncomputable def symmetricPowerLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (Sym[R]^d M) ≃ₗ[R] (Sym[R]^d N) :=
  LinearEquiv.ofLinear
    (SymmetricPower.map (ι := Fin d) e.toLinearMap)
    (SymmetricPower.map (ι := Fin d) e.symm.toLinearMap)
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.comp_symm, SymmetricPower.map_id])
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.symm_comp, SymmetricPower.map_id])

private theorem symmetricPowerLinearEquiv_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  LinearEquiv.ofLinear_toLinearMap ..

private theorem symmetricPowerLinearEquiv_symm_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).symm.toLinearMap =
      SymmetricPower.map (ι := Fin d) e.symm.toLinearMap :=
  LinearEquiv.ofLinear_symm_toLinearMap ..

/-- An equivalence of representations induces an equivalence of every symmetric power. -/
noncomputable def symmetricPower (e : ρ.Equiv σ) (d : ℕ) :
    (ρ.symmetricPower d).Equiv (σ.symmetricPower d) :=
  .mk (symmetricPowerLinearEquiv e d) fun g => by
    rw [symmetricPowerLinearEquiv_toLinearMap]
    exact (e.toIntertwiningMap.symmetricPower d).isIntertwining' g

private theorem symmetricPower_toLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (e.symmetricPower d).toLinearEquiv = symmetricPowerLinearEquiv e d :=
  toLinearEquiv_mk' _

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (e.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  (rfl)

/-- The induced equivalence sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (e : ρ.Equiv σ) (d : ℕ) (m : Fin d → M) :
    e.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, e (m i) :=
  SymmetricPower.map_tprod e.toLinearMap m

/-- Symmetric powers preserve identity equivalences. -/
@[simp]
theorem symmetricPower_refl (d : ℕ) :
    (Equiv.refl ρ).symmetricPower d = .refl (ρ.symmetricPower d) := by
  have h : ((Equiv.refl ρ).symmetricPower d).toLinearMap =
      (Equiv.refl (ρ.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve inverses of equivalences. -/
@[simp]
theorem symmetricPower_symm (e : ρ.Equiv σ) (d : ℕ) :
    e.symm.symmetricPower d = (e.symmetricPower d).symm := by
  have h : (e.symm.symmetricPower d).toLinearMap =
      ((e.symmetricPower d).symm).toLinearMap := by
    rw [symmetricPower_toLinearMap, toLinearMap_symm (e.symmetricPower d),
      symmetricPower_toLinearEquiv, symmetricPowerLinearEquiv_symm_toLinearMap]
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve composition of equivalences. -/
@[simp]
theorem symmetricPower_trans {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (e : ρ.Equiv σ) (f : σ.Equiv τ) (d : ℕ) :
    (e.trans f).symmetricPower d =
      (e.symmetricPower d).trans (f.symmetricPower d) := by
  have h : ((e.trans f).symmetricPower d).toLinearMap =
      ((e.symmetricPower d).trans (f.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

end CommSemiring

end Representation.Equiv
