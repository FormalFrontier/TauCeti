/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Reduction of endomorphisms modulo `I • M`

An endomorphism of a module `M` carries `I • M` into itself, so it descends to the quotient
`M ⧸ I • M`, and the descent is a ring homomorphism `Ideal.endMapQ I M`. This file constructs that
reduction map and proves the two properties that make idempotents lift along it: it is surjective
when `M` is projective, and its kernel consists of nilpotent elements when `I` is nilpotent.

The kernel is characterized by `Ideal.mem_ker_endMapQ_iff`: an endomorphism dies under reduction
exactly when its image lies in `I • M`. Iterating that containment is what makes the kernel nil,
the image of the `k`-th power lying in `I ^ k • M`.

## Main definitions

* `Ideal.endMapQ`: reduction of endomorphisms modulo `I • M`, as a ring homomorphism
  `Module.End R M →+* Module.End R (M ⧸ I • ⊤)`.

## Main results

* `Ideal.mem_ker_endMapQ_iff`: the kernel of the reduction map consists of the endomorphisms with
  image inside `I • M`.
* `Ideal.endMapQ_surjective`: reduction is onto when `M` is projective.
* `Ideal.range_pow_le_of_mem_ker_endMapQ` and `Ideal.isNilpotent_of_mem_ker_endMapQ`: an
  endomorphism killed by reduction has `k`-th power with image inside `I ^ k • M`, hence is
  nilpotent as soon as `I` is.
-/

public section

namespace Ideal

universe u v

variable {R : Type u} [Ring R]

/-- **Reduction of endomorphisms modulo `I • M`.** An endomorphism of `M` carries `I • M` into
itself, so it descends to the quotient `M ⧸ I • M`, and the descent is a ring homomorphism. -/
def endMapQ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Module.End R M →+* Module.End R (M ⧸ I • (⊤ : Submodule R M)) where
  toFun f := Submodule.mapQ _ _ f (Submodule.map_le_iff_le_comap.mp
    (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))
  -- Each law is checked on the classes `Submodule.Quotient.mk x`, where `Submodule.mapQ_apply`
  -- evaluates both sides.
  map_one' := Submodule.linearMap_qext _ (by ext x; simp)
  map_mul' _ _ := Submodule.linearMap_qext _ (by ext x; simp)
  map_zero' := Submodule.linearMap_qext _ (by ext x; simp)
  map_add' _ _ := Submodule.linearMap_qext _ (by ext x; simp)

variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

@[simp]
theorem endMapQ_mk (f : Module.End R M) (x : M) :
    endMapQ I M f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := by
  simp [endMapQ]

/-- Every endomorphism of `M ⧸ I • M` is the reduction of an endomorphism of `M`, provided `M` is
projective: lift the composite `M ↠ M ⧸ I • M → M ⧸ I • M` through the quotient map. -/
theorem endMapQ_surjective [Module.Projective R M] : Function.Surjective (endMapQ I M) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ
    (g ∘ₗ (I • (⊤ : Submodule R M)).mkQ) (Submodule.mkQ_surjective _)
  refine ⟨f, LinearMap.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun hf y

/-- **The kernel of the reduction map.** An endomorphism reduces to zero exactly when its image
lies in `I • M`, membership in the kernel being tested on the classes of `M ⧸ I • M`. -/
theorem mem_ker_endMapQ_iff {f : Module.End R M} :
    f ∈ RingHom.ker (endMapQ I M) ↔ LinearMap.range f ≤ I • (⊤ : Submodule R M) := by
  rw [RingHom.mem_ker]
  constructor
  · rintro hf _ ⟨y, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [← endMapQ_mk I M f y, hf, LinearMap.zero_apply]
  · intro hf
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simpa using (Submodule.Quotient.mk_eq_zero _).mpr (hf ⟨x, rfl⟩)

/-- An endomorphism killed by the reduction map has image inside `I • M`, hence `k`-th power with
image inside `I ^ k • M`. -/
theorem range_pow_le_of_mem_ker_endMapQ {f : Module.End R M}
    (hf : f ∈ RingHom.ker (endMapQ I M)) (k : ℕ) :
    LinearMap.range (f ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
  have hrange : LinearMap.range f ≤ I • (⊤ : Submodule R M) := (mem_ker_endMapQ_iff I M).mp hf
  induction k with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_top
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map f (LinearMap.range (f ^ k))
          ≤ Submodule.map f (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map f ⊤ := by rw [Submodule.map_smul'']
        _ = I ^ k • LinearMap.range f := by rw [Submodule.map_top]
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := Submodule.smul_mono le_rfl hrange
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [Submodule.pow_succ, Submodule.mul_smul]

/-- **The kernel of the reduction map is nil** when `I` is nilpotent: an endomorphism with image in
`I • M` has a vanishing power, because `I ^ k • M` vanishes. -/
theorem isNilpotent_of_mem_ker_endMapQ (hI : IsNilpotent I) {f : Module.End R M}
    (hf : f ∈ RingHom.ker (endMapQ I M)) : IsNilpotent f := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, LinearMap.range_eq_bot.mp (le_bot_iff.mp ?_)⟩
  simpa [hm] using range_pow_le_of_mem_ker_endMapQ I M hf m

end Ideal
