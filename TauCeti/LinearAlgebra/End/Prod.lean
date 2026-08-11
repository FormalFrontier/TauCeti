/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Products of endomorphisms

This file proves that nilpotence and semisimplicity are preserved by componentwise products of
endomorphisms.

## Main declarations

* `IsNilpotent.prodMap`: a product of nilpotent endomorphisms is nilpotent.
* `TauCeti.Module.End.IsSemisimple.prodMap`: a product of semisimple endomorphisms is semisimple.
-/

public section

namespace TauCeti

open LinearMap Polynomial

namespace Module.End

universe u v w

section Semiring

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

@[simp]
private theorem prodMap_pow (f : Module.End K V) (g : Module.End K W) (n : ℕ) :
    (f.prodMap g) ^ n = (f ^ n).prodMap (g ^ n) := by
  induction n with
  | zero => exact LinearMap.prodMap_one.symm
  | succ n hn => rw [pow_succ, pow_succ, pow_succ, hn, LinearMap.prodMap_mul]

/-- The componentwise product of two nilpotent endomorphisms is nilpotent. -/
theorem _root_.IsNilpotent.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : IsNilpotent f) (hg : IsNilpotent g) : IsNilpotent (f.prodMap g) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, ?_⟩
  rw [prodMap_pow, pow_add, hm, zero_mul, pow_add, hn, mul_zero,
    LinearMap.prodMap_zero]

end Semiring

section CommRing

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem aeval_prodMap (f : Module.End K V) (g : Module.End K W) (p : K[X]) :
    aeval (f.prodMap g) p = (aeval f p).prodMap (aeval g p) := by
  have h : aeval (f.prodMap g) =
      (LinearMap.prodMapAlgHom K V W).comp ((aeval f).prod (aeval g)) := by
    ext <;> simp
  exact DFunLike.congr_fun h p

/-- The componentwise product of two semisimple endomorphisms is semisimple. -/
theorem IsSemisimple.prodMap {f : Module.End K V} {g : Module.End K W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    Module.End.IsSemisimple (f.prodMap g) := by
  rw [Module.End.IsSemisimple] at hf hg ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let _ : IsSemisimpleModule K[X] (Module.AEval' g) := hg
  let M : Fin 2 → ModuleCat.{max v w} K[X] := fun i ↦
    if i = 0 then ModuleCat.of K[X] (ULift.{max v w} (Module.AEval' f))
    else ModuleCat.of K[X] (ULift.{max v w} (Module.AEval' g))
  let _ (i : Fin 2) : IsSemisimpleModule K[X] (M i) := by
    by_cases hi : i = 0
    · subst i
      simpa [M] using IsSemisimpleModule.congr
        (ULift.moduleEquiv : ULift.{max v w} (Module.AEval' f) ≃ₗ[K[X]] Module.AEval' f)
    · -- Cross the dependent, universe-lifted family boundary before applying the equivalence.
      have hM : M i = ModuleCat.of K[X] (ULift.{max v w} (Module.AEval' g)) := by
        simp [M, hi]
      rw [hM]
      exact IsSemisimpleModule.congr
        (ULift.moduleEquiv : ULift.{max v w} (Module.AEval' g) ≃ₗ[K[X]] Module.AEval' g)
  have hprod : IsSemisimpleModule K[X] (Module.AEval' f × Module.AEval' g) := by
    let e₀ : (M 0 × M 1) ≃ₗ[K[X]] Module.AEval' f × Module.AEval' g := by
      simpa [M] using
        ((ULift.moduleEquiv : ULift.{max v w} (Module.AEval' f) ≃ₗ[K[X]]
          Module.AEval' f).prodCongr
          (ULift.moduleEquiv : ULift.{max v w} (Module.AEval' g) ≃ₗ[K[X]] Module.AEval' g))
    let e := (LinearEquiv.piFinTwo K[X] (fun i ↦ (M i : Type (max v w)))).trans e₀
    exact e.isSemisimpleModule_iff.mp inferInstance
  let E : Module.AEval' (f.prodMap g) ≃ₗ[K[X]]
      Module.AEval' f × Module.AEval' g := {
    toFun x := (x.1, x.2)
    invFun x := (x.1, x.2)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' p x := by
      -- Unfold the two `AEval` scalar actions to compare their underlying endomorphisms.
      apply Prod.ext
      · change ((aeval (f.prodMap g) p) x).1 = (aeval f p) x.1
        rw [aeval_prodMap]
        rfl
      · change ((aeval (f.prodMap g) p) x).2 = (aeval g p) x.2
        rw [aeval_prodMap]
        rfl
  }
  let _ := hprod
  exact IsSemisimpleModule.congr E

end CommRing

end Module.End

end TauCeti
