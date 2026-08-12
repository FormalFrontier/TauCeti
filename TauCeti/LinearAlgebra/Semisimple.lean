/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Semisimple

/-!
# Transporting semisimplicity of an endomorphism along an injection

`LinearEquiv.isSemisimple_iff` transports semisimplicity between two endomorphisms intertwined by
a linear equivalence. For one of the two directions an injection is enough: an endomorphism that
embeds equivariantly into a semisimple one is semisimple, just as a submodule of a semisimple
module is semisimple.

## Main results

* `TauCeti.Module.End.IsSemisimple.of_injective`: semisimplicity passes to an endomorphism that
  admits an injective intertwiner into a semisimple one.
-/

public section

namespace TauCeti

open Polynomial

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Semisimplicity descends along an injective intertwiner.** If `i` is injective and carries
`f` to `g`, and `g` is semisimple, then so is `f`. -/
theorem IsSemisimple.of_injective {f : _root_.Module.End R M} {g : _root_.Module.End R N}
    (hg : _root_.Module.End.IsSemisimple g) (i : M →ₗ[R] N) (hi : Function.Injective i)
    (hcomm : i ∘ₗ f = g ∘ₗ i) : _root_.Module.End.IsSemisimple f := by
  rw [_root_.Module.End.IsSemisimple] at hg ⊢
  -- `i` is `R[X]`-linear for the two `AEval'` structures precisely because it intertwines the
  -- endomorphisms, so it embeds `AEval' f` into the semisimple module `AEval' g`.
  let iX : Module.AEval' f →ₗ[R[X]] Module.AEval' g :=
    LinearMap.ofAEval _ ((Module.AEval'.of g).toLinearMap.comp i) fun x ↦ by
      simpa [Module.AEval'.X_smul_of] using congrArg (Module.AEval'.of g)
        (LinearMap.congr_fun hcomm x)
  apply IsSemisimpleModule.of_injective iX
  intro x y hxy
  apply (Module.AEval'.of f).symm.injective
  apply hi
  apply (Module.AEval'.of g).injective
  exact hxy

end Module.End

end TauCeti
