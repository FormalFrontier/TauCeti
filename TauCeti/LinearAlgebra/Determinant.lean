/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.LinearAlgebra.BilinearForm.Multilinear

public section

/-!
# Determinant transformation laws

Precomposing an alternating form of top degree with an endomorphism `φ` multiplies it by
`LinearMap.det φ`, and — the direction that is actually used — a *nonzero* form merely known to be
*scaled* by some `d` thereby identifies `d` as the determinant, without computing it, as soon as
scalars cancel on the codomain (`NoZeroSMulDivisors R N`; see the implementation notes, where
`ω ≠ 0` alone is shown to be insufficient). This file records that law in three vocabularies: for
an `AlternatingMap` indexed by a basis' index type, for an alternating bilinear form on a rank-two
module, and for the standard-basis determinant form under matrix multiplication.

Mathlib's `Module.Basis.det_comp` is the case `ω = b.det` of the first statement. The step taken
here is that every top-degree alternating form is a multiple of `b.det`
(`AlternatingMap.eq_basis_det_smulRight`), so the same law holds for all of them; that is what
makes the converse available for a form supplied by something other than a basis, such as a
pairing.

## Main results

* `AlternatingMap.eq_basis_det_smulRight`: `ω = b.det.smulRight (ω b)` for `ω` of top degree.
* `AlternatingMap.compLinearMap_eq_det_smul`: `ω ∘ φ = det φ • ω` for `ω` of top degree.
* `LinearMap.det_eq_of_compLinearMap_eq_smul`: if `ω ≠ 0` and `ω ∘ φ = d • ω` then `det φ = d`,
  assuming `NoZeroSMulDivisors R N`.
* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul` and `LinearMap.det_eq_of_compl₁₂_self_eq_smul`: the
  same two statements for an alternating bilinear form on a module of rank two.
* `TauCeti.Matrix.detRowAlternating_mulVec`: multiplication by a square matrix scales the
  standard-basis determinant form by the matrix determinant.

## Implementation notes

The forms are valued in an arbitrary module `N`, not in `R`. Mathlib's
`AlternatingMap.eq_smul_basis_det` and `AlternatingMap.map_basis_ne_zero_iff` are the `N = R` case
of the first result here and of a step inside the recovery proofs; the codomain plays no part in
either argument, only the coordinates do, so the `N`-valued statements are what is proved.

The recovery statements need a cancellation hypothesis, not just `ω ≠ 0`: over `ZMod 4`, with
`N = R`, the form `ω = 2 • b.det` is nonzero and satisfies `ω ∘ id = 3 • ω`, while `det id = 1`.
`NoZeroSMulDivisors R N` is assumed for them, and for nothing else; for `N = R` it is implied by
`NoZeroDivisors R`.

None of the transformation laws is a `simp` lemma: the basis is a hypothesis and does not occur in
the conclusion, so `simp` could not infer it.

The bilinear statements use `LinearMap.IsAlt.toAlternatingMap` to read an alternating bilinear form
as an `AlternatingMap` on `Fin 2`.

## Provenance

The four transformation and recovery laws are ported from the AINTLIB `HasseWeil` project
(Apache-2.0), revision `513e83879e2f`, file `HasseWeil/WeilPairing/PairingDet.lean`, declarations
`alternating_comp_eq_det_smul` and `det_eq_of_alternating_scaling`. The source states them over a
field, for a scalar-valued form, evaluated at a basis, and proves the first by expanding `φ (b j)`
in coordinates; none of that is reproduced here. `TauCeti.Matrix.detRowAlternating_mulVec` predates
that port and is not from the source.
-/

open Module

namespace AlternatingMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A top-degree alternating form is its basis determinant times its value on the basis.** This
is Mathlib's `AlternatingMap.eq_smul_basis_det` with the codomain an arbitrary module rather than
`R`. -/
theorem eq_basis_det_smulRight [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
    (ω : M [⋀^ι]→ₗ[R] N) : ω = b.det.smulRight (ω ⇑b) := by
  -- Mathlib's proof generalises unchanged: it reads off the coordinates and never touches the
  -- values, and `Module.Basis.ext_alternating` is already stated for an arbitrary codomain.
  refine Module.Basis.ext_alternating b fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  -- `ext_alternating` hands back the arguments as `fun i => b (i j)`, whereas `map_perm` and
  -- `Basis.det_self` are stated for the composite `⇑b ∘ σ`. The two are the same function, so
  -- the `change` is definitional; Mathlib's own `eq_smul_basis_det` opens with the same step.
  change ω (⇑b ∘ σ) = (b.det.smulRight (ω ⇑b)) (⇑b ∘ σ)
  simp [map_perm, Basis.det_self]

/-- **An endomorphism scales a top-degree alternating form by its determinant.** Here `ω` is of
top degree in the sense that its index type indexes a basis of `M`; that basis is a hypothesis and
does not occur in the conclusion, which is an equality of alternating maps. -/
theorem compLinearMap_eq_det_smul [Finite ι] (b : Basis ι R M) (ω : M [⋀^ι]→ₗ[R] N)
    (φ : M →ₗ[R] M) : ω.compLinearMap φ = LinearMap.det φ • ω := by
  cases nonempty_fintype ι
  classical
  ext v
  rw [compLinearMap_apply, eq_basis_det_smulRight b ω]
  simp only [smulRight_apply, smul_apply]
  rw [← Function.comp_def, Basis.det_comp, mul_smul]

end AlternatingMap

namespace LinearMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The multiplier of a nonzero top-degree alternating form is the determinant.** An
endomorphism which scales `ω` by `d` has `det φ = d`; the scaling identifies the determinant
without computing it, and only the one endomorphism is involved.

`NoZeroSMulDivisors R N` is required, not incidental: `ω ≠ 0` alone leaves the multiplier
ambiguous, as the `ZMod 4` example in the module docstring shows. -/
theorem det_eq_of_compLinearMap_eq_smul [Finite ι] [NoZeroSMulDivisors R N] (b : Basis ι R M)
    {ω : M [⋀^ι]→ₗ[R] N} (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compLinearMap φ = d • ω) : LinearMap.det φ = d := by
  cases nonempty_fintype ι
  classical
  have hb : ω ⇑b ≠ 0 := fun h0 =>
    hω (by rw [AlternatingMap.eq_basis_det_smulRight b ω, h0]; ext v; simp)
  rw [AlternatingMap.compLinearMap_eq_det_smul b ω φ] at h
  have h2 := congrArg (fun f : M [⋀^ι]→ₗ[R] N => f ⇑b) h
  simp only [AlternatingMap.smul_apply] at h2
  have h3 : (LinearMap.det φ - d) • ω ⇑b = 0 := by rw [sub_smul, h2, sub_self]
  exact sub_eq_zero.mp
    ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h3).resolve_right hb)

section RankTwo

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private theorem IsAlt.toAlternatingMap_ne_zero {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (hω : ω ≠ 0) : halt.toAlternatingMap ≠ 0 := by
  contrapose! hω
  ext x y
  simpa using congrArg (fun f : M [⋀^Fin 2]→ₗ[R] N => f ![x, y]) hω

/-- **An endomorphism of a rank-two module scales an alternating bilinear form by its
determinant.** The basis is a hypothesis witnessing that the rank is two; it does not occur in the
conclusion, which is an equality of bilinear maps. -/
theorem IsAlt.compl₁₂_self_eq_det_smul (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N}
    (halt : ω.IsAlt) (φ : M →ₗ[R] M) : ω.compl₁₂ φ φ = LinearMap.det φ • ω := by
  ext x y
  have h := AlternatingMap.compLinearMap_eq_det_smul b
    halt.toAlternatingMap φ
  simpa only [compl₁₂_apply, smul_apply, AlternatingMap.compLinearMap_apply,
    LinearMap.IsAlt.toAlternatingMap_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, AlternatingMap.smul_apply] using
    congrArg (fun f : M [⋀^Fin 2]→ₗ[R] N => f ![x, y]) h

/-- **The multiplier of a nonzero alternating bilinear form on a rank-two module is the
determinant.** This is the form the additivised Weil pairing supplies: its scaling by an isogeny's
degree identifies that degree as a determinant.

As above, `NoZeroSMulDivisors R N` is required and `ω ≠ 0` alone does not suffice. -/
theorem det_eq_of_compl₁₂_self_eq_smul [NoZeroSMulDivisors R N] (b : Basis (Fin 2) R M)
    {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d := by
  refine det_eq_of_compLinearMap_eq_smul b (halt.toAlternatingMap_ne_zero hω) ?_
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simpa only [Fin.isValue, AlternatingMap.compLinearMap_apply,
    LinearMap.IsAlt.toAlternatingMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, AlternatingMap.smul_apply, compl₁₂_apply, smul_apply] using
    DFunLike.congr_fun (DFunLike.congr_fun h (v 0)) (v 1)

end RankTwo

end LinearMap

namespace TauCeti

open Matrix

universe u

variable (k : Type u)

namespace Matrix

/-- Multiplication by a square matrix scales the standard-basis determinant form by its
determinant. This is `AlternatingMap.compLinearMap_eq_det_smul` at `ω = (Pi.basisFun k ι).det`,
in matrix vocabulary. -/
@[simp]
theorem detRowAlternating_mulVec [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (v : ι → ι → k) :
    Matrix.detRowAlternating (fun i => M *ᵥ v i) =
      M.det * Matrix.detRowAlternating v := by
  -- Taken from `Module.Basis.det_comp` rather than from the general law above: it lands directly
  -- in the matrix vocabulary this `simp`-normal form needs, with nothing to transport.
  simpa only [Pi.basisFun_det, Function.comp_def, Matrix.toLin'_apply, Matrix.mulVecBilin_apply,
    LinearMap.det_toLin'] using
    (Module.Basis.det_comp (Pi.basisFun k ι) (Matrix.toLin' M) v)

end Matrix

end TauCeti
