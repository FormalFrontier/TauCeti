/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.mulVecLin` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

/-!
# The identities forced by the character-lattice matrix of a special map

At the level of a root datum, a special isogeny is pinned by a square matrix `A` together with a
permutation `σ` of the root indices and a rescaling exponent `ℓ`, subject to the two equations

```text
A *ᵥ root i = ℓ i • root (σ i),    Aᵀ *ᵥ coroot (σ j) = ℓ j • coroot j
```

and, for the isogeny to square to the Frobenius, `A * A = c • 1`. Everything those equations imply
without using the root datum is collected here once, so that the per-type files record only the
tables and the equations themselves.

## Main results

* `TauCeti.transpose_mul_transpose_of_mul_self_eq_smul_one`,
  `TauCeti.mulVec_mulVec_of_mul_self_eq_smul_one` and
  `TauCeti.mulVecLin_comp_mulVecLin_of_mul_self_eq_smul_one`: a matrix squaring to `c • 1` acts as
  multiplication by `c` when applied twice, on the transposed matrix, on vectors, and as a linear
  map.
* `TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul`: the two displayed equations force the Cartan
  integers, computed as dot products, to transform by `ℓ i ⟨root (σ i), coroot (σ j)⟩ =
  ℓ j ⟨root i, coroot j⟩`.

## References

The lattice-level special-isogeny equations these lemmas abstract are those of R. Steinberg,
*Endomorphisms of Linear Algebraic Groups*, §11. The statements themselves are the type-independent
core of the per-type files
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/SpecialMap.lean` and
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/G2/SpecialMap.lean`, where they were
first proved.
-/

namespace TauCeti

open _root_.Matrix

variable {n : Type*} [Fintype n] {R : Type*} [CommRing R] {A : Matrix n n R} {c : R}

section DecidableEq

variable [DecidableEq n]

/-- If a matrix squares to a scalar matrix, then so does its transpose. -/
theorem transpose_mul_transpose_of_mul_self_eq_smul_one (h : A * A = c • (1 : Matrix n n R)) :
    Aᵀ * Aᵀ = c • (1 : Matrix n n R) := by
  rw [← transpose_mul, h, transpose_smul, transpose_one]

/-- A matrix squaring to `c • 1` rescales every vector by `c` when applied twice. -/
theorem mulVec_mulVec_of_mul_self_eq_smul_one (h : A * A = c • (1 : Matrix n n R)) (x : n → R) :
    A *ᵥ (A *ᵥ x) = c • x := by
  rw [mulVec_mulVec, h, smul_mulVec, one_mulVec]

/-- The square relation of a matrix squaring to `c • 1`, as an equality of linear maps. -/
theorem mulVecLin_comp_mulVecLin_of_mul_self_eq_smul_one (h : A * A = c • (1 : Matrix n n R)) :
    A.mulVecLin ∘ₗ A.mulVecLin = c • (LinearMap.id : (n → R) →ₗ[R] (n → R)) := by
  refine LinearMap.ext fun x => ?_
  simpa only [LinearMap.comp_apply, mulVecLin_apply, LinearMap.smul_apply, LinearMap.id_apply]
    using mulVec_mulVec_of_mul_self_eq_smul_one h x

end DecidableEq

/-- **The Cartan integers transform by the rule the special-isogeny equations force.** If a matrix
`A` carries each member of a family `v` to a rescaled member, and its transpose carries the
correspondingly indexed member of a family `w` back with the same scalar, then the dot products of
the two families satisfy `ℓ i ⟨v (σ i), w (σ j)⟩ = ℓ j ⟨v i, w j⟩`. Applied to the roots and
coroots of a pinned root datum, this is the identity that separates a special isogeny from a
diagram automorphism, for which every `ℓ` is `1`. -/
theorem mul_dotProduct_eq_of_mulVec_eq_smul {ι : Type*} {σ : ι → ι} {l : ι → R}
    {v w : ι → (n → R)} (hv : ∀ i, A *ᵥ v i = l i • v (σ i))
    (hw : ∀ j, Aᵀ *ᵥ w (σ j) = l j • w j) (i j : ι) :
    l i * (v (σ i) ⬝ᵥ w (σ j)) = l j * (v i ⬝ᵥ w j) := by
  have key : (A *ᵥ v i) ⬝ᵥ w (σ j) = v i ⬝ᵥ (Aᵀ *ᵥ w (σ j)) := by
    rw [dotProduct_mulVec, vecMul_transpose]
  rwa [hv, hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at key

end TauCeti
