/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

public section

/-!
# The identity forced by the character-lattice matrix of a special map

At the level of a root datum, a special isogeny is pinned by a square matrix `A` together with a
permutation `σ` of the root indices and a rescaling exponent `ℓ`, subject to the two equations

```text
A *ᵥ root i = ℓ i • root (σ i),    Aᵀ *ᵥ coroot (σ j) = ℓ j • coroot j
```

The Cartan-integer identity that these equations imply without using the root datum is collected
here once, so that the per-type files record only the tables and the equations themselves.

## Main results

* `TauCeti.mul_dotProduct_eq_of_mulVec_eq_smul`: the two displayed equations force the Cartan
  integers, computed as dot products, to transform by `ℓ i ⟨root (σ i), coroot (σ j)⟩ =
  ℓ j ⟨root i, coroot j⟩`.

## References

The lattice-level special-isogeny equations this lemma abstracts are those of R. Steinberg,
*Endomorphisms of Linear Algebraic Groups*, §11. The statement is the type-independent
core of the per-type files
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/SpecialMap.lean` and
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/G2/SpecialMap.lean`, where they were
first proved.
-/

namespace TauCeti

open _root_.Matrix

variable {n : Type*} [Fintype n] {R : Type*} [CommSemiring R] {A : Matrix n n R}

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
