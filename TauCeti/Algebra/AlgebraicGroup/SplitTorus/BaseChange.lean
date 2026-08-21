/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Base change of split-torus points

The rank-`σ` split torus over `k` is the diagonalizable group
`D(Multiplicative (σ →₀ ℤ))`, represented by the group algebra
`k[Multiplicative (σ →₀ ℤ)]`. This file records the base-changed functor-of-points
calculation: if `K` is a `k`-algebra and `A` is a commutative `K`-algebra, then the
convolution group of `K`-algebra maps out of
`K ⊗[k] k[Multiplicative (σ →₀ ℤ)]` is the product group `σ → Aˣ`.

The equivalence is the specialization of
`DiagonalizableGroup.baseChangePointsMulEquiv` to the free abelian character group, followed
by `freeAbelianCharEquiv`. The pointwise API reads a base-changed point on the standard
coordinate characters `1 ⊗ single (ofAdd (single i 1)) 1`, records the inverse evaluation,
and gives the finite-rank specialization.

This advances the ReductiveGroups roadmap, Layer 0 ("Base change. `K ⊗[k] A` as a Hopf
algebra over `K`") and Layer 4 ("Tori: split ... the character lattice `X*(T)`").

## Main declarations

* `TauCeti.SplitTorus.baseChangePointsMulEquiv`: the multiplicative equivalence from
  base-changed points of the rank-`σ` split torus to coordinate families `σ → Aˣ`.
* `TauCeti.SplitTorus.baseChangePointsMulEquiv_apply_coe`: the equivalence reads a point on
  the base-changed standard coordinate generator.
* `TauCeti.SplitTorus.baseChangePointsMulEquiv_symm_apply_single_one`: the inverse equivalence
  takes each standard coordinate generator to the chosen coordinate.
## References

The base-change step is Tau Ceti's `DiagonalizableGroup.baseChangePointsMulEquiv`, and the
free-abelian character calculation is Tau Ceti's `freeAbelianCharEquiv`, built from Mathlib's
`Finsupp.liftAddHom` and `zmultiplesHom`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace SplitTorus

universe u v w w'

variable {k : Type u} {K : Type v} {A : Type w} {σ : Type w'}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The `A`-points of the base change of the rank-`σ` split torus are coordinate families
`σ → Aˣ`.

The source is the convolution group of `K`-algebra maps out of the base-changed Hopf algebra
`K ⊗[k] k[Multiplicative (σ →₀ ℤ)]`; the target is the product group of units of the value
algebra. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) →ₐ[K] A) ≃* (σ → Aˣ) :=
  (DiagonalizableGroup.baseChangePointsMulEquiv (k := k) (K := K) (A := A)
      (G := Multiplicative (σ →₀ ℤ))).trans freeAbelianCharEquiv

/-- The base-changed split-torus points equivalence reads a point by evaluating it on the
base-changed standard coordinate generator indexed by `i`. -/
@[simp]
theorem baseChangePointsMulEquiv_apply_coe
    (f : WithConv (K ⊗[k] MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) →ₐ[K] A))
    (i : σ) :
    (baseChangePointsMulEquiv f i : A) =
      f.ofConv (1 ⊗ₜ[k]
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) (1 : k)) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, freeAbelianCharEquiv_apply,
    DiagonalizableGroup.baseChangePointsMulEquiv_apply_coe]

/-- The inverse base-changed split-torus points equivalence sends a pure tensor
`s ⊗ single (ofAdd m) r` to the scalar multiple of the monomial in the chosen coordinates
with exponent vector `m`. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_single (c : σ → Aˣ) (s : K)
    (m : σ →₀ ℤ) (r : k) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (σ := σ)).symm c).ofConv
        (s ⊗ₜ[k] MonoidAlgebra.single (Multiplicative.ofAdd m) r) =
      s • (r • ((m.prod fun i n => c i ^ n : Aˣ) : A)) := by
  rw [baseChangePointsMulEquiv, MulEquiv.symm_trans_apply,
    DiagonalizableGroup.baseChangePointsMulEquiv_symm_apply_tmul_single]
  simp only [freeAbelianCharEquiv_symm_apply_ofAdd]

/-- The inverse base-changed split-torus points equivalence takes the standard coordinate
generator indexed by `i` to the chosen coordinate `c i`. -/
theorem baseChangePointsMulEquiv_symm_apply_single_one (c : σ → Aˣ) (i : σ) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (σ := σ)).symm c).ofConv
        (1 ⊗ₜ[k] MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) (1 : k)) =
      (c i : A) := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_single]
  simp

/-- The base-changed rank-`n` split torus has `A`-points `Fin n → Aˣ = (Aˣ)ⁿ`. -/
noncomputable example (n : ℕ) :
    WithConv (K ⊗[k] MonoidAlgebra k (Multiplicative (Fin n →₀ ℤ)) →ₐ[K] A) ≃*
      (Fin n → Aˣ) :=
  baseChangePointsMulEquiv

end SplitTorus

end TauCeti
