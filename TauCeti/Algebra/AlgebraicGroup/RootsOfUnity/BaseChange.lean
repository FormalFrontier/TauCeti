/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic

/-!
# Base change of the roots-of-unity group scheme

This file records the base-changed functor-of-points calculation for the diagonalizable group
`μ_n = D(Multiplicative (ZMod n))`. If `K` is a `k`-algebra and `A` is a commutative
`K`-algebra, then the `A`-points of the base-changed Hopf algebra
`K ⊗[k] k[Multiplicative (ZMod n)]` are the usual subgroup `rootsOfUnity n A`.

The construction first restricts a base-changed point along
`1 ⊗ _ : k[Multiplicative (ZMod n)] → K ⊗[k] k[Multiplicative (ZMod n)]`, then applies
`RootsOfUnityGroup.pointsMulEquiv`.
The characteristic lemmas spell out that the equivalence reads a point on the base-changed
standard generator `1 ⊗ single (ofAdd 1) 1`, how the inverse point evaluates on scalar
multiples of that generator.

This is part of the ReductiveGroups roadmap worked examples: `μ_n = D(ℤ/n)` in the
diagonalizable-groups lane, together with the Layer 0 base-change target for Hopf algebras and
their functors of points.

## Main declarations

* `TauCeti.RootsOfUnityGroup.baseChangePointsMulEquiv`: the multiplicative equivalence from
  base-changed `μ_n` points to `rootsOfUnity n A`.
* `TauCeti.RootsOfUnityGroup.baseChangePointsMulEquiv_apply`: the equivalence reads a point
  by evaluating it on `1 ⊗ single (generator n) 1`.
* `TauCeti.RootsOfUnityGroup.baseChangePointsMulEquiv_symm_apply_tmul_single_generator`: the
  inverse equivalence evaluates scalar multiples of the base-changed generator.
* `TauCeti.RootsOfUnityGroup.baseChangePointsMulEquiv_symm_apply_single_generator`: the
  inverse equivalence sends a root of unity to the base-changed point taking the standard
  generator to it.
## References

The generic algebra base-change calculation is Tau Ceti's
`AlgHom.baseChangePointsMulEquiv`, and the roots-of-unity points calculation is
`RootsOfUnityGroup.pointsMulEquiv`. This specialization follows the API pattern of
`DiagonalizableGroup.baseChangePointsMulEquiv` in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace RootsOfUnityGroup

universe u v w

variable {k : Type u} {K : Type v} {A : Type w}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The `A`-points of the base change `K ⊗[k] k[Multiplicative (ZMod n)]` of `μ_n` are
the subgroup of `n`th roots of unity in `A`.

The source is the convolution group of `K`-algebra maps out of the base-changed Hopf algebra.
The target is Mathlib's subgroup of units whose `n`th power is one. -/
noncomputable def baseChangePointsMulEquiv (n : ℕ) :
    WithConv (K ⊗[k] MonoidAlgebra k (Multiplicative (ZMod n)) →ₐ[K] A) ≃*
      rootsOfUnity n A :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := MonoidAlgebra k (Multiplicative (ZMod n))) (R := A)).symm.trans
    (RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) n)

/-- The base-changed roots-of-unity points equivalence reads a point by evaluating it on the
base-changed standard generator `1 ⊗ single (ofAdd 1) 1`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply (n : ℕ)
    (f : WithConv (K ⊗[k] MonoidAlgebra k (Multiplicative (ZMod n)) →ₐ[K] A)) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) n f : Aˣ) : A) =
      f.ofConv (1 ⊗ₜ[k] MonoidAlgebra.single (generator n) (1 : k)) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, pointsMulEquiv_apply,
    AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed roots-of-unity points equivalence evaluates scalar multiples of
the standard generator by scalar multiplication of the chosen root of unity. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply_tmul_single_generator (n : ℕ)
    (ζ : rootsOfUnity n A) (s : K) (r : k) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) n).symm ζ).ofConv
        (s ⊗ₜ[k] MonoidAlgebra.single (generator n) r) =
      s • (r • ((ζ : Aˣ) : A)) := by
  rw [baseChangePointsMulEquiv, MulEquiv.symm_trans_apply]
  -- After unfolding the transposed equivalence, Lean still sees the inverse result through the
  -- `WithConv` coercion; this `change` exposes exactly the generic base-change point to rewrite.
  change (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := MonoidAlgebra k (Multiplicative (ZMod n))) (R := A)
        ((pointsMulEquiv (R := k) (A := A) n).symm ζ)).ofConv
      (s ⊗ₜ[k] MonoidAlgebra.single (generator n) r) =
    s • (r • ((ζ : Aˣ) : A))
  rw [AlgHom.baseChangePointsMulEquiv_apply_tmul]
  rw [pointsMulEquiv_symm_apply_single_generator_smul]

/-- The inverse base-changed roots-of-unity points equivalence takes the standard generator to
the chosen root of unity. -/
lemma baseChangePointsMulEquiv_symm_apply_single_generator (n : ℕ) (ζ : rootsOfUnity n A) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) n).symm ζ).ofConv
        (1 ⊗ₜ[k] MonoidAlgebra.single (generator n) (1 : k)) =
      ((ζ : Aˣ) : A) := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_single_generator]
  simp

end RootsOfUnityGroup

end TauCeti
