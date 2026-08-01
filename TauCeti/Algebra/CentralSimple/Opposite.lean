/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.Degree` is imported publicly: it supplies the dimension count
-- `TauCeti.Algebra.finrank_tensorProduct_mulOpposite` that the surjectivity proof below runs on,
-- and it re-exports `TauCeti.Algebra.CentralSimple.TensorProduct`, and with it the simplicity
-- instance `TauCeti.IsSimpleRing.tensorProduct` that makes `A ⊗[K] Aᵐᵒᵖ` simple -- the fact the
-- whole file rests on -- as well as `Mathlib.RingTheory.TensorProduct.Basic` (the `⊗[K]` notation
-- and the algebra structure on `A ⊗[K] Aᵐᵒᵖ`, both of which occur in the statements below) and
-- `Mathlib.Algebra.Central.Basic`, which is why none of those is imported again here.
public import TauCeti.Algebra.CentralSimple.Degree
-- `AlgHom.mulLeftRight` and `IsAzumaya` appear in the statements below.
public import Mathlib.Algebra.Azumaya.Defs
-- `TauCeti.LinearAlgebra.Matrix.ToLin` is imported publicly for the matrix half of the opposite
-- isomorphism, `TauCeti.Algebra.endAlgEquivMatrix`; it re-exports
-- `Mathlib.LinearAlgebra.Matrix.ToLin` and with it the `Matrix` occurring in the statements below.
public import TauCeti.LinearAlgebra.Matrix.ToLin
-- Non-public: the dimension count for a space of linear maps and the rank-nullity consequence that
-- an injective linear map between equidimensional spaces is surjective are used only inside proofs,
-- so downstream importers do not pay for them.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The opposite isomorphism `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Mₙ(K)`

Let `A` be a finite-dimensional central simple algebra over a field `K`, of dimension `n` over `K`.
This file proves that the **Azumaya map**

`AlgHom.mulLeftRight K A : A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A`,  `a ⊗ₜ b ↦ (x ↦ a * x * b.unop)`,

is an isomorphism, and combines it with a choice of `K`-basis of `A` to write

`A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix (Fin n) (Fin n) K`.

This is the fact that makes the class of `Aᵐᵒᵖ` the inverse of the class of `A` in the Brauer group:
the tensor product of `A` with its opposite is a full matrix algebra, hence Brauer-trivial.

The matrix size is `n = Module.finrank K A`, **not** the degree: for a central simple algebra of
degree `d` one has `Module.finrank K A = d ^ 2`, so this is `Matrix (Fin (d ^ 2)) (Fin (d ^ 2)) K`.
The dimension and degree counts this rests on are general facts about `A ⊗[K] Aᵐᵒᵖ` and live with
the rest of the degree API, as `TauCeti.Algebra.finrank_tensorProduct_mulOpposite` and
`TauCeti.Algebra.deg_tensorProduct_mulOpposite`.

## The proof

Both halves of bijectivity are cheap once the right facts are in place, and neither is a
computation with the map.

*Injectivity* is simplicity: `Aᵐᵒᵖ` is simple because `A` is, so `A ⊗[K] Aᵐᵒᵖ` is simple by
`TauCeti.IsSimpleRing.tensorProduct` (this is where centrality of `A` enters), and a ring
homomorphism out of a simple ring into a nontrivial ring is injective (`RingHom.injective`).
No finite-dimensionality is used here, and the half is stated on its own as
`TauCeti.IsSimpleRing.mulLeftRight_injective`.

*Surjectivity* is a dimension count: `A ⊗[K] Aᵐᵒᵖ` and `Module.End K A` both have dimension `n ^ 2`
over `K`, so an injective `K`-linear map between them is surjective. This is the only place
finite-dimensionality is needed, and it is essential: for an infinite-dimensional central simple
algebra the Azumaya map is injective but need not be surjective.

Centrality enters only through the first half, and it cannot be dropped there. Take `A = ℂ` over
`K = ℝ`, which is simple and finite-dimensional but not central. Then `ℂ ⊗[ℝ] ℂᵐᵒᵖ` is not simple:
multiplication `a ⊗ₜ b ↦ a * b` is an `ℝ`-algebra map onto `ℂ` whose kernel contains the nonzero
element `Complex.I ⊗ₜ 1 - 1 ⊗ₜ Complex.I`. Injectivity genuinely fails, and so does the conclusion:
because `ℂ` is commutative the Azumaya map has image the scalar multiplications, a `2`-dimensional
subalgebra of the `4`-dimensional `Module.End ℝ ℂ`.

## Main results

* `TauCeti.IsSimpleRing.mulLeftRight_injective`: **the Azumaya map of a central simple algebra is
  injective**, with no finiteness hypothesis, and
  `TauCeti.IsSimpleRing.mulLeftRight_bijective`: **for a finite-dimensional one it is bijective**,
  with its packaging `TauCeti.IsSimpleRing.isAzumaya`: such an algebra is an Azumaya algebra over
  its base field.
* `TauCeti.Algebra.tensorOpAlgEquivEnd`: the resulting isomorphism
  `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A`.
* `TauCeti.Algebra.tensorOpAlgEquivMatrix`: **the opposite isomorphism**
  `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix (Fin n) (Fin n) K` for any `n` with `Module.finrank K A = n`.

The real quaternions run all of this concretely in
`TauCeti/Algebra/CentralSimple/Quaternion.lean`.

## Implementation notes

`TauCeti.IsSimpleRing.isAzumaya` is deliberately **not** an instance. Mathlib's
`Algebra.IsCentral.instIsAzumaya` goes the other way, deducing `Algebra.IsCentral K A` from
`IsAzumaya K A`; registering the converse as an instance would let typeclass search cycle between
the two. Apply it with `haveI` where an `IsAzumaya` hypothesis is wanted.

`TauCeti.Algebra.tensorOpAlgEquivMatrix` takes the matrix size as a parameter `n` together with a
proof `Module.finrank K A = n`, rather than using `Module.finrank K A` itself. Instantiating `n` at
`Module.finrank K A` and `hn` at `rfl` recovers the unparametrized form, while the parametrized one
is what makes the quaternion example (where the dimension is `4` on the nose) come out without
reindexing. Its second half is `TauCeti.Algebra.endAlgEquivMatrix`, which involves neither an
algebra structure nor central simplicity and so lives with the linear algebra, in
`TauCeti/LinearAlgebra/Matrix/ToLin.lean`; nothing downstream should depend on which basis it
chooses.

## References

This implements the fourth bullet of Layer 4 ("The opposite isomorphism") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
which also lists it among the Brauer-triviality prerequisites of Layer 6. See P. Gille,
T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.4, and R. S. Pierce,
*Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-! ### The Azumaya map is bijective -/

namespace IsSimpleRing

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
  [IsSimpleRing A]

/-- **The Azumaya map of a central simple algebra is injective**: `A ⊗[K] Aᵐᵒᵖ` is a simple ring
(`TauCeti.IsSimpleRing.tensorProduct`, which is where centrality of `A` enters), and a ring
homomorphism out of a simple ring into a nontrivial ring is injective.

No finite-dimensionality is used, and none should be added: this half of
`TauCeti.IsSimpleRing.mulLeftRight_bijective` holds for an infinite-dimensional central simple
algebra too, where the Azumaya map is injective but need not be surjective. -/
theorem mulLeftRight_injective : Function.Injective (AlgHom.mulLeftRight K A) :=
  RingHom.injective (AlgHom.mulLeftRight K A : (A ⊗[K] Aᵐᵒᵖ) →+* Module.End K A)

variable [FiniteDimensional K A]

/-- **The Azumaya map of a finite-dimensional central simple algebra is bijective**: for `A` central
simple and finite-dimensional over a field `K`, the map

`AlgHom.mulLeftRight K A : A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A`,  `a ⊗ₜ b ↦ (x ↦ a * x * b.unop)`,

is a bijection.

Injectivity is `TauCeti.IsSimpleRing.mulLeftRight_injective`, which holds for any central simple
`A`, finite-dimensional or not. Finite-dimensionality is used only for surjectivity, where it makes
the two sides equidimensional `K`-vector spaces. -/
theorem mulLeftRight_bijective : Function.Bijective (AlgHom.mulLeftRight K A) := by
  have hdim : Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
    rw [Algebra.finrank_tensorProduct_mulOpposite, Module.finrank_linearMap, sq]
  exact ⟨mulLeftRight_injective K A, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (AlgHom.mulLeftRight K A).toLinearMap)).mp (mulLeftRight_injective K A)⟩

/-- **A finite-dimensional central simple algebra is an Azumaya algebra** over its base field.

This is not an instance. Mathlib's `Algebra.IsCentral.instIsAzumaya` deduces `Algebra.IsCentral K A`
from `IsAzumaya K A`, so making the converse an instance would let typeclass search cycle between
the two; use `haveI := TauCeti.IsSimpleRing.isAzumaya K A` where an `IsAzumaya` hypothesis is
wanted. -/
theorem isAzumaya : IsAzumaya K A where
  bij := mulLeftRight_bijective K A

end IsSimpleRing

/-! ### The opposite isomorphism -/

namespace Algebra

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
  [IsSimpleRing A] [FiniteDimensional K A]

/-- The Azumaya map of a finite-dimensional central simple algebra, promoted to an isomorphism
`A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A`. Its value on a pure tensor is
`TauCeti.Algebra.tensorOpAlgEquivEnd_tmul_apply`. -/
noncomputable def tensorOpAlgEquivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight K A) (IsSimpleRing.mulLeftRight_bijective K A)

@[simp]
theorem tensorOpAlgEquivEnd_tmul_apply (a : A) (b : Aᵐᵒᵖ) (x : A) :
    tensorOpAlgEquivEnd K A (a ⊗ₜ[K] b) x = a * x * b.unop :=
  AlgHom.mulLeftRight_apply K A a b x

/-- **The opposite isomorphism.** A finite-dimensional central simple `K`-algebra `A` of dimension
`n` satisfies `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix (Fin n) (Fin n) K`: the tensor product of a central simple
algebra with its opposite is a full matrix algebra, which is what makes the Brauer class of `Aᵐᵒᵖ`
the inverse of that of `A`.

The size is the **dimension** `n = Module.finrank K A`, not the degree `TauCeti.Algebra.deg K A`;
the two are related by `TauCeti.Algebra.deg_sq`, and the resulting degree count is
`TauCeti.Algebra.deg_tensorProduct_mulOpposite`. The dimension is taken as a parameter so that a
caller who already knows it as a numeral, as in
`TauCeti.Quaternion.tensorSelfAlgEquivMatrix`, gets that numeral back with no reindexing.

This is `TauCeti.Algebra.tensorOpAlgEquivEnd` followed by `TauCeti.Algebra.endAlgEquivMatrix`, as
recorded by `TauCeti.Algebra.tensorOpAlgEquivMatrix_apply`. -/
noncomputable def tensorOpAlgEquivMatrix {n : ℕ} (hn : Module.finrank K A = n) :
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  (tensorOpAlgEquivEnd K A).trans (endAlgEquivMatrix K A hn)

/-- The opposite isomorphism is the Azumaya isomorphism `TauCeti.Algebra.tensorOpAlgEquivEnd`
followed by `TauCeti.Algebra.endAlgEquivMatrix`. This is the only handle on it: which basis
`TauCeti.Algebra.endAlgEquivMatrix` chooses is deliberately opaque, so there is no lemma computing
matrix entries. Together with `TauCeti.Algebra.tensorOpAlgEquivEnd_tmul_apply` it identifies the
image of a pure tensor as the matrix of `x ↦ a * x * b.unop`. -/
@[simp]
theorem tensorOpAlgEquivMatrix_apply {n : ℕ} (hn : Module.finrank K A = n) (x : A ⊗[K] Aᵐᵒᵖ) :
    tensorOpAlgEquivMatrix K A hn x = endAlgEquivMatrix K A hn (tensorOpAlgEquivEnd K A x) :=
  AlgEquiv.trans_apply _ _ x

end Algebra

/-! ### Worked example: the base field -/

section Examples

variable (K : Type*) [Field K]

/-- The base field itself: `K ⊗[K] Kᵐᵒᵖ` is `1 × 1` matrices over `K`. -/
noncomputable example : K ⊗[K] Kᵐᵒᵖ ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
  Algebra.tensorOpAlgEquivMatrix K K (Module.finrank_self K)

end Examples

end TauCeti
