/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The first three imports are public because this module is where the scalar extension of a central
-- simple algebra is assembled and it re-exports the pieces. `TauCeti.Algebra.deg` occurs in the
-- statement of `TauCeti.Algebra.deg_baseChange` and `TauCeti.Algebra.CentralSimple.Degree`
-- re-exports the simplicity of a tensor product; `TauCeti.Algebra.Central.BaseChange` supplies the
-- centrality instance that makes `L ⊗[K] A` central simple over `L` visible to instance search from
-- this import alone; `TauCeti.Algebra.TensorProduct.BaseChange` supplies the compatibility of the
-- scalar extension with `⊗` and with `ᵐᵒᵖ`.
public import TauCeti.Algebra.Central.BaseChange
public import TauCeti.Algebra.CentralSimple.Degree
public import TauCeti.Algebra.TensorProduct.BaseChange
-- Public: the two-sided-ideal operations occur in the base-change API below.
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
-- Non-public: none of these appears in the type of an exported declaration.
-- `Module.finrank_baseChange` is used only inside the proof of `TauCeti.Algebra.deg_baseChange`,
-- and the complex numbers and the real quaternions only by the worked examples at the end of the
-- file (`TauCeti.Algebra.Central.Quaternion` re-exports `Mathlib.Algebra.Quaternion`, hence the
-- `ℍ[·]` notation there).
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import TauCeti.Algebra.Central.Quaternion

/-!
# Base change preserves central simplicity

Let `A` be a central simple algebra over a field `K` and let `L / K` be a field extension. This file
assembles the statement that the scalar extension `L ⊗[K] A` is central simple *over `L`*, and adds
the degree bookkeeping that goes with it.

Both halves are already available. Simplicity is a statement about `L ⊗[K] A` as a ring, so
`TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` applies with `L` the simple factor and `A`
the central simple one; centrality over `L` is `TauCeti.Algebra.IsCentral.baseChange`, in
`TauCeti/Algebra/Central/BaseChange.lean`. Both are instances, so instance search sees `L ⊗[K] A` as
a central simple `L`-algebra with no glue at all.

## Main results

* `TwoSidedIdeal.baseChange`: scalar extension of a two-sided ideal.
* `IsSimpleRing.of_baseChange`: simplicity descends along a field extension.
* `TauCeti.Algebra.deg_baseChange`: base change **preserves the degree**,
  `deg L (L ⊗[K] A) = deg K A`.

Together with the centrality of `TauCeti/Algebra/Central/BaseChange.lean` and the two compatibility
equivalences of `TauCeti/Algebra/TensorProduct/BaseChange.lean`, both re-exported here, this is what
will let base change descend to a homomorphism of Brauer groups: the centrality and the simplicity
say the class of `L ⊗[K] A` is defined, and the two equivalences say the assignment respects the
multiplication and the inversion of classes.

## Implementation notes

`TauCeti.Algebra.deg_baseChange` is read off `Module.finrank_baseChange` through the transport
lemma `TauCeti.Algebra.deg_eq_of_finrank_eq`, so it never unfolds `TauCeti.Algebra.deg`. It asks
nothing of `A` beyond being a `K`-algebra: both degrees are the integer square root of the same
dimension, so the equality does not depend on that dimension being a square, and central simplicity
is what makes it one rather than what makes the two agree.

The worked examples at the end check both directions on the two standard test cases: `ℂ ⊗[ℝ] ℍ[ℝ]`
is central simple over `ℂ` of degree `2`, while `ℂ ⊗[ℝ] ℂ` is *not* central over `ℂ`, because `ℂ` is
not central over `ℝ`. The second is the failure `TauCeti.Algebra.IsCentral.of_baseChange` detects,
and it is the reason the centrality hypothesis on `A` cannot be dropped from the forward direction.

## References

This completes, apart from the homomorphism itself, the **Base change preserves central simplicity,
then is a homomorphism** bullet of Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
The induced homomorphism of Brauer groups waits on the group structure of `BrauerGroup K`, a
separate bullet of the same layer. See P. Gille, T. Szamuely, *Central Simple Algebras and Galois
Cohomology*, Section 2.2, and R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

open scoped TensorProduct

namespace TwoSidedIdeal

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The scalar extension of a two-sided ideal. Its underlying subspace is the usual scalar
extension of the ideal regarded as a `K`-submodule. -/
noncomputable def baseChange (L : Type*) [Field L] [Algebra K L] (I : TwoSidedIdeal A) :
    TwoSidedIdeal (L ⊗[K] A) :=
  let p : Submodule K A := I.asIdeal.restrictScalars K
  TwoSidedIdeal.mk' (p.baseChange L)
    (p.baseChange L).zero_mem
    (fun hx hy => (p.baseChange L).add_mem hx hy)
    (fun hx => (p.baseChange L).neg_mem hx)
    (fun {x y} hy => by
      obtain ⟨z, rfl⟩ := hy
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa [add_mul] using (p.baseChange L).add_mem hx hy
      | tmul l a =>
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simpa [mul_add] using (p.baseChange L).add_mem hx hy
          | tmul m i =>
              refine ⟨(l * m) ⊗ₜ[K] ⟨a * i.1, ?_⟩, ?_⟩
              · exact I.mul_mem_left a i.1 i.2
              · simp [Algebra.TensorProduct.tmul_mul_tmul])
    (fun {x y} hx => by
      obtain ⟨z, rfl⟩ := hx
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa [mul_add] using (p.baseChange L).add_mem hx hy
      | tmul l a =>
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simpa [add_mul] using (p.baseChange L).add_mem hx hy
          | tmul m i =>
              refine ⟨(m * l) ⊗ₜ[K] ⟨i.1 * a, ?_⟩, ?_⟩
              · exact I.mul_mem_right i.1 a i.2
              · simp [Algebra.TensorProduct.tmul_mul_tmul])

/-- Membership in a base-changed two-sided ideal is membership in the base-changed underlying
subspace. -/
@[simp]
theorem mem_baseChange (L : Type*) [Field L] [Algebra K L] (I : TwoSidedIdeal A)
    (x : L ⊗[K] A) :
    x ∈ baseChange L I ↔ x ∈ (I.asIdeal.restrictScalars K).baseChange L := by
  simp [baseChange]

private theorem baseChange_injective (L : Type*) [Field L] [Algebra K L] :
    Function.Injective (baseChange L : TwoSidedIdeal A → TwoSidedIdeal (L ⊗[K] A)) := by
  intro I J h
  have hsub : (I.asIdeal.restrictScalars K).baseChange L =
      (J.asIdeal.restrictScalars K).baseChange L := by
    ext x
    rw [← mem_baseChange L I, ← mem_baseChange L J, h]
  have hrestrict := (Submodule.baseChange_inj (A := L)).mp hsub
  ext x
  exact SetLike.ext_iff.mp hrestrict x

end TwoSidedIdeal

namespace IsSimpleRing

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
  [Ring A] [Algebra K A] [Nontrivial A]

/-- Simplicity descends along a field extension: if the scalar extension of a nontrivial algebra
is a simple ring, then the original algebra is a simple ring. -/
theorem of_baseChange (h : IsSimpleRing (L ⊗[K] A)) : IsSimpleRing A := by
  let _ := h
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  rcases IsSimpleOrder.eq_bot_or_eq_top
      (TwoSidedIdeal.baseChange (K := K) L I) with hI | hI
  · left
    exact TwoSidedIdeal.baseChange_injective (K := K) L (by ext x; rw [hI]; simp)
  · right
    exact TwoSidedIdeal.baseChange_injective (K := K) L (by ext x; rw [hI]; simp)

end IsSimpleRing

namespace TauCeti

namespace Algebra

/-! ### The degree of a scalar extension -/

section Degree

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (A : Type*) [Ring A] [Algebra K A]

/-- **Base change preserves the degree**: the scalar extension `L ⊗[K] A` has the same dimension
over `L` that `A` has over `K`, and the degree is the integer square root of the dimension.

No hypothesis on `A` is needed. For a finite-dimensional central simple `A` the common dimension is
a square and both sides are the honest degree (`TauCeti.Algebra.deg_sq`); in general the two sides
are equal because they are `Nat.sqrt` of the same number. -/
@[simp]
theorem deg_baseChange : deg L (L ⊗[K] A) = deg K A :=
  deg_eq_of_finrank_eq (Module.finrank_baseChange (R := L) (S := K) (M' := A))

end Degree

end Algebra

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- Complexifying the real quaternions gives a central `ℂ`-algebra: instance search finds it. -/
example : Algebra.IsCentral ℂ (ℂ ⊗[ℝ] ℍ[ℝ]) := inferInstance

/-- It is simple too, so `ℂ ⊗[ℝ] ℍ[ℝ]` is a central simple `ℂ`-algebra with no glue at all. -/
example : IsSimpleRing (ℂ ⊗[ℝ] ℍ[ℝ]) := inferInstance

/-- Complexification keeps the degree: `ℂ ⊗[ℝ] ℍ[ℝ]` has degree `2`, like `ℍ[ℝ]` itself. (Being
split over the algebraically closed `ℂ`, it is in fact `M₂(ℂ)`.) -/
example : Algebra.deg ℂ (ℂ ⊗[ℝ] ℍ[ℝ]) = 2 := by
  rw [Algebra.deg_baseChange]
  exact Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)

/-- The negative control for `TauCeti.Algebra.IsCentral.baseChange`: `ℂ ⊗[ℝ] ℂ` is not central over
`ℂ`, because `ℂ` is not central over `ℝ`. So centrality of the algebra being extended is doing real
work, and `ℂ` is a simple finite-dimensional `ℝ`-algebra that base change excludes.

The proof runs the converse `TauCeti.Algebra.IsCentral.of_baseChange` backwards: assuming
`ℂ ⊗[ℝ] ℂ` central over `ℂ` makes `ℂ` central over `ℝ`, and then `Complex.I`, central because `ℂ` is
commutative, would have to be real. -/
example : ¬ Algebra.IsCentral ℂ (ℂ ⊗[ℝ] ℂ) := fun _ => by
  have h : Algebra.IsCentral ℝ ℂ := Algebra.IsCentral.of_baseChange (K := ℝ) (L := ℂ) (A := ℂ)
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp
    (h.out (Subalgebra.mem_center_iff.mpr fun b => mul_comm b Complex.I))
  simpa using congrArg Complex.im hr

end Examples

end TauCeti
