/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the classes occurring in the exported statement. `IsIsotypic` is the hypothesis, along
-- with the semisimplicity and finiteness of the module, and `IsSimpleRing (Module.End R M)` is the
-- conclusion.
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Defs
-- Non-public: used only inside the proof. The matrix presentation of the endomorphism ring of a
-- power, transport of simplicity along a ring isomorphism, and simplicity of a matrix ring over a
-- division ring are all internal to the argument below; no exported statement mentions a matrix.
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The endomorphism ring of an isotypic module is simple

A semisimple module `M` all of whose simple submodules are isomorphic to one another
(`IsIsotypic R M`) and which is finite over `R` is a finite power `Sⁿ` of a single simple module,
by Mathlib's `IsIsotypic.linearEquiv_fun`.  Its endomorphism ring is therefore the matrix ring
`Matₙ(End_R S)` over the division ring supplied by Schur's lemma, and a matrix ring of nonzero
size over a division ring is simple.  So

  `IsSimpleRing (Module.End R M)`

for every nonzero such `M`, with no hypothesis on `R` beyond what makes `M` semisimple.

This is the shape in which Artin--Wedderburn uniqueness uses endomorphism rings: over a semisimple
ring the isotypic components of the regular module are exactly the modules this applies to, so
`End_R R` is a product of simple rings indexed by them, one factor per Wedderburn block.  See
`TauCeti/RingTheory/Semisimple/Wedderburn/Blocks.lean`.

## Main results

* `TauCeti.isSimpleRing_moduleEnd_of_isIsotypic`: **the endomorphism ring of a nonzero finite
  isotypic semisimple module is simple.**

## Implementation notes

Nonzero-ness of `M` is what makes the matrix size `n` nonzero, and it cannot be dropped: for
`M = 0` the ring `Module.End R M` is trivial and a trivial ring is not simple.

## References

This is the module-theoretic engine behind the Layer 2 uniqueness statements of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **The endomorphism ring of a nonzero finite isotypic semisimple module is simple.**

Writing `M` as a power `Sⁿ` of a simple module presents `End_R M` as the matrix ring
`Matₙ(End_R S)` over the division ring `End_R S` of Schur's lemma, and `n ≠ 0` because `M ≠ 0`.

The ring `R` is arbitrary: only the module is asked to be semisimple, isotypic and finite.  Over a
simple Artinian ring every module is isotypic, which is the specialization
`TauCeti.IsSimpleRing.moduleEnd`. -/
theorem isSimpleRing_moduleEnd_of_isIsotypic [IsSemisimpleModule R M] [Module.Finite R M]
    [Nontrivial M] (h : IsIsotypic R M) : IsSimpleRing (Module.End R M) := by
  classical
  obtain ⟨n, hn, S, hS, ⟨e⟩⟩ := h.linearEquiv_fun
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn.ne⟩⟩
  -- Schur's lemma makes `End_R S` a division ring, hence a simple ring, hence so is `Matₙ` of it.
  exact IsSimpleRing.of_ringEquiv
    (e.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin n) R S)).symm inferInstance

end TauCeti
