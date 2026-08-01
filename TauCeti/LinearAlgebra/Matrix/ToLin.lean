/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Module.End`, `Matrix` and `algEquivMatrix` occur in the statement and the body below; this is
-- also the Mathlib file that `algEquivMatrix` itself lives in.
public import Mathlib.LinearAlgebra.Matrix.ToLin
-- `FiniteDimensional` and `Module.finrank` occur in the statement, and
-- `Module.finBasisOfFinrankEq` in the body.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The endomorphism algebra of a finite-dimensional vector space, as matrices of a known size

Mathlib's `algEquivMatrix` turns `Module.End K M` into matrices indexed by the index type of a
chosen basis of `M`. This file records the form of it that is wanted when the *dimension* of `M` is
known but no particular basis is: for `Module.finrank K M = n`, an isomorphism

`Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K`.

## Main results

* `TauCeti.Algebra.endAlgEquivMatrix`: the above, read off the basis
  `Module.finBasisOfFinrankEq`.

It is used to turn the Azumaya isomorphism of a finite-dimensional central simple algebra into a
matrix algebra in `TauCeti/Algebra/CentralSimple/Opposite.lean`.
-/

public section

namespace TauCeti

namespace Algebra

variable (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A `K`-vector space `M` of dimension `n` has `Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K`,
read off a chosen `K`-basis of `M`.

This is Mathlib's `algEquivMatrix` at the basis `Module.finBasisOfFinrankEq`, named here because it
is wanted wherever a finite-dimensional endomorphism algebra has to be turned into matrices of a
known size -- in particular as the second half of the opposite isomorphism
`TauCeti.Algebra.tensorOpAlgEquivMatrix`, which the roadmap asks for separately.

The basis is a choice, and nothing downstream should depend on which one it is; there is
deliberately no lemma computing the matrix entries. -/
noncomputable def endAlgEquivMatrix {n : ℕ} (hn : Module.finrank K M = n) :
    Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  algEquivMatrix (Module.finBasisOfFinrankEq K M hn)

end Algebra

end TauCeti
