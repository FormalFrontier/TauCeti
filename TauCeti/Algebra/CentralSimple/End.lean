/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.Degree` is imported publicly: `TauCeti.Algebra.deg` appears in the
-- statement of `TauCeti.Algebra.deg_moduleEnd`. It also re-exports `Mathlib.Algebra.Central.Basic`
-- and `Mathlib.RingTheory.SimpleRing.Basic`, hence `Algebra.IsCentral` and `IsSimpleRing`, which is
-- why neither is imported again here.
public import TauCeti.Algebra.CentralSimple.Degree
-- Public: Mathlib's `Algebra.IsCentral` instance for the endomorphisms of a free module is the
-- centrality half of "central simple", so it has to reach everywhere `Module.End K V` is asked for
-- as a central simple algebra. It also re-exports `Mathlib.Algebra.Module.LinearMap.End`, hence
-- `Module.End` itself, which is why that is not imported again here.
public import Mathlib.Algebra.Central.End
-- Non-public: the matrix presentation `algEquivMatrix (Module.finBasis K V)` and the matrix fact it
-- transports, `IsSimpleRing.matrix`, are used only inside a proof, as is the transport
-- `IsSimpleRing.of_ringEquiv` itself and the dimension count `Module.finrank_linearMap`.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The endomorphism algebra of a finite-dimensional vector space is central simple

For a nonzero finite-dimensional vector space `V` over a field `K`, the algebra `Module.End K V` is
central simple over `K`: it is the untwisted, "split" central simple algebra of degree
`Module.finrank K V`. Centrality is already Mathlib's: its `Algebra.IsCentral` instance in
`Mathlib.Algebra.Central.End` covers the endomorphisms of any free module. This file supplies the
missing half, simplicity, as the instance typeclass inference needs, so that `Module.End K V` is
available wherever a central simple algebra is asked for, and computes the degree.

Simplicity is not a new theorem. A choice of basis turns `Module.End K V` into the matrix algebra
`Matrix (Fin n) (Fin n) K` with `n = Module.finrank K V` (Mathlib's `algEquivMatrix`), and Mathlib
already knows that a matrix algebra over a simple ring is simple (`IsSimpleRing.matrix`); that fact
is transported back along the isomorphism. The content is that the transport is available to
instance search, which it is not while the isomorphism has to be produced by hand from a basis.

Finite-dimensionality is essential for simplicity: on an infinite-dimensional `V` the endomorphisms
of finite rank form a proper nonzero two-sided ideal of `Module.End K V`. The centre, by contrast,
is the scalars in any dimension, which is why Mathlib's centrality instance carries no finiteness
hypothesis.

## Main results

* `TauCeti.IsSimpleRing.moduleEnd`: `Module.End K V` is a simple ring, for `V` a nonzero
  finite-dimensional `K`-vector space.
* `TauCeti.Algebra.deg_moduleEnd`: the degree of `Module.End K V` is `Module.finrank K V`, for any
  finite-dimensional `V` -- nonzero or not, since the degree is defined for every algebra whose
  dimension is a square. Equivalently
  `Module.finrank K (Module.End K V) = (Module.finrank K V) ^ 2`, which is Mathlib's
  `Module.finrank_linearMap`; the point of stating it degree-side is that
  `TauCeti.Algebra.deg` is the invariant that composes, so a split algebra of degree `d` can be
  compared with a general central simple algebra of degree `d`.

## References

* [Semisimple algebras, Artin-Wedderburn, and the structure of their modules roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
  Layers 4 and 6.
* R. S. Pierce, *Associative Algebras*, Springer GTM 88 (1982), Chapter 12.
-/

public section

universe u v

namespace TauCeti

variable (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

section Nontrivial

variable [Nontrivial V]

/-- **The endomorphism algebra of a nonzero finite-dimensional vector space is a simple ring.**

The proof is the transport of `IsSimpleRing.matrix` along the matrix presentation
`algEquivMatrix (Module.finBasis K V)`; nothing downstream depends on that choice of basis.

Finite-dimensionality cannot be dropped: on an infinite-dimensional `V` the finite-rank
endomorphisms are a proper nonzero two-sided ideal. -/
instance IsSimpleRing.moduleEnd : IsSimpleRing (Module.End K V) :=
  have : Nonempty (Fin (Module.finrank K V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  .of_ringEquiv (algEquivMatrix (Module.finBasis K V)).symm.toRingEquiv inferInstance

end Nontrivial

/-- The degree of the endomorphism algebra `Module.End K V` is the dimension of `V`. This is the
degree-side reading of `Module.finrank_linearMap`, and it needs no hypothesis beyond
finite-dimensionality: `TauCeti.Algebra.deg` is `Nat.sqrt` of the dimension, and the dimension of
`Module.End K V` is a square whether or not `V` is nonzero. It is the degree of a *split central
simple* algebra exactly when `V` is nonzero, which is the extra hypothesis
`TauCeti.IsSimpleRing.moduleEnd` carries; for `V = 0` the ring `Module.End K V` is trivial, hence
not simple, and both sides read `0`. -/
@[simp]
theorem Algebra.deg_moduleEnd : deg K (Module.End K V) = Module.finrank K V :=
  deg_eq_of_finrank_eq_sq (by rw [Module.finrank_linearMap, sq])

end TauCeti
