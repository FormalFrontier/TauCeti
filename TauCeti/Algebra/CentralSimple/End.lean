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
public import Mathlib.Algebra.Module.LinearMap.End
-- Non-public: the matrix presentation `algEquivMatrix (Module.finBasis K V)` and the two matrix
-- facts it transports, `Algebra.IsCentral.matrix` and `IsSimpleRing.matrix`, are used only inside
-- proofs, as is the transport `IsSimpleRing.of_ringEquiv` itself and the dimension count
-- `Module.finrank_linearMap`.
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The endomorphism algebra of a finite-dimensional vector space is central simple

For a nonzero finite-dimensional vector space `V` over a field `K`, the algebra `Module.End K V` is
central simple over `K`: it is the untwisted, "split" central simple algebra of degree
`Module.finrank K V`. This file records that as the two instances typeclass inference needs, so
that `Module.End K V` is available wherever a central simple algebra is asked for, and computes its
degree.

Nothing here is a new theorem. A choice of basis turns `Module.End K V` into the matrix algebra
`Matrix (Fin n) (Fin n) K` with `n = Module.finrank K V` (Mathlib's `algEquivMatrix`), and Mathlib
already knows that a matrix algebra over a central algebra is central (`Algebra.IsCentral.matrix`)
and that a matrix algebra over a simple ring is simple (`IsSimpleRing.matrix`); both facts are
transported back along that isomorphism. The content is that the transport is available to instance
search, which it is not while the isomorphism has to be produced by hand from a basis.

Finite-dimensionality is essential for simplicity, and only for simplicity: on an
infinite-dimensional `V` the endomorphisms of finite rank form a proper nonzero two-sided ideal of
`Module.End K V`, whereas the centre is the scalars in any dimension. The centrality instance below
nonetheless carries the same hypotheses as the simplicity one, since it is proved by the same
transport along a finite basis; the infinite-dimensional statement would need a different argument,
along the lines of Mathlib's `LinearMap.commute_transvections_iff_of_basis`, and is not needed here.

## Main results

* `TauCeti.IsSimpleRing.moduleEnd` and `TauCeti.Algebra.IsCentral.moduleEnd`: `Module.End K V` is a
  simple ring and a central `K`-algebra, for `V` a nonzero finite-dimensional `K`-vector space.
* `TauCeti.Algebra.deg_moduleEnd`: its degree is `Module.finrank K V`. Equivalently
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

/-- The chosen matrix presentation of `Module.End K V`, in the basis `Module.finBasis K V`. Both
instances below are transported along it; nothing downstream depends on the choice. -/
private noncomputable def endAlgEquivFinBasis :
    Module.End K V ≃ₐ[K] Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
  algEquivMatrix (Module.finBasis K V)

private theorem nonempty_fin_finrank : Nonempty (Fin (Module.finrank K V)) :=
  ⟨⟨0, Module.finrank_pos⟩⟩

/-- **The endomorphism algebra of a nonzero finite-dimensional vector space is a simple ring.**

Finite-dimensionality cannot be dropped: on an infinite-dimensional `V` the finite-rank
endomorphisms are a proper nonzero two-sided ideal. -/
instance IsSimpleRing.moduleEnd : IsSimpleRing (Module.End K V) :=
  have := nonempty_fin_finrank K V
  .of_ringEquiv (endAlgEquivFinBasis K V).symm.toRingEquiv inferInstance

/-- **The endomorphism algebra of a nonzero finite-dimensional vector space is central.**

Mathlib's `Algebra.IsCentral.of_algEquiv` is not usable here: it places the two algebras in a
single universe, while `Module.End K V` lives in the universe of `V` and its matrix presentation
in the universe of `K`. The proof is the same transport, run by hand. -/
instance Algebra.IsCentral.moduleEnd : Algebra.IsCentral K (Module.End K V) where
  out f hf := by
    obtain ⟨c, hc⟩ := (_root_.Algebra.IsCentral.mem_center_iff (D := Matrix
      (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) K).mp
      ((MulEquivClass.apply_mem_center_iff (endAlgEquivFinBasis K V)).mpr hf)
    exact _root_.Algebra.mem_bot.mpr
      ⟨c, by simpa using congrArg (endAlgEquivFinBasis K V).symm hc.symm⟩

end Nontrivial

/-- The degree of the split central simple algebra `Module.End K V` is the dimension of `V`. This
is the degree-side reading of `Module.finrank_linearMap`, and it needs no hypothesis beyond
finite-dimensionality: `TauCeti.Algebra.deg` is `Nat.sqrt` of the dimension, and the dimension of
`Module.End K V` is a square whether or not `V` is nonzero. -/
@[simp]
theorem Algebra.deg_moduleEnd : deg K (Module.End K V) = Module.finrank K V :=
  deg_eq_of_finrank_eq_sq (by rw [Module.finrank_linearMap, sq])

end TauCeti
