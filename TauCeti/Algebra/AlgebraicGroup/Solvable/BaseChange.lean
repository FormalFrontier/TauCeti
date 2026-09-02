/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced

/-!
# Geometric solvability under field extension

Let `H` be a finite-type commutative Hopf algebra over a field `k`, and let `K / k` be any field
extension. Geometric solvability of the affine group represented by `H` is equivalent to geometric
solvability after extending scalars to `K`.

Preservation under scalar extension is proved in
`TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced`: finite-type point separation turns solvability
into a universal derived-word identity, which remains valid over `K`. This file proves reflection.
Choose a `k`-embedding of `AlgebraicClosure k` into `AlgebraicClosure K`. Postcomposition embeds
the original geometric point group into the points valued in `AlgebraicClosure K`, and the standard
base-change equivalence identifies the latter with the geometric point group of `K ⊗[k] H`.
Solvability passes to subgroups, giving the result.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.of_baseChange`: geometric solvability is
  reflected by arbitrary field extension.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.baseChange_iff`: geometric solvability is
  invariant under arbitrary field extension for finite-type affine groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This supplies the two-way scalar-extension interface needed to compare solvable radicals in
Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti.geometricallySolvablePointsCommHopfAlgProperty

universe u v w

noncomputable section

variable {k : Type u} [Field k]

/-- Geometric solvability is reflected by arbitrary field extension.

The point group over `AlgebraicClosure k` embeds into the point group over
`AlgebraicClosure K`, which is identified with the geometric points of the base-changed Hopf
algebra. -/
theorem of_baseChange {K : Type w} [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallySolvablePointsCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallySolvablePointsCommHopfAlgProperty k H := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH ⊢
  let _ : Algebra k (AlgebraicClosure K) :=
    Algebra.compHom (AlgebraicClosure K) (algebraMap k K)
  let ι : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let e := CommHopfAlgCat.baseChangePointsMulEquiv (K := K)
    (CommAlgCat.of K (AlgebraicClosure K)) H
  let f : WithConv (H →ₐ[k] AlgebraicClosure k) →*
      WithConv (CommHopfAlgCat.baseChange (K := K) H →ₐ[K] AlgebraicClosure K) :=
    e.symm.toMonoidHom.comp (AlgHom.mapValue ι)
  let _ : Group.IsSolvable
      (WithConv (CommHopfAlgCat.baseChange (K := K) H →ₐ[K] AlgebraicClosure K)) := hH
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  exact e.symm.injective.comp (AlgHom.mapValue_injective ι.injective)

/-- Geometric solvability of a finite-type affine group is invariant under arbitrary extension of
the ground field. -/
theorem baseChange_iff {K : Type w} [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k) [Algebra.FiniteType k H] :
    geometricallySolvablePointsCommHopfAlgProperty K
        (CommHopfAlgCat.baseChange (K := K) H) ↔
      geometricallySolvablePointsCommHopfAlgProperty k H :=
  ⟨of_baseChange H, baseChange H⟩

end

end TauCeti.geometricallySolvablePointsCommHopfAlgProperty
