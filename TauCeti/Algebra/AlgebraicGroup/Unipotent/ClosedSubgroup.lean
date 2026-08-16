/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Closed subgroups of smooth unipotent affine groups

A closed subgroup of an affine group is represented contravariantly by a surjective morphism of
coordinate Hopf algebras. This file proves that geometric-point unipotence descends along such a
morphism. Consequently, a smooth closed subgroup of a smooth unipotent affine group is again
smooth unipotent.

The pointwise argument uses naturality and uniqueness of Jordan decomposition. If `f : H ⟶ K`
is surjective and a `K`-point `g` becomes unipotent after precomposition with `f`, naturality says
that the semisimple part of `g` also becomes the identity after precomposition. Surjectivity makes
precomposition injective on points, so the semisimple part of `g` was already the identity.

Smoothness of the subgroup is retained as an explicit hypothesis. It cannot be deduced from the
closed immersion: in positive characteristic, the nonsmooth group scheme `αₚ` is a closed subgroup
of the smooth unipotent group `𝔾ₐ`.

## Main declarations

* `TauCeti.HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective`: unipotence is reflected by
  precomposition with a surjective coordinate morphism.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective`: geometric unipotence
  descends to a quotient coordinate Hopf algebra.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_of_surjective`: a smooth quotient of a
  geometrically unipotent finite-type coordinate Hopf algebra is smooth unipotent.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_quotient`: the preceding result for the quotient by
  a Hopf ideal, hence for a smooth closed subgroup scheme.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is a closure result needed in Layer 5, "Unipotent groups", of the ReductiveGroups roadmap.
It supplies a basic input for comparing connected normal unipotent closed subgroups in the
construction of the unipotent radical.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

namespace HopfAlgebra

variable {k H K L : Type u} [Field k]
variable [CommRing H] [_root_.HopfAlgebra k H]
variable [CommRing K] [_root_.HopfAlgebra k K]
variable [Field L] [Algebra k L] [PerfectField L]

/-- Precomposition with a surjective coordinate Hopf-algebra morphism detects unipotent points.

Contravariantly, this says that a point of a closed subgroup is unipotent exactly when its image
in the ambient affine group is unipotent. -/
@[simp]
theorem isUnipotentPoint_mapDomain_iff_of_surjective
    (f : H →ₐc[k] K) (hf : Function.Surjective f)
    (g : WithConv (K →ₐ[k] L)) :
    IsUnipotentPoint (toConv (g.ofConv.comp (f : H →ₐ[k] K))) ↔ IsUnipotentPoint g := by
  rw [← AlgHom.mapDomain_apply]
  constructor
  · intro hg
    rw [Point.isUnipotentPoint_iff_semisimplePart_eq_one] at hg ⊢
    let f' : CommHopfAlgCat.of k H ⟶ CommHopfAlgCat.of k K := CommHopfAlgCat.ofHom f
    apply CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective f' hf
      (CommAlgCat.of k L)
    have hmap' :
        (CommHopfAlgCat.mapPointsFunctor f').app (CommAlgCat.of k L)
          (Point.semisimplePart k K L g) = 1 := by
      rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
      simp only [HopfAlgebra.pointsFunctor_obj]
      dsimp [f']
      rw [← AlgHom.mapDomain_apply, ← Point.semisimplePart_mapDomain]
      exact hg
    exact hmap'.trans (map_one _).symm
  · intro hg
    exact hg.mapDomain f

end HopfAlgebra

/-- Geometric-point unipotence descends along a surjective morphism of coordinate Hopf algebras.

The corresponding morphism of affine groups is a closed immersion in the opposite direction. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{u} k}
    (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H) :
    geometricallyUnipotentPointsCommHopfAlgProperty k K := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hH ⊢
  intro g
  exact (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective f.hom hf g).mp (hH _)

/-- A smooth quotient of a geometrically unipotent finite-type coordinate Hopf algebra is smooth
unipotent.

Contravariantly, the quotient coordinate algebra represents a smooth closed subgroup of the
original affine group. Smoothness of the quotient is an explicit hypothesis because closed
subgroups of smooth group schemes need not be smooth in positive characteristic. -/
theorem smoothUnipotentCommHopfAlgProperty_of_surjective
    (k : Type u) [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj)
    (hK : Algebra.Smooth k K) :
    smoothUnipotentCommHopfAlgProperty k K := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨hK, ?_⟩
  rw [← geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective k f.hom hf hH

/-- A smooth Hopf-ideal quotient of a geometrically unipotent finite-type coordinate Hopf algebra is
smooth unipotent.

The spectrum of `H ⧸ I` is the closed subgroup scheme cut out by `I`; thus this is the coordinate
form of closure of smooth unipotent affine groups under smooth closed subgroup schemes. -/
theorem smoothUnipotentCommHopfAlgProperty_quotient
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj)
    (hI : Algebra.Smooth k (H ⧸ I.toIdeal)) :
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) := by
  apply smoothUnipotentCommHopfAlgProperty_of_surjective k
    (FiniteTypeCommHopfAlgCat.mkQuotient H I) _ hH hI
  exact Ideal.Quotient.mkₐ_surjective k I.toIdeal

end TauCeti
