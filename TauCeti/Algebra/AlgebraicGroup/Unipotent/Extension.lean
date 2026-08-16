/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup

/-!
# Extensions of smooth unipotent affine groups

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field `k`. In the
contravariant affine-group dictionary it represents a homomorphism `Spec K ⟶ Spec H`. This
file proves the pointwise extension principle: a point of `Spec K` is unipotent when its image in
`Spec H` is unipotent and every point in the kernel of the homomorphism is unipotent.

The proof uses Jordan decomposition rather than a chosen representation. Naturality sends the
semisimple part of the original point to the semisimple part of its unipotent image, hence to the
identity. The semisimple part therefore belongs to the kernel closed subgroup. If every kernel
point is unipotent, this semisimple point is both semisimple and unipotent, so it is the identity.

On coordinate rings, the kernel closed subgroup has algebra

```text
K / K·f(H⁺),
```

implemented as `CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f)`. The resulting
object-property theorem says that geometric-point unipotence of `Spec K` is equivalent to that of
the kernel whenever `Spec H` is geometrically unipotent. The final statements combine this with
the explicit smoothness hypothesis used by `smoothUnipotentCommHopfAlgProperty`.

## Main declarations

* `TauCeti.HopfAlgebra.IsUnipotentPoint.of_mapDomain_of_kernel`: the pointwise extension
  principle.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_of_kernel`: geometric-point
  unipotence is closed under extensions.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff_kernel`: when the target is
  geometrically unipotent, the source is geometrically unipotent exactly when its kernel is.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_iff_smooth_and_kernel`: the corresponding
  characterization for a smooth finite-type source.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the extension-closure step in Layer 5, "Unipotent groups", of the ReductiveGroups
roadmap. Together with closed-subgroup and product closure, it is part of the subgroup calculus
needed to construct and compare connected normal unipotent closed subgroups in the unipotent
radical.
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

/-- A point is unipotent when its image is unipotent and every point in the kernel of the
coordinate morphism is unipotent.

Here the kernel hypothesis is expressed pointwise: it applies to precisely those `K`-points whose
precomposition along `f` is the identity `H`-point. The object-level results below identify this
condition with points of the quotient by `CommHopfAlgCat.kernelHopfIdeal`. -/
theorem IsUnipotentPoint.of_mapDomain_of_kernel
    (f : H →ₐc[k] K) (g : WithConv (K →ₐ[k] L))
    (himage : IsUnipotentPoint (AlgHom.mapDomain f g))
    (hkernel : ∀ s : WithConv (K →ₐ[k] L),
      AlgHom.mapDomain f s = 1 → IsUnipotentPoint s) :
    IsUnipotentPoint g := by
  rw [Point.isUnipotentPoint_iff_semisimplePart_eq_one] at himage ⊢
  let s := Point.semisimplePart k K L g
  have hs_map : AlgHom.mapDomain f s = 1 := by
    rw [← Point.semisimplePart_mapDomain]
    exact himage
  have hs_unipotent : IsUnipotentPoint s := hkernel s hs_map
  have hs_semisimple : Point.semisimplePart k K L s = s :=
    Point.semisimplePart_eq_self k K L
      (Point.isSemisimple_pointsAction_semisimplePart k K L g)
  calc
    Point.semisimplePart k K L g = s := rfl
    _ = Point.semisimplePart k K L s := hs_semisimple.symm
    _ = 1 := Point.semisimplePart_eq_one_of_isUnipotent k K L hs_unipotent

end HopfAlgebra

/-- Geometric-point unipotence is closed under extensions.

For the group homomorphism represented by `f : H ⟶ K`, assume that the target `Spec H` and
the kernel `Spec (K / K·f(H⁺))` have only unipotent geometric points. Then every geometric
point of the source `Spec K` is unipotent. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_of_kernel
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H)
    (hkernel : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f))) :
    geometricallyUnipotentPointsCommHopfAlgProperty k K := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hH hkernel ⊢
  intro g
  apply HopfAlgebra.IsUnipotentPoint.of_mapDomain_of_kernel f.hom g (hH _)
  intro s hs
  have hs_mem :
      s ∈ CommHopfAlgCat.quotientPointsSubgroup K
        (CommHopfAlgCat.kernelHopfIdeal f) (CommAlgCat.of k (AlgebraicClosure k)) := by
    apply (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f
      (CommAlgCat.of k (AlgebraicClosure k)) s).mp
    simpa only [AlgHom.mapDomain_apply] using hs
  -- The subgroup is the range of the quotient-points inclusion, but the exposed definition does
  -- not reduce during pattern matching; identify the carrier before extracting its preimage.
  change s ∈ Set.range
    (CommHopfAlgCat.quotientPointsHom K (CommHopfAlgCat.kernelHopfIdeal f)
      (CommAlgCat.of k (AlgebraicClosure k))) at hs_mem
  obtain ⟨q, hq⟩ := hs_mem
  have hq_unipotent := (hkernel q).mapDomain
    (CommHopfAlgCat.mkQuotient K (CommHopfAlgCat.kernelHopfIdeal f)).hom
  rw [AlgHom.mapDomain_apply,
    ← CommHopfAlgCat.quotientPointsHom_apply] at hq_unipotent
  rwa [hq] at hq_unipotent

/-- If the target of a homomorphism is geometrically unipotent, then its source is geometrically
unipotent exactly when its kernel is.

The forward implication is closure under closed subgroups, applied to the quotient coordinate
map. The reverse implication is the extension theorem above. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_iff_kernel
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H) :
    geometricallyUnipotentPointsCommHopfAlgProperty k K ↔
      geometricallyUnipotentPointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f)) := by
  constructor
  · intro hK
    apply geometricallyUnipotentPointsCommHopfAlgProperty_of_surjective k
      (CommHopfAlgCat.mkQuotient K (CommHopfAlgCat.kernelHopfIdeal f))
      (Ideal.Quotient.mkₐ_surjective k (CommHopfAlgCat.kernelHopfIdeal f).toIdeal) hK
  · exact geometricallyUnipotentPointsCommHopfAlgProperty_of_kernel k f hH

/-- A smooth finite-type affine group with geometrically unipotent target is smooth unipotent
exactly when the geometric points of its kernel are unipotent.

Smoothness of the source remains explicit. This theorem proves the unipotence part of extension
closure; it does not assert smoothness of the middle group from exactness hypotheses that are not
present in the coordinate morphism alone. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_smooth_and_kernel
    (k : Type u) [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k} (f : H ⟶ K)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) :
    smoothUnipotentCommHopfAlgProperty k K ↔
      Algebra.Smooth k K ∧
        geometricallyUnipotentPointsCommHopfAlgProperty k
          (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  apply and_congr_right
  intro _
  rw [← geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact geometricallyUnipotentPointsCommHopfAlgProperty_iff_kernel k f.hom hH

/-- A smooth finite-type source of a homomorphism is smooth unipotent when its target and kernel
have only unipotent geometric points. -/
theorem smoothUnipotentCommHopfAlgProperty_of_kernel
    (k : Type u) [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k} (f : H ⟶ K)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj)
    (hkernel : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)))
    (hK : Algebra.Smooth k K) :
    smoothUnipotentCommHopfAlgProperty k K :=
  (smoothUnipotentCommHopfAlgProperty_iff_smooth_and_kernel k f hH).2 ⟨hK, hkernel⟩

end TauCeti
