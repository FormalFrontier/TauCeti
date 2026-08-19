/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint

/-!
# Central points under base change

Let `H` be a bialgebra over `k`, let `K` be a commutative `k`-algebra, and let `A` be a
commutative `K`-algebra. The standard equivalence

```text
  (K ⊗[k] H →ₐ[K] A) ≃ (H →ₐ[k] A)
```

identifies universally central points on the two sides. The reverse implication uses the full
universal definition of centrality: a `k`-algebra map out of `A` gives its codomain the induced
`K`-algebra structure, so every test point before base change is also a test point after base
change.

## Main results

* `TauCeti.HopfAlgebra.isCentralPoint_baseChangePointsMulEquiv_symm_iff`: the unbundled
  base-change equivalence preserves and reflects universal centrality.
* `TauCeti.CommHopfAlgCat.isCentralPoint_baseChangePointsMulEquiv_iff`: the corresponding
  statement for bundled commutative Hopf algebras and their functors of points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.d, 1.k, and 2.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 2 and 16.

This is the pointwise base-change input for the center `Z(G)` in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open TensorProduct WithConv

namespace TauCeti

universe u v

namespace HopfAlgebra

variable {k : Type u} {K H A : Type v} [CommRing k] [CommRing K] [Ring H] [CommRing A]
variable [Algebra k K] [_root_.Bialgebra k H]
variable [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- Universal centrality is preserved and reflected by the base-change equivalence on points.

The equivalence is written in the restriction direction, from a point of `K ⊗[k] H` to a
point of `H`. -/
theorem isCentralPoint_baseChangePointsMulEquiv_symm_iff
    (g : WithConv (K ⊗[k] H →ₐ[K] A)) :
    IsCentralPoint
        ((AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := A)).symm g) ↔
      IsCentralPoint g := by
  constructor
  · intro hg
    rw [isCentralPoint_def] at hg ⊢
    intro B _ _ φ h
    let _ : Algebra k B := Algebra.compHom B (algebraMap k K)
    let _ : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
    rw [commute_iff_eq]
    apply (AlgHom.baseChangePointsMulEquiv
      (k := k) (K := K) (A := H) (R := B)).symm.injective
    simp only [map_mul]
    rw [AlgHom.baseChangePointsMulEquiv_symm_mapValue]
    exact (hg (φ.restrictScalars k)
      ((AlgHom.baseChangePointsMulEquiv
        (k := k) (K := K) (A := H) (R := B)).symm h)).eq
  · intro hg
    rw [isCentralPoint_def] at hg ⊢
    intro B _ _ φ h
    let _ : Algebra K B :=
      (φ.toRingHom.comp (algebraMap K A)).toAlgebra
    let _ : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply k K A]
      exact (φ.commutes r).symm
    let φK : A →ₐ[K] B :=
      { φ.toRingHom with
        commutes' := fun r ↦ by
          rw [RingHom.algebraMap_toAlgebra]
          rfl }
    rw [commute_iff_eq]
    apply (AlgHom.baseChangePointsMulEquiv
      (k := k) (K := K) (A := H) (R := B)).injective
    simp only [map_mul]
    have hφ : φK.restrictScalars k = φ := AlgHom.ext fun _ ↦ rfl
    rw [← hφ, ← AlgHom.mapValue_baseChangePointsMulEquiv φK]
    simpa only [MulEquiv.apply_symm_apply] using (hg φK
      (AlgHom.baseChangePointsMulEquiv
        (k := k) (K := K) (A := H) (R := B) h)).eq

end HopfAlgebra

namespace CommHopfAlgCat

variable {k : Type u} {K : Type v} [CommRing k] [CommRing K] [Algebra k K]

/-- The bundled base-change equivalence on points preserves and reflects universal centrality. -/
theorem isCentralPoint_baseChangePointsMulEquiv_iff
    (H : _root_.CommHopfAlgCat.{v} k) (A : CommAlgCat.{v} K)
    (g : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    HopfAlgebra.IsCentralPoint (baseChangePointsMulEquiv (K := K) A H g) ↔
      HopfAlgebra.IsCentralPoint g := by
  let _ : Algebra k A := Algebra.compHom A (algebraMap k K)
  let _ : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  have he : baseChangePointsMulEquiv (K := K) A H g =
      (AlgHom.baseChangePointsMulEquiv
        (k := k) (K := K) (A := H) (R := A)).symm g := by
    apply WithConv.ext
    ext h
    rw [baseChangePointsMulEquiv_apply_apply,
      AlgHom.baseChangePointsMulEquiv_symm_apply]
  rw [he]
  exact HopfAlgebra.isCentralPoint_baseChangePointsMulEquiv_symm_iff g

end CommHopfAlgCat

end TauCeti
