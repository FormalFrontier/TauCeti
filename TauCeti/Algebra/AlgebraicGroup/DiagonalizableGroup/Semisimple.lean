/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Points of diagonalizable groups are semisimple

A representation of a diagonalizable group `D(G) = Spec R[G]` decomposes into weight submodules
(the internal direct sum of character spaces). Consequently, every point of `D(G)` acts on each
representation by scalar multiplication on each weight space, making the underlying linear
endomorphism diagonalizable and therefore semisimple.

This file proves that **every point of a diagonalizable group is semisimple**: for any commutative
semiring `R`, any commutative group `G`, and any field `K` equipped with an `R`-algebra structure,
every point `g : WithConv (R[G] →ₐ[R] K)` acts on every finitely generated comodule by a semisimple
linear automorphism.

As a consequence, over a perfect field `K`, the multiplicative Jordan decomposition of every point
`g` of a diagonalizable group is trivial: `g_s = g` and `g_u = 1`.

The result specializes immediately to split tori, the multiplicative group `𝔾ₘ`, and the
roots-of-unity groups `μ_n`. We also package the condition that all geometric points are semisimple
as an object property `geometricallySemisimplePointsCommHopfAlgProperty` on commutative Hopf
algebras, parallel to `geometricallyUnipotentPointsCommHopfAlgProperty`, and prove it is closed
under isomorphisms and tensor products.

## Main declarations

* `TauCeti.Comodule.baseChange_weightSpace_le_eigenspace`: the base-changed `x`-weight space is
  contained in the corresponding eigenspace of the point-action endomorphism.
* `TauCeti.Comodule.iSup_baseChange_weightSpace_eq_top`: the base-changed weight submodules span the
  scalar extension.
* `TauCeti.Comodule.isSemisimple_endOfPoint_monoidAlgebra`: the point-action endomorphism on any
  comodule over a monoid algebra is semisimple.
* `TauCeti.HopfAlgebra.isSemisimplePoint_mapDomain_iff`: invariance of point semisimplicity under
  bialgebra isomorphisms.
* `TauCeti.HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff`: a point of a product affine group is
  semisimple if and only if both component points are semisimple.
* `TauCeti.DiagonalizableGroup.isSemisimplePoint`: every point of a diagonalizable group is a
  semisimple point.
* `TauCeti.DiagonalizableGroup.semisimplePart_eq_self` and
  `TauCeti.DiagonalizableGroup.unipotentPart_eq_one`: the Jordan factors of a point of a
  diagonalizable group are the point itself and the identity.
* `TauCeti.DiagonalizableGroup.jordanDecomposition_eq`: the Jordan decomposition of a point of a
  diagonalizable group is `(g, 1)`.
* `TauCeti.SplitTorus.isSemisimplePoint`: every point of a split torus is semisimple.
* `TauCeti.RootsOfUnityGroup.isSemisimplePoint`: every point of `μ_n` is semisimple.
* `TauCeti.MultiplicativeGroup.isSemisimplePoint`: every point of `𝔾ₘ` is semisimple.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty`: the object property asserting that
  every algebraic-closure-valued point is semisimple.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct`: geometric semisimplicity
  is closed under direct products of affine groups.
* `TauCeti.DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty`: diagonalizable
  groups have only semisimple geometric points.
* `TauCeti.SplitTorus.geometricallySemisimplePointsCommHopfAlgProperty`: split tori have only
  semisimple geometric points.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.

This supplies the semisimple-points theorem for diagonalizable groups and tori in Layer 4 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory Module WithConv
open scoped DirectSum TensorProduct

namespace TauCeti

universe u v w x

section ComoduleEigenspaces

variable {R : Type u} {X : Type v} {V : Type w} {K : Type x}
variable [CommSemiring R] [Monoid X] [AddCommMonoid V] [Module R V]
variable [Comodule R (MonoidAlgebra R X) V]
variable [Field K] [Algebra R K]

/-- The base change to `K` of the `x`-weight submodule is contained in the eigenspace of
`Comodule.endOfPoint V f` with eigenvalue `f (MonoidAlgebra.single x 1)`. -/
theorem Comodule.baseChange_weightSpace_le_eigenspace (f : MonoidAlgebra R X →ₐ[R] K) (x : X) :
    (weightSpace R X V x).baseChange K ≤
      End.eigenspace (endOfPoint V f) (f (MonoidAlgebra.single x 1)) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, End.mem_eigenspace_iff]
  have h := endOfPoint_tmul_of_mem_weightSpace f (1 : K) hv
  rw [one_mul] at h
  change endOfPoint V f (1 ⊗ₜ[R] v) = f (MonoidAlgebra.single x 1) • (1 ⊗ₜ[R] v)
  rw [h, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit [Monoid X] in
/-- The base-changed weight submodules of a monoid-algebra comodule span the scalar extension. -/
theorem Comodule.iSup_baseChange_weightSpace_eq_top :
    ⨆ x : X, (weightSpace R X V x).baseChange K = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a v =>
    have hv : v = (weightDecomposition R X V v).sum (fun _ w ↦ w) :=
      (weightDecomposition_sum (R := R) (G := X) (V := V) v).symm
    rw [hv, Finsupp.sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun x _ ↦ ?_
    refine Submodule.mem_iSup_of_mem x ?_
    rw [weightDecomposition_apply]
    exact Submodule.tmul_mem_baseChange_of_mem a (weightProj_mem_weightSpace x v)
  | add z₁ z₂ hz₁ hz₂ => exact add_mem hz₁ hz₂

/-- The eigenspaces of the point-action endomorphism `Comodule.endOfPoint V f` span the scalar
extension `K ⊗[R] V`. -/
theorem Comodule.iSup_eigenspace_endOfPoint_eq_top (f : MonoidAlgebra R X →ₐ[R] K) :
    ⨆ μ : K, End.eigenspace (endOfPoint V f) μ = ⊤ := by
  classical
  have hspan : ⨆ x : X, (weightSpace R X V x).baseChange K ≤
      ⨆ μ : K, End.eigenspace (endOfPoint V f) μ := by
    refine iSup_le fun x ↦ ?_
    exact le_trans (baseChange_weightSpace_le_eigenspace f x)
      (le_iSup (fun μ : K ↦ End.eigenspace (endOfPoint V f) μ) (f (MonoidAlgebra.single x 1)))
  rw [iSup_baseChange_weightSpace_eq_top] at hspan
  exact top_unique hspan

/-- **The point-action endomorphism on any comodule over a monoid algebra is semisimple.** -/
theorem Comodule.isSemisimple_endOfPoint_monoidAlgebra (f : MonoidAlgebra R X →ₐ[R] K) :
    End.IsSemisimple (endOfPoint V f) :=
  isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_endOfPoint_eq_top f)

end ComoduleEigenspaces

section MapDomain

variable {k : Type u} {H₁ : Type v} {H₂ : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H₁] [Semiring H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]
variable [Field K] [Algebra k K]

/-- Semisimplicity of points is invariant under precomposition by a bialgebra isomorphism. -/
theorem HopfAlgebra.isSemisimplePoint_mapDomain_iff
    (e : H₁ ≃ₐc[k] H₂) (g : WithConv (H₂ →ₐ[k] K)) :
    IsSemisimplePoint (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) ↔ IsSemisimplePoint g := by
  constructor
  · intro hg
    have h := hg.mapDomain (e.symm : H₂ →ₐc[k] H₁)
    have he : AlgHom.mapDomain (e.symm : H₂ →ₐc[k] H₁)
        (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) = g := by
      rw [← AlgHom.mapDomainMulEquiv_symm_apply e, ← AlgHom.mapDomainMulEquiv_apply e]
      exact (AlgHom.mapDomainMulEquiv (A := K) e).left_inv g
    rwa [he] at h
  · intro hg
    exact hg.mapDomain (e : H₁ →ₐc[k] H₂)

end MapDomain

section Product

variable {k : Type u} [CommSemiring k]
variable {H K' : Type v} [CommSemiring H] [CommSemiring K']
variable [_root_.HopfAlgebra k H] [_root_.HopfAlgebra k K']
variable {A : Type w} [Field A] [Algebra k A] [PerfectField A]

/-- A point of a product affine group is semisimple exactly when both factor points are
semisimple. -/
theorem HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff
    (g : WithConv ((H ⊗[k] K') →ₐ[k] A)) :
    IsSemisimplePoint g ↔
      IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).1 ∧
        IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).2 := by
  constructor
  · intro hg
    exact ⟨hg.mapDomain Bialgebra.TensorProduct.includeLeft,
      hg.mapDomain Bialgebra.TensorProduct.includeRight⟩
  · rintro ⟨hleft, hright⟩
    let e := AffineGroup.Product.pointsMulEquiv
      (R := k) (H₁ := H) (H₂ := K') (A := A)
    let gleft := e.symm ((e g).1, 1)
    let gright := e.symm (1, (e g).2)
    have hgleft : IsSemisimplePoint gleft := by
      have h := hleft.mapDomain (Bialgebra.TensorProduct.projectLeft
        (R := k) (H₁ := H) (H₂ := K'))
      simpa only [AlgHom.mapDomain_apply, gleft, e,
        AffineGroup.Product.mapDomain_projectLeft] using h
    have hgright : IsSemisimplePoint gright := by
      have h := hright.mapDomain (Bialgebra.TensorProduct.projectRight
        (R := k) (H₁ := H) (H₂ := K'))
      simpa only [AlgHom.mapDomain_apply, gright, e,
        AffineGroup.Product.mapDomain_projectRight] using h
    have hcomm : Commute gleft gright := by
      rw [commute_iff_eq]
      apply e.injective
      simp only [map_mul, e, gleft, gright, MulEquiv.apply_symm_apply]
      ext <;> simp
    have hfactor : g = gleft * gright := by
      apply e.injective
      simp only [map_mul, e, gleft, gright, MulEquiv.apply_symm_apply]
      ext <;> simp
    rw [hfactor]
    exact hgleft.mul_of_commute hgright hcomm

end Product

namespace DiagonalizableGroup

variable {R : Type u} {G : Type v} {K : Type x}
variable [CommSemiring R] [CommGroup G] [Field K] [Algebra R K]

/-- **Every point of the diagonalizable group `D(G)` is semisimple.** -/
theorem isSemisimplePoint (g : WithConv (MonoidAlgebra R G →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g := by
  rw [HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint]
  intro M
  exact Comodule.isSemisimple_endOfPoint_monoidAlgebra g.ofConv

section JordanDecomposition

variable {k : Type u} {G : Type u} {K : Type u}
variable [Field k] [CommGroup G] [Field K] [Algebra k K] [PerfectField K]

/-- **The semisimple part of a point of a diagonalizable group is the point itself.** -/
@[simp]
theorem semisimplePart_eq_self (g : WithConv (MonoidAlgebra k G →ₐ[k] K)) :
    HopfAlgebra.Point.semisimplePart k (MonoidAlgebra k G) K g = g :=
  HopfAlgebra.Point.semisimplePart_eq_self k (MonoidAlgebra k G) K (fun M ↦ by
    have h := isSemisimplePoint (R := k) (G := G) (K := K) g
    exact (HopfAlgebra.isSemisimplePoint_def g).mp h M)

/-- **The unipotent part of a point of a diagonalizable group is trivial.** -/
@[simp]
theorem unipotentPart_eq_one (g : WithConv (MonoidAlgebra k G →ₐ[k] K)) :
    HopfAlgebra.Point.unipotentPart k (MonoidAlgebra k G) K g = 1 :=
  HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k (MonoidAlgebra k G) K (fun M ↦ by
    have h := isSemisimplePoint (R := k) (G := G) (K := K) g
    exact (HopfAlgebra.isSemisimplePoint_def g).mp h M)

/-- The Jordan decomposition of a point of a diagonalizable group is `(g, 1)`. -/
@[simp]
theorem jordanDecomposition_eq (g : WithConv (MonoidAlgebra k G →ₐ[k] K)) :
    HopfAlgebra.Point.jordanDecomposition k (MonoidAlgebra k G) K g = (g, 1) := by
  refine Prod.ext ?_ ?_
  · rw [HopfAlgebra.Point.jordanDecomposition_fst, semisimplePart_eq_self]
  · rw [HopfAlgebra.Point.jordanDecomposition_snd, unipotentPart_eq_one]

end JordanDecomposition

end DiagonalizableGroup

section StandardExamples

variable {R : Type u} {K : Type x} [CommSemiring R] [Field K] [Algebra R K]

namespace SplitTorus

variable {σ : Type v}

/-- **Every point of a split torus is a semisimple point.** -/
theorem isSemisimplePoint
    (g : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g :=
  DiagonalizableGroup.isSemisimplePoint g

end SplitTorus

namespace RootsOfUnityGroup

variable (n : ℕ)

/-- **Every point of the roots-of-unity group scheme `μ_n` is a semisimple point.** -/
theorem isSemisimplePoint
    (g : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g :=
  DiagonalizableGroup.isSemisimplePoint g

end RootsOfUnityGroup

namespace MultiplicativeGroup

/-- **Every point of the multiplicative group `𝔾ₘ` is a semisimple point.** -/
theorem isSemisimplePoint
    (g : WithConv (LaurentPolynomial R →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  have h := DiagonalizableGroup.isSemisimplePoint
    (AlgHom.mapDomain (e.symm : MonoidAlgebra R (Multiplicative ℤ) →ₐc[R] LaurentPolynomial R) g)
  exact (HopfAlgebra.isSemisimplePoint_mapDomain_iff e.symm g).mp h

end MultiplicativeGroup

end StandardExamples

section ObjectProperty

variable (k : Type u) [Field k]

/-- The object property asserting that every algebraic-closure-valued point of a commutative Hopf
algebra is a semisimple point. -/
def geometricallySemisimplePointsCommHopfAlgProperty :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsSemisimplePoint g

/-- Membership in `geometricallySemisimplePointsCommHopfAlgProperty` means that every geometric
point is semisimple. -/
@[simp]
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff
    (H : CommHopfAlgCat.{v} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsSemisimplePoint g :=
  Iff.rfl

/-- The geometric-point semisimplicity property is invariant under isomorphisms of commutative Hopf
algebras. -/
instance :
    (geometricallySemisimplePointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH g := by
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    apply (HopfAlgebra.isSemisimplePoint_mapDomain_iff e' g).mp
    exact hH _

/-- The tensor product of two coordinate Hopf algebras with semisimple geometric points again has
only semisimple geometric points. Contravariantly, geometric-point semisimplicity is closed under
direct products of affine groups. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct
    (H K : CommHopfAlgCat.{v} k)
    (hH : geometricallySemisimplePointsCommHopfAlgProperty k H)
    (hK : geometricallySemisimplePointsCommHopfAlgProperty k K) :
    geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff]
  exact ⟨hH _, hK _⟩

/-- Every geometric point is semisimple exactly when the unipotent part of every geometric point is
the identity. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_unipotentPart_eq_one
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = 1 := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  constructor
  · intro hg
    exact HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k H (AlgebraicClosure k)
      (fun M ↦ (HopfAlgebra.isSemisimplePoint_def g).mp hg M)
  · intro hu
    rw [HopfAlgebra.isSemisimplePoint_def]
    intro M
    have hdecomp := HopfAlgebra.Point.jordanDecomposition_spec k H (AlgebraicClosure k) g
    have hs := hdecomp.1 M
    have hg_eq : g = (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).1 := by
      have hmul := hdecomp.2.2.2
      have h2 : (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).2 = 1 := by
        rw [HopfAlgebra.Point.jordanDecomposition_snd, hu]
      rw [h2, mul_one] at hmul
      exact hmul
    rw [hg_eq]
    exact hs

/-- Every geometric point is semisimple exactly when the semisimple part of every geometric point
is the point itself. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_semisimplePart_eq_self
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = g := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  constructor
  · intro hg
    exact HopfAlgebra.Point.semisimplePart_eq_self k H (AlgebraicClosure k)
      (fun M ↦ (HopfAlgebra.isSemisimplePoint_def g).mp hg M)
  · intro hs
    rw [HopfAlgebra.isSemisimplePoint_def]
    intro M
    have hdecomp := HopfAlgebra.Point.jordanDecomposition_spec k H (AlgebraicClosure k) g
    have hsem := hdecomp.1 M
    have h1 : (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).1 = g := by
      rw [HopfAlgebra.Point.jordanDecomposition_fst, hs]
    rw [h1] at hsem
    exact hsem

namespace DiagonalizableGroup

/-- **Every diagonalizable group has only semisimple geometric points.** -/
theorem geometricallySemisimplePointsCommHopfAlgProperty (G : Type v) [CommGroup G] :
    TauCeti.geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (MonoidAlgebra k G)) := by
  rw [TauCeti.geometricallySemisimplePointsCommHopfAlgProperty_iff]
  intro g
  exact isSemisimplePoint g

end DiagonalizableGroup

namespace SplitTorus

/-- **Every split torus has only semisimple geometric points.** -/
theorem geometricallySemisimplePointsCommHopfAlgProperty (σ : Type v) :
    TauCeti.geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative (σ →₀ ℤ)))) :=
  DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty k (Multiplicative (σ →₀ ℤ))

end SplitTorus

end ObjectProperty

end TauCeti
