/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Representation.GeometricSemisimplePoint
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
roots-of-unity groups `μ_n`. Using the generic object property
`geometricallySemisimplePointsCommHopfAlgProperty`, this file also packages the corresponding
geometric statements for diagonalizable groups and split tori.

## Main declarations

* `TauCeti.Comodule.baseChange_weightSpace_le_eigenspace`: the base-changed `x`-weight space is
  contained in the corresponding eigenspace of the point-action endomorphism.
* `TauCeti.Comodule.iSup_baseChange_weightSpace_eq_top`: the base-changed weight submodules span the
  scalar extension.
* `TauCeti.Comodule.isSemisimple_endOfPoint_monoidAlgebra`: the point-action endomorphism on any
  comodule over a monoid algebra is semisimple.
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
  -- Eigenspace membership uses scalar multiplication on `K ⊗[R] V`, whereas the weight-space
  -- action lemma expresses the same vector as a pure tensor; expose that definitional equality
  -- before normalizing scalar multiplication on the tensor product.
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

section ObjectPropertyExamples

variable (k : Type u) [Field k]

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

end ObjectPropertyExamples

end TauCeti
