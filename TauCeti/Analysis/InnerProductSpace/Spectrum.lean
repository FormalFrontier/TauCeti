/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# An orthonormal basis of eigenvectors for a compact self-adjoint operator

Mathlib's spectral theorem for a compact self-adjoint operator `T` on a Hilbert space `E` says
that the eigenspaces of `T` have trivial mutual orthogonal complement
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) and that the eigenspaces at
nonzero eigenvalues are finite dimensional
(`ContinuousLinearMap.finite_dimensional_eigenspace`).  This file turns the first statement into
the form the applications want: **`E` has an orthonormal basis consisting of eigenvectors of
`T`**.

The construction is the classical one.  Each eigenspace is closed, hence a Hilbert space in its
own right, so it has a Hilbert basis; the eigenspaces are mutually orthogonal, so the union of
those bases is an orthonormal family; and a vector orthogonal to the whole family is orthogonal
to every eigenspace, hence zero.  `HilbertBasis.mkOfOrthogonalEqBot` then assembles the family
into a Hilbert basis of `E`.

No separability is assumed anywhere: the basis is indexed by a set of vectors of `E`, exactly as
in Mathlib's `exists_hilbertBasis`, and the eigenvalue `0` may well carry an infinite-dimensional
eigenspace.  When `T` is injective that eigenspace is trivial and every basis vector has a
nonzero eigenvalue, which is the form the eigenvalue problem of an elliptic operator uses.

## Main declarations

* `ContinuousLinearMap.exists_hilbertBasis_hasEigenvector`: a compact symmetric operator admits a
  Hilbert basis of eigenvectors, with the eigenvalues given as a function on the basis.
* `ContinuousLinearMap.exists_hilbertBasis_hasEigenvector_ne_zero`: for an injective such
  operator, every vector of that basis has a nonzero eigenvalue.
* `ContinuousLinearMap.hasSum_smul_repr_of_apply_eq_smul`: an operator diagonal in a Hilbert
  basis is the sum of its eigencomponents, the spectral expansion such a basis is for.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 6.11 (the Hilbert--Schmidt spectral decomposition); L. C. Evans, *Partial Differential
Equations*, Appendix D.6.
-/

public section

open Module.End
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {T : E →L[𝕜] E}

omit [CompleteSpace E] in
/-- A vector orthogonal to every member of a Hilbert basis of a subspace is orthogonal to the
whole subspace: expand the subspace vector in that basis and use continuity of the inner
product. -/
private theorem inner_eq_zero_of_forall_inner_hilbertBasis_eq_zero {K : Submodule 𝕜 E}
    {iota : Type*} (bK : HilbertBasis iota 𝕜 K) {x : E}
    (hx : ∀ i, ⟪x, (bK i : E)⟫_𝕜 = 0) {y : E} (hy : y ∈ K) : ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : iota => (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- **A compact self-adjoint operator has an orthonormal basis of eigenvectors.**  The basis is
indexed by a set of vectors of `E`, as in `exists_hilbertBasis`, and no separability is
assumed. -/
theorem exists_hilbertBasis_hasEigenvector (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) := by
  classical
  have hbasis : ∀ mu : 𝕜, ∃ (w : Set (eigenspace (T : Module.End 𝕜 E) mu))
      (b : HilbertBasis w 𝕜 (eigenspace (T : Module.End 𝕜 E) mu)),
      ⇑b = ((↑) : w → eigenspace (T : Module.End 𝕜 E) mu) := by
    intro mu
    have : CompleteSpace (eigenspace (T : Module.End 𝕜 E) mu) :=
      (isClosed_eigenspace T mu).completeSpace_coe
    exact exists_hilbertBasis 𝕜 _
  choose w bw _ using hbasis
  set v : (Σ mu : 𝕜, w mu) → E := fun p =>
    (eigenspace (T : Module.End 𝕜 E) p.1).subtypeₗᵢ (bw p.1 p.2)
  have hv : Orthonormal 𝕜 v :=
    hT'.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun mu => (bw mu).orthonormal
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hmem : ∀ p, v p ∈ eigenspace (T : Module.End 𝕜 E) p.1 := fun p => (bw p.1 p.2).2
  have hspan : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT',
      ← Submodule.iInf_orthogonal]
    intro x hx
    have hx' : ∀ p, ⟪x, v p⟫_𝕜 = 0 := fun p =>
      (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨p, rfl⟩)
    simp only [Submodule.mem_iInf]
    intro mu
    rw [Submodule.mem_orthogonal']
    exact fun y hy =>
      inner_eq_zero_of_forall_inner_hilbertBasis_eq_zero (bw mu) (fun i => hx' ⟨mu, i⟩) hy
  have key : ∀ x : Set.range v, ∃ mu : 𝕜, HasEigenvector (T : Module.End 𝕜 E) mu (x : E) := by
    rintro ⟨-, p, rfl⟩
    refine ⟨p.1, hmem p, fun hzero => ?_⟩
    have hzero' : v p = 0 := hzero
    have hnorm : ‖v p‖ = 1 := hv.1 p
    rw [hzero', norm_zero] at hnorm
    exact zero_ne_one hnorm
  choose nu hnu using key
  exact ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot ((orthonormal_subtype_range hinj).2 hv)
    (by rwa [Subtype.range_coe]), nu, HilbertBasis.coe_mkOfOrthogonalEqBot _ _, hnu⟩

/-- **An injective compact self-adjoint operator has an orthonormal basis of eigenvectors with
nonzero eigenvalues.**  Injectivity is exactly the vanishing of the eigenspace at `0`, the one
eigenspace that a compact operator may have of infinite dimension. -/
theorem exists_hilbertBasis_hasEigenvector_ne_zero (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hker : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (nu : s → 𝕜), ⇑b = ((↑) : s → E) ∧
      (∀ x : s, nu x ≠ 0) ∧ ∀ x : s, HasEigenvector (T : Module.End 𝕜 E) (nu x) (x : E) := by
  obtain ⟨s, b, nu, hb, hev⟩ := exists_hilbertBasis_hasEigenvector hT hT'
  refine ⟨s, b, nu, hb, fun x hx => ?_, hev⟩
  have hx0 : (x : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] E) := by
    rw [← eigenspace_zero, ← hx]
    exact (hev x).1
  rw [hker, Submodule.mem_bot] at hx0
  exact (hev x).2 hx0

omit [CompleteSpace E] in
/-- **The spectral expansion of an operator diagonal in a Hilbert basis.**  Applying `T` term by
term to the expansion of `y` writes `T y` as the sum of its eigencomponents; combined with
`ContinuousLinearMap.exists_hilbertBasis_hasEigenvector` this diagonalizes a compact
self-adjoint operator. -/
theorem hasSum_smul_repr_of_apply_eq_smul {iota : Type*} (b : HilbertBasis iota 𝕜 E)
    (nu : iota → 𝕜) (hb : ∀ i, T (b i) = nu i • b i) (y : E) :
    HasSum (fun i => nu i • b.repr y i • b i) (T y) := by
  have key : ∀ i, T (b.repr y i • b i) = nu i • b.repr y i • b i := fun i => by
    rw [map_smul, hb, smul_comm]
  simpa only [key] using T.hasSum (b.hasSum_repr y)

end ContinuousLinearMap
