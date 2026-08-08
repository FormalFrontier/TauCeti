/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Idempotents

/-!
# A complete family of orthogonal idempotents decomposes every module

Let `R` be an `S`-algebra and let `e : ι → R` be a *complete orthogonal family of idempotents*:
`eᵢ eⱼ = 0` for `i ≠ j` and `∑ᵢ eᵢ = 1`. Then every left `R`-module `M` splits as an internal
direct sum of the `S`-submodules `eᵢ • M`,

`M = ⨁ᵢ eᵢ M`,

the component of `x` in position `i` being `eᵢ • x`. This file proves that
(`TauCeti.isInternal_smulRange`) and records the dimension count `dim M = ∑ᵢ dim (eᵢ M)` that
follows over a field.

Mathlib has the family (`CompleteOrthogonalIdempotents`) and the converse direction — a
decomposition of `R` itself into left ideals produces such a family
(`DirectSum.completeOrthogonalIdempotents_idempotent`) — but not the decomposition of an arbitrary
module that the family induces.

## The two scalar rings

The pieces `eᵢ • M` are *not* `R`-submodules: `R` is noncommutative in the intended applications,
and `r • (eᵢ • x)` need not lie in `eᵢ • M`. They are submodules over any commutative ring `S`
acting through the centre of `R`, which is exactly the data of an `S`-algebra structure on `R`
together with `IsScalarTower S R M`; carrying that ambient `S` is what makes the dimension count
below available. Taking `S = ℕ` recovers the decomposition as additive submonoids.

## Main definitions

* `TauCeti.smulRange S M e`: the `S`-submodule `e • M` of an `R`-module `M`.

## Main results

* `TauCeti.mem_smulRange_iff_smul_eq_self`: for an idempotent `e`, membership in `e • M` is the
  fixed-point condition `e • x = x`. This is the form every proof below uses, and it is what makes
  `e • M` a *summand* rather than a mere image.
* `TauCeti.isInternal_smulRange`: **the decomposition** `M = ⨁ᵢ eᵢ M`. Independence comes from
  orthogonality (`eᵢ` annihilates `eⱼ • M` for `j ≠ i`) and spanning from completeness
  (`x = ∑ᵢ eᵢ • x`).
* `TauCeti.finrank_eq_sum_finrank_smulRange`: the resulting dimension count over a field.
* `TauCeti.smulRange_le_comap`: an `R`-linear map carries `e • M` into `e • N`, so the pieces are
  natural in the module.

## References

This is the module-theoretic step behind the identification of representations of a quiver with
left modules over its path algebra (`quiverRepEquivalence`) in
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 1 inverts
"through the idempotent decomposition `M = ⨁ᵥ eᵥ M` guaranteed by `∑ᵥ eᵥ = 1`".
-/

public section

namespace TauCeti

open scoped DirectSum

section Defs

variable (S M : Type*) {R : Type*} [CommSemiring S] [Semiring R] [Algebra S R]
  [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower S R M]

/-- The `S`-submodule `e • M` of an `R`-module `M`, the image of multiplication by `e : R`.

The scalars `S` act through the centre of `R`, so multiplication by `e` is `S`-linear even though
it is not `R`-linear. For an idempotent `e` this submodule is the summand `e` cuts out; see
`TauCeti.mem_smulRange_iff_smul_eq_self`. -/
def smulRange (e : R) : Submodule S M where
  carrier := Set.range fun y : M => e • y
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, smul_add e a b⟩
  zero_mem' := ⟨0, smul_zero e⟩
  smul_mem' := by
    rintro s _ ⟨a, rfl⟩
    exact ⟨s • a, smul_comm e s a⟩

variable {S M}

@[simp]
theorem mem_smulRange_iff {e : R} {x : M} : x ∈ smulRange S M e ↔ ∃ y : M, e • y = x :=
  Iff.rfl

/-- Every multiple of `e` lies in `e • M`. -/
theorem smul_mem_smulRange (e : R) (y : M) : e • y ∈ smulRange S M e :=
  ⟨y, rfl⟩

/-- The whole module is cut out by the unit. -/
@[simp]
theorem smulRange_one : smulRange S M (1 : R) = ⊤ :=
  eq_top_iff.2 fun x _ => ⟨x, one_smul R x⟩

/-- Nothing is cut out by zero. -/
@[simp]
theorem smulRange_zero : smulRange S M (0 : R) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨y, rfl⟩ := hx
  simp

/-- **Membership in `e • M` for an idempotent `e` is a fixed-point condition.** One direction is
idempotency, the other is that a fixed point is its own multiple. -/
theorem mem_smulRange_iff_smul_eq_self {e : R} (he : IsIdempotentElem e) {x : M} :
    x ∈ smulRange S M e ↔ e • x = x := by
  refine ⟨?_, fun hx => ⟨x, hx⟩⟩
  rintro ⟨y, rfl⟩
  rw [smul_smul, he.eq]

/-- Multiplication by an idempotent `e` fixes `e • M` pointwise. -/
theorem smul_of_mem_smulRange {e : R} (he : IsIdempotentElem e) {x : M}
    (hx : x ∈ smulRange S M e) : e • x = x :=
  (mem_smulRange_iff_smul_eq_self he).1 hx

end Defs

section Map

variable {S M N R : Type*} [CommSemiring S] [Semiring R] [Algebra S R]
  [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower S R M]
  [AddCommMonoid N] [Module S N] [Module R N] [IsScalarTower S R N]

/-- **The pieces are natural in the module**: an `R`-linear map carries `e • M` into `e • N`. -/
theorem smulRange_le_comap (e : R) (f : M →ₗ[R] N) :
    smulRange S M e ≤ (smulRange S N e).comap (f.restrictScalars S) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨f y, (map_smul f e y).symm⟩

end Map

section Orthogonal

variable {S M R ι : Type*} [CommSemiring S] [Semiring R] [Algebra S R]
  [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower S R M] {e : ι → R}

/-- An orthogonal idempotent annihilates the piece cut out by any of the others. -/
theorem smul_eq_zero_of_mem_smulRange (he : OrthogonalIdempotents e)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ smulRange S M (e j)) : e i • x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [smul_smul, he.ortho hij, zero_smul]

/-- The pieces cut out by an orthogonal family are independent: the piece at `i` meets the
supremum of the others only in `0`, because `eᵢ` fixes the former and kills the latter. -/
theorem iSupIndep_smulRange (he : OrthogonalIdempotents e) :
    iSupIndep fun i => smulRange S M (e i) := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hker : (⨆ j, ⨆ _ : j ≠ i, smulRange S M (e j))
      ≤ LinearMap.ker (DistribSMul.toLinearMap S M (e i)) :=
    iSup_le fun j => iSup_le fun hj y hy =>
      LinearMap.mem_ker.2 (smul_eq_zero_of_mem_smulRange he (Ne.symm hj) hy)
  have hx0 : e i • x = 0 := LinearMap.mem_ker.1 (hker hx')
  rw [← smul_of_mem_smulRange (he.idem i) hx, hx0]

variable [Fintype ι]

/-- **Completeness is the decomposition of an element**: `x = ∑ᵢ eᵢ • x`. -/
theorem sum_smul_eq_self (he : CompleteOrthogonalIdempotents e) (x : M) :
    ∑ i, e i • x = x := by
  rw [← Finset.sum_smul, he.complete, one_smul]

/-- The pieces cut out by a complete orthogonal family span the module. -/
theorem iSup_smulRange_eq_top (he : CompleteOrthogonalIdempotents e) :
    (⨆ i, smulRange S M (e i)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [← sum_smul_eq_self he x]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (smul_mem_smulRange (e i) x)

end Orthogonal

section Internal

variable {S M R ι : Type*} [CommRing S] [Semiring R] [Algebra S R]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M] {e : ι → R}
  [Fintype ι] [DecidableEq ι]

/-- **A complete orthogonal family of idempotents decomposes every module**: `M = ⨁ᵢ eᵢ M`.

The `S`-submodule at `i` is `eᵢ • M`, and the component of `x` there is `eᵢ • x`.

The scalars are asked to form a *ring* only because that is the generality in which Mathlib's
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` assembles independence and spanning
into an internal direct sum; the two ingredients
`TauCeti.iSupIndep_smulRange` and `TauCeti.iSup_smulRange_eq_top` hold over a commutative
semiring. -/
theorem isInternal_smulRange (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal fun i => smulRange S M (e i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_smulRange he.toOrthogonalIdempotents) (iSup_smulRange_eq_top he)

/-- The module is `S`-linearly isomorphic to the direct sum of its pieces. -/
noncomputable def smulRangeDirectSumEquiv (he : CompleteOrthogonalIdempotents e) :
    (⨁ i, smulRange S M (e i)) ≃ₗ[S] M :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (isInternal_smulRange he)

end Internal

section Finrank

variable {S M R ι : Type*} [Field S] [Semiring R] [Algebra S R]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M] {e : ι → R} [Fintype ι]

/-- **The dimension count**: over a field the dimensions of the pieces add up to the dimension of
the module. -/
theorem finrank_eq_sum_finrank_smulRange [Module.Finite S M]
    (he : CompleteOrthogonalIdempotents e) :
    Module.finrank S M = ∑ i, Module.finrank S (smulRange S M (e i) : Submodule S M) := by
  classical
  rw [← (smulRangeDirectSumEquiv he).finrank_eq, Module.finrank_directSum]

end Finrank

end TauCeti
