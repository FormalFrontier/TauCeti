/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Idempotents

/-!
# A complete family of orthogonal idempotents decomposes every module

Let `R` be a semiring and let `e : ι → R` be a *complete orthogonal family of idempotents*:
`eᵢ eⱼ = 0` for `i ≠ j` and `∑ᵢ eᵢ = 1`. Then every left `R`-module `M` splits as an internal
direct sum of the `S`-submodules `eᵢ • M`,

`M = ⨁ᵢ eᵢ M`,

the component of `x` in position `i` being `eᵢ • x`. This file proves that
(`TauCeti.isInternal_smulRange`) and records the dimension count `dim M = ∑ᵢ dim (eᵢ M)` that
follows over a division ring.

Mathlib has the family (`CompleteOrthogonalIdempotents`) and the converse direction — a
decomposition of `R` itself into left ideals produces such a family
(`DirectSum.completeOrthogonalIdempotents_idempotent`) — but not the decomposition of an arbitrary
module that the family induces.

## The two scalar rings

The pieces `eᵢ • M` are *not* `R`-submodules: `R` is noncommutative in the intended applications,
and `r • (eᵢ • x)` need not lie in `eᵢ • M`. They are submodules over any second ring `S` whose
action on `M` commutes with that of `R`, that is, under `SMulCommClass R S M`, which is exactly
what makes multiplication by `e` an `S`-linear map (`DistribSMul.toLinearMap`); carrying that
ambient `S` is what makes the dimension count below available. Taking `S = ℕ` recovers the
decomposition as additive submonoids, and an `S`-algebra structure on `R` together with
`IsScalarTower S R M` supplies the hypothesis in the intended applications.

## Main definitions

* `TauCeti.smulRange S M e`: the `S`-submodule `e • M` of an `R`-module `M`.
* `TauCeti.smulRangeMap S e f`: the restriction of an `R`-linear map `f : M →ₗ[R] N` to
  `e • M →ₗ[S] e • N`.

## Main results

* `TauCeti.mem_smulRange_iff_smul_eq_self`: for an idempotent `e`, membership in `e • M` is the
  fixed-point condition `e • x = x`. This is the form every proof below uses, and it is what makes
  `e • M` a *summand* rather than a mere image.
* `TauCeti.isInternal_smulRange`: **the decomposition** `M = ⨁ᵢ eᵢ M`. Independence comes from
  orthogonality (`eᵢ` annihilates `eⱼ • M` for `j ≠ i`) and spanning from completeness
  (`x = ∑ᵢ eᵢ • x`).
* `TauCeti.smul_coeLinearMap_smulRange`: multiplying by `eᵢ` reads off the `i`-th component of a
  sum. This is what makes the sum direct, and it describes the inverse of the decomposition
  (`TauCeti.coe_isInternal_smulRange_symm_apply`).
* `TauCeti.finrank_eq_sum_finrank_smulRange`: for a module finite-dimensional over a division
  ring `S`, the dimensions of the pieces add up to the dimension of the module.

## References

This is the module-theoretic step behind the identification of representations of a quiver with
left modules over its path algebra (`quiverRepEquivalence`) in
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 1 inverts
"through the idempotent decomposition `M = ⨁ᵥ eᵥ M` guaranteed by `∑ᵥ eᵥ = 1`".

The decomposition of a module along a complete orthogonal family of idempotents is the classical
*Peirce decomposition*; see T. Y. Lam, *A First Course in Noncommutative Rings*, §21, or
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. I.4.
-/

public section

namespace TauCeti

open scoped DirectSum

section Defs

variable (S M : Type*) {R : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M]

/-- The `S`-submodule `e • M` of an `R`-module `M`, the range of multiplication by `e : R`.

The action of `S` commutes with that of `R`, so multiplication by `e` is `S`-linear even though
it is not `R`-linear. For an idempotent `e` this submodule is the summand `e` cuts out; see
`TauCeti.mem_smulRange_iff_smul_eq_self`. -/
def smulRange (e : R) : Submodule S M :=
  LinearMap.range (DistribSMul.toLinearMap S M e)

variable {S M}

/-- Membership in `e • M` is being a multiple of `e`. This is `LinearMap.mem_range` for the map
`DistribSMul.toLinearMap S M e`, phrased in the action; it is the form every proof uses. -/
@[simp]
theorem mem_smulRange_iff {e : R} {x : M} : x ∈ smulRange S M e ↔ ∃ y : M, e • y = x :=
  LinearMap.mem_range

/-- Every multiple of `e` lies in `e • M`. -/
theorem smul_mem_smulRange (e : R) (y : M) : e • y ∈ smulRange S M e :=
  LinearMap.mem_range_self _ y

/-- The whole module is cut out by the unit. -/
@[simp]
theorem smulRange_one : smulRange S M (1 : R) = ⊤ :=
  eq_top_iff.2 fun x _ => mem_smulRange_iff.2 ⟨x, one_smul R x⟩

/-- Nothing is cut out by zero. -/
@[simp]
theorem smulRange_zero : smulRange S M (0 : R) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨y, rfl⟩ := mem_smulRange_iff.1 hx
  simp

/-- **Membership in `e • M` for an idempotent `e` is a fixed-point condition.** This is Mathlib's
`LinearMap.IsIdempotentElem.mem_range_iff` for the idempotent endomorphism `x ↦ e • x`. -/
theorem mem_smulRange_iff_smul_eq_self {e : R} (he : IsIdempotentElem e) {x : M} :
    x ∈ smulRange S M e ↔ e • x = x :=
  LinearMap.IsIdempotentElem.mem_range_iff (he.map (Module.toModuleEnd S M))

/-- Multiplication by an idempotent `e` fixes `e • M` pointwise. -/
theorem smul_eq_self_of_mem_smulRange {e : R} (he : IsIdempotentElem e) {x : M}
    (hx : x ∈ smulRange S M e) : e • x = x :=
  (mem_smulRange_iff_smul_eq_self he).1 hx

/-- **An element that `r` fixes on the left carries the whole module into `r • M`**: if
`f * r = r` then every multiple of `r` lies in `f • M`. No idempotency is needed. -/
theorem smul_mem_smulRange_of_mul_eq_self {f r : R} (hr : f * r = r) (x : M) :
    r • x ∈ smulRange S M f := by
  rw [← hr, mul_smul]
  exact smul_mem_smulRange f _

/-- **An element that kills `e` on the right annihilates `e • M`**: if `r * e = 0` then `r` sends
every element of `e • M` to zero. No idempotency is needed. -/
theorem smul_eq_zero_of_mul_eq_zero_of_mem_smulRange {r e : R} (hr : r * e = 0) {x : M}
    (hx : x ∈ smulRange S M e) : r • x = 0 := by
  obtain ⟨y, rfl⟩ := mem_smulRange_iff.1 hx
  rw [smul_smul, hr, zero_smul]

end Defs

section Map

variable (S : Type*) {M N P R : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M]
  [AddCommMonoid N] [Module S N] [Module R N] [SMulCommClass R S N]
  [AddCommMonoid P] [Module S P] [Module R P] [SMulCommClass R S P]
  [LinearMap.CompatibleSMul M N S R]

/-- **The pieces are natural in the module**: an `R`-linear map carries `e • M` into `e • N`. -/
theorem smulRange_le_comap (e : R) (f : M →ₗ[R] N) :
    smulRange S M e ≤ (smulRange S N e).comap (f.restrictScalars S) := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_smulRange_iff.1 hx
  exact mem_smulRange_iff.2 ⟨f y, (map_smul f e y).symm⟩

/-- The restriction of an `R`-linear map `M → N` to the pieces cut out by `e`, an `S`-linear map
`e • M → e • N`. This is `TauCeti.smulRange_le_comap` promoted to the map it describes. -/
def smulRangeMap (e : R) (f : M →ₗ[R] N) : smulRange S M e →ₗ[S] smulRange S N e :=
  (f.restrictScalars S).restrict (smulRange_le_comap S e f)

variable {S}

@[simp]
theorem coe_smulRangeMap_apply (e : R) (f : M →ₗ[R] N) (x : smulRange S M e) :
    (smulRangeMap S e f x : N) = f (x : M) :=
  LinearMap.coe_restrict_apply _ x

/-- **The restriction to the pieces is functorial**: the identity restricts to the identity. -/
@[simp]
theorem smulRangeMap_id [LinearMap.CompatibleSMul M M S R] (e : R) :
    smulRangeMap S e (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  simp

/-- **The restriction to the pieces is functorial**: a composite restricts to the composite of the
restrictions. -/
@[simp]
theorem smulRangeMap_comp [LinearMap.CompatibleSMul N P S R] [LinearMap.CompatibleSMul M P S R]
    (e : R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    smulRangeMap S e (g.comp f) = (smulRangeMap S e g).comp (smulRangeMap S e f) := by
  ext x
  simp

end Map

section Orthogonal

variable {S M R ι : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R}

/-- An orthogonal idempotent annihilates the piece cut out by any of the others. -/
theorem smul_eq_zero_of_mem_smulRange (he : OrthogonalIdempotents e)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ smulRange S M (e j)) : e i • x = 0 :=
  smul_eq_zero_of_mul_eq_zero_of_mem_smulRange (he.ortho hij) hx

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
  rw [← smul_eq_self_of_mem_smulRange (he.idem i) hx, hx0]

variable [Fintype ι]

/-- **Completeness is the decomposition of an element**: `x = ∑ᵢ eᵢ • x`. -/
theorem sum_smul_eq_self_of_completeOrthogonalIdempotents
    (he : CompleteOrthogonalIdempotents e) (x : M) :
    ∑ i, e i • x = x := by
  rw [← Finset.sum_smul, he.complete, one_smul]

/-- The pieces cut out by a complete orthogonal family span the module. -/
theorem iSup_smulRange_eq_top (he : CompleteOrthogonalIdempotents e) :
    (⨆ i, smulRange S M (e i)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [← sum_smul_eq_self_of_completeOrthogonalIdempotents he x]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (smul_mem_smulRange (e i) x)

end Orthogonal

section Internal

variable {S M R ι : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R}
  [DecidableEq ι]

/-- **Multiplying by `eⱼ` reads off the `j`-th component of a sum**: in `∑ᵢ zᵢ` with `zᵢ ∈ eᵢ M`,
the idempotent `eⱼ` fixes the term at `j` and annihilates all the others. This is what makes the
sum direct. -/
theorem smul_coeLinearMap_smulRange (he : OrthogonalIdempotents e)
    (z : ⨁ i, smulRange S M (e i)) (j : ι) :
    e j • DirectSum.coeLinearMap (fun i => smulRange S M (e i)) z = (z j : M) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rcases eq_or_ne j i with rfl | hji
    · rw [DirectSum.coeLinearMap_of, DirectSum.of_eq_same,
        smul_eq_self_of_mem_smulRange (he.idem j) x.2]
    · rw [DirectSum.coeLinearMap_of, DirectSum.of_eq_of_ne _ _ _ hji,
        smul_eq_zero_of_mem_smulRange he hji x.2, ZeroMemClass.coe_zero]
  | add z w hz hw =>
    rw [map_add, smul_add, hz, hw, DFinsupp.add_apply, Submodule.coe_add]

variable [Fintype ι]

/-- **A complete orthogonal family of idempotents decomposes every module**: `M = ⨁ᵢ eᵢ M`.

The `S`-submodule at `i` is `eᵢ • M`, and the component of `x` there is `eᵢ • x`. Injectivity is
`TauCeti.smul_coeLinearMap_smulRange`, which recovers each component from the sum, and
surjectivity is spanning, `TauCeti.iSup_smulRange_eq_top`. -/
theorem isInternal_smulRange (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal fun i => smulRange S M (e i) := by
  -- `DirectSum.IsInternal` is bijectivity of `DirectSum.coeAddMonoidHom`, which is the underlying
  -- function of `DirectSum.coeLinearMap`. Mathlib's
  -- `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` cannot be used to assemble it from
  -- `TauCeti.iSupIndep_smulRange` and `TauCeti.iSup_smulRange_eq_top`: it lives in the `Ring`
  -- section of `Mathlib/Algebra/DirectSum/Module.lean` and, as its own note there records, "is not
  -- generally true for `[Semiring R]`", while `S` is only a semiring here. Independence is
  -- therefore replaced by the stronger `TauCeti.smul_coeLinearMap_smulRange`, which recovers each
  -- component of a sum outright; only surjectivity goes through Mathlib.
  refine ⟨fun z w hzw => DFinsupp.ext fun j => Subtype.ext ?_, ?_⟩
  · replace hzw : DirectSum.coeLinearMap (fun i => smulRange S M (e i)) z
        = DirectSum.coeLinearMap (fun i => smulRange S M (e i)) w := hzw
    rw [← smul_coeLinearMap_smulRange he.toOrthogonalIdempotents z j,
      ← smul_coeLinearMap_smulRange he.toOrthogonalIdempotents w j, hzw]
  · exact (LinearMap.range_eq_top
      (f := DirectSum.coeLinearMap fun i => smulRange S M (e i))).1 (by
        rw [DirectSum.range_coeLinearMap, iSup_smulRange_eq_top he])

/-- **The component of `x` at `i` is `eᵢ • x`**: this is the inverse of the decomposition, read
off one index at a time. The isomorphism `⨁ᵢ eᵢ M ≃ₗ[S] M` is the canonical
`LinearEquiv.ofBijective (DirectSum.coeLinearMap _)` of an internal direct sum, so Mathlib's
`DirectSum.IsInternal.ofBijective_coeLinearMap_same` and friends apply to it as well. -/
@[simp]
theorem coe_isInternal_smulRange_symm_apply (he : CompleteOrthogonalIdempotents e) (x : M)
    (i : ι) :
    (((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => smulRange S M (e i))
      (isInternal_smulRange he)).symm x i : smulRange S M (e i)) : M) = e i • x := by
  have h : DirectSum.coeLinearMap (fun i => smulRange S M (e i))
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => smulRange S M (e i))
        (isInternal_smulRange he)).symm x) = x :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => smulRange S M (e i))
      (isInternal_smulRange he)).apply_symm_apply x
  rw [← smul_coeLinearMap_smulRange he.toOrthogonalIdempotents _ i, h]

end Internal

section Finrank

variable {S M R ι : Type*} [DivisionRing S] [Semiring R]
  [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R} [Fintype ι]

/-- **The dimension count**: for a module finite-dimensional over a division ring `S`, the
dimensions of the pieces add up to the dimension of the module. -/
theorem finrank_eq_sum_finrank_smulRange [Module.Finite S M]
    (he : CompleteOrthogonalIdempotents e) :
    Module.finrank S M = ∑ i, Module.finrank S (smulRange S M (e i) : Submodule S M) := by
  classical
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => smulRange S M (e i))
    (isInternal_smulRange he)).finrank_eq, Module.finrank_directSum]

end Finrank

end TauCeti
