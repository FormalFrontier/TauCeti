/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Idempotents
public import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# A complete family of orthogonal idempotents decomposes every module

Let `R` be a semiring and let `e : ι → R` be a *complete orthogonal family of idempotents*:
`eᵢ eⱼ = 0` for `i ≠ j` and `∑ᵢ eᵢ = 1`. Then every left `R`-module `M` splits as an internal
direct sum of the `S`-submodules `eᵢ • M`,

`M = ⨁ᵢ eᵢ M`,

the component of `x` in position `i` being `eᵢ • x`. This file proves that
(`TauCeti.isInternal_smul_top`) and records the dimension count `dim M = ∑ᵢ dim (eᵢ M)` that
follows over a division ring.

Mathlib has the family (`CompleteOrthogonalIdempotents`) and the converse direction — a
decomposition of `R` itself into left ideals produces such a family
(`DirectSum.completeOrthogonalIdempotents_idempotent`) — but not the decomposition of an arbitrary
module that the family induces.

## The pieces

The piece `eᵢ M` is Mathlib's pointwise action `e i • (⊤ : Submodule S M)` (scoped in `Pointwise`),
so no new definition is introduced for it and Mathlib's pointwise API —
`Submodule.pointwise_smul_def`, `Submodule.mem_smul_pointwise_iff_exists`,
`Submodule.smul_mem_pointwise_smul` — applies to the statements below as it stands.

## The two scalar rings

The pieces `eᵢ • M` are *not* `R`-submodules: `R` is noncommutative in the intended applications,
and `r • (eᵢ • x)` need not lie in `eᵢ • M`. They are submodules over any second ring `S` whose
action on `M` commutes with that of `R`, that is, under `SMulCommClass R S M`, which is exactly
what makes multiplication by `e` an `S`-linear map (`DistribSMul.toLinearMap`) and is exactly the
hypothesis of Mathlib's pointwise action on `Submodule S M`; carrying that ambient `S` is what
makes the dimension count below available. Taking `S = ℕ` recovers the decomposition as additive
submonoids, and an `S`-algebra structure on `R` together with `IsScalarTower S R M` supplies the
hypothesis in the intended applications.

## Main definitions

* `TauCeti.smulTopMap S e f`: the restriction of an `R`-linear map `f : M →ₗ[R] N` to
  `e • M →ₗ[S] e • N`.

## Main results

* `TauCeti.mem_smul_top_iff_smul_eq_self`: for an idempotent `e`, membership in `e • M` is the
  fixed-point condition `e • x = x`. This is the form every proof below uses, and it is what makes
  `e • M` a *summand* rather than a mere image.
* `TauCeti.isInternal_smul_top`: **the decomposition** `M = ⨁ᵢ eᵢ M`, with the component of `x` at
  `i` being `eᵢ • x` (`TauCeti.coe_ofBijective_coeLinearMap_symm_apply_smul_top`).
* `TauCeti.smul_coeLinearMap_smul_top`: multiplying by `eᵢ` reads off the `i`-th component of a
  sum. This is what makes the sum direct.
* `TauCeti.finrank_eq_sum_finrank_smul_top`: for a module finite-dimensional over a division
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

open scoped DirectSum Pointwise

section Defs

variable {S M R : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M]

/-- **Membership in `e • M` for an idempotent `e` is a fixed-point condition.** This is Mathlib's
`LinearMap.IsIdempotentElem.mem_range_iff` for the idempotent endomorphism `x ↦ e • x`, whose range
is the piece `e • M`. -/
theorem mem_smul_top_iff_smul_eq_self {e : R} (he : IsIdempotentElem e) {x : M} :
    x ∈ e • (⊤ : Submodule S M) ↔ e • x = x := by
  rw [Submodule.pointwise_smul_def, Submodule.map_top]
  exact LinearMap.IsIdempotentElem.mem_range_iff (he.map (Module.toModuleEnd S M))

/-- Multiplication by an idempotent `e` fixes `e • M` pointwise. -/
theorem smul_eq_self_of_mem_smul_top {e : R} (he : IsIdempotentElem e) {x : M}
    (hx : x ∈ e • (⊤ : Submodule S M)) : e • x = x :=
  (mem_smul_top_iff_smul_eq_self he).1 hx

/-- **An element `r` fixed on the left by `f` carries the whole module into `f • M`**: if
`f * r = r` then every multiple of `r` lies in `f • M`. No idempotency is needed. -/
theorem smul_mem_smul_top_of_mul_eq_self {f r : R} (hr : f * r = r) (x : M) :
    r • x ∈ f • (⊤ : Submodule S M) := by
  rw [← hr, mul_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

/-- **An element that kills `e` on the right annihilates `e • M`**: if `r * e = 0` then `r` sends
every element of `e • M` to zero. No idempotency is needed. -/
theorem smul_eq_zero_of_mul_eq_zero_of_mem_smul_top {r e : R} (hr : r * e = 0) {x : M}
    (hx : x ∈ e • (⊤ : Submodule S M)) : r • x = 0 := by
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [smul_smul, hr, zero_smul]

end Defs

section Map

variable (S : Type*) {M N P R : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M]
  [AddCommMonoid N] [Module S N] [Module R N] [SMulCommClass R S N]
  [AddCommMonoid P] [Module S P] [Module R P] [SMulCommClass R S P]
  [LinearMap.CompatibleSMul M N S R]

/-- **The pieces are natural in the module**: an `R`-linear map carries `e • M` into `e • N`. -/
theorem smul_top_le_comap_smul_top (e : R) (f : M →ₗ[R] N) :
    e • (⊤ : Submodule S M) ≤ (e • (⊤ : Submodule S N)).comap (f.restrictScalars S) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

/-- The restriction of an `R`-linear map `M → N` to the pieces cut out by `e`, an `S`-linear map
`e • M → e • N`. This is `TauCeti.smul_top_le_comap_smul_top` promoted to the map it describes. -/
def smulTopMap (e : R) (f : M →ₗ[R] N) :
    ↥(e • (⊤ : Submodule S M)) →ₗ[S] ↥(e • (⊤ : Submodule S N)) :=
  (f.restrictScalars S).restrict (smul_top_le_comap_smul_top S e f)

variable {S}

@[simp]
theorem coe_smulTopMap_apply (e : R) (f : M →ₗ[R] N) (x : ↥(e • (⊤ : Submodule S M))) :
    (smulTopMap S e f x : N) = f (x : M) :=
  LinearMap.coe_restrict_apply _ x

/-- **The restriction to the pieces is functorial**: the identity restricts to the identity. -/
@[simp]
theorem smulTopMap_id [LinearMap.CompatibleSMul M M S R] (e : R) :
    smulTopMap S e (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  simp

/-- **The restriction to the pieces is functorial**: a composite restricts to the composite of the
restrictions. -/
@[simp]
theorem smulTopMap_comp [LinearMap.CompatibleSMul N P S R] [LinearMap.CompatibleSMul M P S R]
    (e : R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    smulTopMap S e (g.comp f) = (smulTopMap S e g).comp (smulTopMap S e f) := by
  ext x
  simp

end Map

section Orthogonal

variable {S M R ι : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R}

/-- An orthogonal idempotent annihilates the piece cut out by any of the others. -/
theorem smul_eq_zero_of_ne_of_mem_smul_top (he : OrthogonalIdempotents e)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ e j • (⊤ : Submodule S M)) : e i • x = 0 :=
  smul_eq_zero_of_mul_eq_zero_of_mem_smul_top (he.ortho hij) hx

/-- The pieces cut out by an orthogonal family are independent: the piece at `i` meets the
supremum of the others only in `0`, because `eᵢ` fixes the former and kills the latter. -/
theorem iSupIndep_smul_top (he : OrthogonalIdempotents e) :
    iSupIndep fun i => e i • (⊤ : Submodule S M) := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hker : (⨆ j, ⨆ _ : j ≠ i, e j • (⊤ : Submodule S M))
      ≤ LinearMap.ker (DistribSMul.toLinearMap S M (e i)) :=
    iSup_le fun j => iSup_le fun hj y hy =>
      LinearMap.mem_ker.2 (smul_eq_zero_of_ne_of_mem_smul_top he (Ne.symm hj) hy)
  have hx0 : e i • x = 0 := LinearMap.mem_ker.1 (hker hx')
  rw [← smul_eq_self_of_mem_smul_top (he.idem i) hx, hx0]

variable [Fintype ι]

/-- **A decomposition of the unit decomposes every element**: if `∑ᵢ eᵢ = 1` then `x = ∑ᵢ eᵢ • x`.
Neither idempotency nor orthogonality is needed. -/
theorem sum_smul_eq_self_of_sum_eq_one (he : ∑ i, e i = 1) (x : M) :
    ∑ i, e i • x = x := by
  rw [← Finset.sum_smul, he, one_smul]

/-- The pieces cut out by a decomposition of the unit span the module. -/
theorem iSup_smul_top_eq_top_of_sum_eq_one (he : ∑ i, e i = 1) :
    (⨆ i, e i • (⊤ : Submodule S M)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [← sum_smul_eq_self_of_sum_eq_one he x]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (Submodule.smul_mem_pointwise_smul _ _ _ trivial)

end Orthogonal

section Internal

variable {S M R ι : Type*} [Semiring S] [Semiring R]
  [AddCommMonoid M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R}
  [DecidableEq ι]

/-- **Multiplying by `eⱼ` reads off the `j`-th component of a sum**: in `∑ᵢ zᵢ` with `zᵢ ∈ eᵢ M`,
the idempotent `eⱼ` fixes the term at `j` and annihilates all the others. This is what makes the
sum direct. -/
theorem smul_coeLinearMap_smul_top (he : OrthogonalIdempotents e)
    (z : ⨁ i, ↥(e i • (⊤ : Submodule S M))) (j : ι) :
    e j • DirectSum.coeLinearMap (fun i => e i • (⊤ : Submodule S M)) z = (z j : M) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rcases eq_or_ne j i with rfl | hji
    · rw [DirectSum.coeLinearMap_of, DirectSum.of_eq_same,
        smul_eq_self_of_mem_smul_top (he.idem j) x.2]
    · rw [DirectSum.coeLinearMap_of, DirectSum.of_eq_of_ne _ _ _ hji,
        smul_eq_zero_of_ne_of_mem_smul_top he hji x.2, ZeroMemClass.coe_zero]
  | add z w hz hw =>
    rw [map_add, smul_add, hz, hw, DFinsupp.add_apply, Submodule.coe_add]

variable [Fintype ι]

/-- **A complete orthogonal family of idempotents decomposes every module**: `M = ⨁ᵢ eᵢ M`.

The `S`-submodule at `i` is `eᵢ • M`, and the component of `x` there is `eᵢ • x`. -/
theorem isInternal_smul_top (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal fun i => e i • (⊤ : Submodule S M) := by
  -- `DirectSum.IsInternal` is bijectivity of `DirectSum.coeAddMonoidHom`, which is the underlying
  -- function of `DirectSum.coeLinearMap`. Mathlib's
  -- `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` cannot be used to assemble it from
  -- `TauCeti.iSupIndep_smul_top` and `TauCeti.iSup_smul_top_eq_top_of_sum_eq_one`: it lives in the
  -- `Ring` section of `Mathlib/Algebra/DirectSum/Module.lean` and, as its own note there records,
  -- "is not generally true for `[Semiring R]`", while `S` is only a semiring here. Independence is
  -- therefore replaced by the stronger `TauCeti.smul_coeLinearMap_smul_top`, which recovers each
  -- component of a sum outright; only surjectivity goes through Mathlib.
  refine ⟨fun z w hzw => DFinsupp.ext fun j => Subtype.ext ?_, ?_⟩
  · replace hzw : DirectSum.coeLinearMap (fun i => e i • (⊤ : Submodule S M)) z
        = DirectSum.coeLinearMap (fun i => e i • (⊤ : Submodule S M)) w := hzw
    rw [← smul_coeLinearMap_smul_top he.toOrthogonalIdempotents z j,
      ← smul_coeLinearMap_smul_top he.toOrthogonalIdempotents w j, hzw]
  · exact (LinearMap.range_eq_top
      (f := DirectSum.coeLinearMap fun i => e i • (⊤ : Submodule S M))).1 (by
        rw [DirectSum.range_coeLinearMap, iSup_smul_top_eq_top_of_sum_eq_one he.complete])

/-- **The component of `x` at `i` is `eᵢ • x`**: this is the inverse of the decomposition, read
off one index at a time. The isomorphism `⨁ᵢ eᵢ M ≃ₗ[S] M` is the canonical
`LinearEquiv.ofBijective (DirectSum.coeLinearMap _)` of an internal direct sum, so Mathlib's
`DirectSum.IsInternal.ofBijective_coeLinearMap_same` and friends apply to it as well. -/
@[simp]
theorem coe_ofBijective_coeLinearMap_symm_apply_smul_top (he : CompleteOrthogonalIdempotents e)
    (x : M) (i : ι) :
    (((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => e i • (⊤ : Submodule S M))
      (isInternal_smul_top he)).symm x i : ↥(e i • (⊤ : Submodule S M))) : M)
      = e i • x := by
  have h : DirectSum.coeLinearMap (fun i => e i • (⊤ : Submodule S M))
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => e i • (⊤ : Submodule S M))
        (isInternal_smul_top he)).symm x) = x :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => e i • (⊤ : Submodule S M))
      (isInternal_smul_top he)).apply_symm_apply x
  rw [← smul_coeLinearMap_smul_top he.toOrthogonalIdempotents _ i, h]

end Internal

section Finrank

variable {S M R ι : Type*} [DivisionRing S] [Semiring R]
  [AddCommGroup M] [Module S M] [Module R M] [SMulCommClass R S M] {e : ι → R} [Fintype ι]

/-- **The dimension count**: for a module finite-dimensional over a division ring `S`, the
dimensions of the pieces add up to the dimension of the module. -/
theorem finrank_eq_sum_finrank_smul_top [Module.Finite S M]
    (he : CompleteOrthogonalIdempotents e) :
    Module.finrank S M
      = ∑ i, Module.finrank S ↥(e i • (⊤ : Submodule S M)) := by
  classical
  exact finrank_eq_sum_finrank_of_isInternal (isInternal_smul_top he)

end Finrank

end TauCeti
