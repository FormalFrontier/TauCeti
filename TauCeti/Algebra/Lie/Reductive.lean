/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.Weights.Central
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Reductive Lie algebras: the centre and the derived ideal span

A finite-dimensional Lie algebra `L` over a field of characteristic zero is **reductive** when its
solvable radical is its centre, Mathlib's `LieAlgebra.HasCentralRadical`. This file proves that a
reductive Lie algebra is spanned by its centre and its derived ideal,

`center K L ⊔ ⁅L, L⁆ = ⊤`  (`TauCeti.sup_center_derivedSeries_eq_top`),

and draws the consequences the representation theory of a reductive Lie algebra runs on: the
derived ideal is perfect, equivariance of a linear map may be tested on the centre and on the
derived ideal, and a finite-dimensional irreducible module over `L` stays irreducible over the
derived ideal (`TauCeti.isIrreducible_restrict_derivedSeries`).

## The argument

Everything comes from the Killing form `κ` and its orthogonal complements
(`LieIdeal.killingCompl`). Cartan's criterion, in the form
`LieAlgebra.killingCompl_top_le_radical`, says that the radical of `κ` is contained in the solvable
radical; for a reductive `L` that radical is the centre, and the reverse inclusion is immediate
because a central element has vanishing adjoint action. So the radical of `κ` is the centre
(`TauCeti.killingCompl_top_eq_center`).

The derived ideal has the *same* orthogonal complement
(`TauCeti.killingCompl_derivedSeries_eq_center`). Indeed the invariance `κ ⁅x, y⁆ z = κ x ⁅y, z⁆`
turns "`x` is orthogonal to every bracket" into "`⁅y, x⁆` is orthogonal to everything", that is
into `⁅y, x⁆ ∈ center K L` for every `y`. The elements with that property are the normalizer of the
centre, an ideal whose derived ideal is central and therefore abelian: it is a solvable ideal, so
reductivity puts it back inside the centre. This is `TauCeti.normalizer_center_eq_center`.

Two subspaces of a finite-dimensional space with the same orthogonal complement for a symmetric
form need not be equal — but they are if both contain the radical of the form, and the dimension
formula `LinearMap.BilinForm.finrank_add_finrank_orthogonal` makes that precise. Applied to
`center K L ⊔ ⁅L, L⁆`, whose orthogonal complement is the centre by the two computations above and
which contains the centre for trivial reasons, it forces that ideal to be everything.

## What is not proved here

The full structure theorem asks for more, namely that the sum is **direct** and that the derived
ideal is semisimple. That half is not a formal consequence of what is proved here: it amounts to
the vanishing of `H²` of a semisimple Lie algebra, equivalently to Weyl's complete reducibility
theorem applied to the adjoint action of `L` on itself, and the complete reducibility available in
`TauCeti/Algebra/Lie/HighestWeight/CompleteReducibility.lean` is stated for a Lie algebra with
*nondegenerate* Killing form over an algebraically closed field, which a reductive `L` is not. The
spanning half proved here supplies data needed for the eventual classification of irreducible
modules; for the concrete `gl n`, where the sum really is direct, that stronger statement is
available as `TauCeti.isCompl_center_derivedSeries_one_matrix`.

## Main results

* `TauCeti.normalizer_center_eq_center`: over a reductive Lie algebra the centre is its own
  normalizer, because the normalizer is a solvable ideal
  (`TauCeti.isSolvable_normalizer_center`).
* `TauCeti.killingCompl_top_eq_center` and `TauCeti.killingCompl_derivedSeries_eq_center`: the
  radical of the Killing form and the orthogonal complement of the derived ideal are both the
  centre.
* `TauCeti.sup_center_derivedSeries_eq_top`: **the centre and the derived ideal span**,
  `center K L ⊔ ⁅L, L⁆ = ⊤`, with `TauCeti.exists_mem_center_add_mem_derivedSeries` its
  elementwise form.
* `TauCeti.lie_derivedSeries_derivedSeries_eq_self`: **the derived ideal is perfect.**
* `TauCeti.map_lie_of_forall_center_of_forall_derivedSeries` and
  `TauCeti.lieModuleEquivOfCenterOfDerivedSeries`: a linear map equivariant for the centre and for
  the derived ideal is equivariant for `L`, so a derived-ideal equivalence between modules on which
  the centre acts by the same scalars is an `L`-equivalence.
* `TauCeti.isIrreducible_restrict_derivedSeries`: **a finite-dimensional irreducible module over a
  reductive Lie algebra restricts to an irreducible module over the derived ideal**, over an
  algebraically closed field.

## Roadmap

This is the spanning half of "the structure of reductive Lie algebras" and the "semisimple part
acts irreducibly" target of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, whose pinned names are
`hasCentralRadical_iff_isCompl_center_derivedSeries` and `isIrreducible_restrict_derivedSeries`.
Together with `TauCeti.exists_centralWeight_of_isIrreducible` of
`TauCeti/Algebra/Lie/Weights/Central.lean`, it shows that every finite-dimensional irreducible of a
reductive Lie algebra determines an irreducible restricted module and a central weight.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6.4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5 and §6.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w w'

/-! ### The centre is its own normalizer -/

section Normalizer

variable (K : Type u) (L : Type v) [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The elements `x` for which `⁅y, x⁆` is central for every `y` — that is, the normalizer of the
centre — form a **solvable** ideal: its derived ideal is central, hence abelian. -/
theorem isSolvable_normalizer_center :
    LieAlgebra.IsSolvable ((LieAlgebra.center K L).normalizer) := by
  have hle : ⁅(LieAlgebra.center K L).normalizer, (LieAlgebra.center K L).normalizer⁆ ≤
      LieAlgebra.center K L :=
    (LieSubmodule.lie_le_iff _ _ _).2 fun x _ y hy ↦
      (LieSubmodule.mem_normalizer _ y).1 hy x
  have hcentral : ⁅LieAlgebra.center K L, LieAlgebra.center K L⁆ = (⊥ : LieIdeal K L) :=
    le_bot_iff.1 <| (LieSubmodule.lie_le_iff _ _ _).2 fun x hx y _ ↦ by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L x).1 hx y, neg_zero]
      exact LieSubmodule.zero_mem _
  refine LieAlgebra.IsSolvable.mk (R := K) (k := 2)
    ((LieIdeal.derivedSeries_eq_bot_iff _ 2).2 ?_)
  rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    ← le_bot_iff, ← hcentral]
  exact LieSubmodule.mono_lie hle hle

variable [IsNoetherian K L] [LieAlgebra.HasCentralRadical K L]

/-- **Over a reductive Lie algebra the centre is its own normalizer.** The normalizer is a solvable
ideal by `TauCeti.isSolvable_normalizer_center`, hence lies in the radical, which is the centre. -/
theorem normalizer_center_eq_center :
    (LieAlgebra.center K L).normalizer = LieAlgebra.center K L := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  have h := (LieIdeal.solvable_iff_le_radical K L (LieAlgebra.center K L).normalizer).1
    (isSolvable_normalizer_center K L)
  rwa [LieAlgebra.radical_eq_center] at h

/-- A convenient elementwise form of `TauCeti.normalizer_center_eq_center`: over a reductive Lie
algebra, if every bracket `⁅y, x⁆` is central, then `x` itself is central. -/
theorem mem_center_of_forall_lie_mem_center {x : L}
    (h : ∀ y : L, ⁅y, x⁆ ∈ LieAlgebra.center K L) : x ∈ LieAlgebra.center K L :=
  normalizer_center_eq_center K L ▸ (LieSubmodule.mem_normalizer _ x).2 h

end Normalizer

/-! ### The Killing form sees only the centre -/

section KillingCompl

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]

/-- **For a reductive Lie algebra the radical of the Killing form is the centre.** One inclusion is
Cartan's criterion `LieAlgebra.killingCompl_top_le_radical` together with reductivity; the other
holds because a central element acts by zero. -/
theorem killingCompl_top_eq_center :
    LieIdeal.killingCompl K L ⊤ = LieAlgebra.center K L := by
  refine le_antisymm ?_ fun z hz ↦ ?_
  · simpa [LieAlgebra.radical_eq_center] using LieAlgebra.killingCompl_top_le_radical K L
  · refine (LieIdeal.mem_killingCompl K L ⊤).2 fun y _ ↦ ?_
    have hz' : LieAlgebra.ad K L z = 0 := by
      ext w
      rw [LieAlgebra.ad_apply, ← lie_skew, (LieModule.mem_maxTrivSubmodule K L L z).1 hz w]
      simp
    rw [LieModule.traceForm_comm, killingForm_apply_apply, hz']
    simp

variable {K L}

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L] in
/-- An element orthogonal to the derived ideal brackets into the radical of the Killing form: this
is the invariance `κ ⁅x, y⁆ z = κ x ⁅y, z⁆` read from right to left. -/
theorem lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries {x : L}
    (hx : x ∈ LieIdeal.killingCompl K L (derivedSeries K L 1)) (y : L) :
    ⁅y, x⁆ ∈ LieIdeal.killingCompl K L ⊤ := by
  refine (LieIdeal.mem_killingCompl K L ⊤).2 fun z _ ↦ ?_
  have hyz : ⁅z, y⁆ ∈ derivedSeries K L 1 :=
    LieSubmodule.lie_mem_lie (LieSubmodule.mem_top z) (LieSubmodule.mem_top y)
  have hinv := LieModule.traceForm_apply_lie_apply K L L z y x
  rw [← hinv]
  exact (LieIdeal.mem_killingCompl K L _).1 hx _ hyz

variable (K L)

/-- **The derived ideal of a reductive Lie algebra has the centre as its orthogonal complement.**
Nothing beyond the radical of the Killing form is orthogonal to the derived ideal: an element
orthogonal to it normalizes the centre by
`TauCeti.lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries`, hence is central. -/
theorem killingCompl_derivedSeries_eq_center :
    LieIdeal.killingCompl K L (derivedSeries K L 1) = LieAlgebra.center K L := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · refine mem_center_of_forall_lie_mem_center K L fun y ↦ ?_
    rw [← killingCompl_top_eq_center K L]
    exact lie_mem_killingCompl_top_of_mem_killingCompl_derivedSeries hx y
  · rw [← killingCompl_top_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y _ ↦
      (LieIdeal.mem_killingCompl K L ⊤).1 hx y (LieSubmodule.mem_top y)

/-- The orthogonal complement of the centre together with the derived ideal is again the centre:
it is squeezed between the complements of the derived ideal and of the whole algebra, which
`TauCeti.killingCompl_derivedSeries_eq_center` and `TauCeti.killingCompl_top_eq_center` identify
with one another. -/
theorem killingCompl_sup_center_derivedSeries_eq_center :
    LieIdeal.killingCompl K L (LieAlgebra.center K L ⊔ derivedSeries K L 1)
      = LieAlgebra.center K L := by
  refine le_antisymm ?_ ?_
  · rw [← killingCompl_derivedSeries_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y hy ↦
      (LieIdeal.mem_killingCompl K L _).1 hx y (le_sup_right (α := LieIdeal K L) hy)
  · rw [← killingCompl_top_eq_center K L]
    exact fun _ hx ↦ (LieIdeal.mem_killingCompl K L _).2 fun y _ ↦
      (LieIdeal.mem_killingCompl K L ⊤).1 hx y (LieSubmodule.mem_top y)

end KillingCompl

/-! ### The centre and the derived ideal span -/

section Span

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]

/-- **The centre and the derived ideal of a reductive Lie algebra span it**: `L = Z(L) + ⁅L, L⁆`.

The ideal `center K L ⊔ ⁅L, L⁆` and the whole algebra have the same orthogonal complement for the
Killing form, namely the centre, and both contain the radical of that form. The dimension formula
`LinearMap.BilinForm.finrank_add_finrank_orthogonal` then equates their dimensions. -/
theorem sup_center_derivedSeries_eq_top :
    LieAlgebra.center K L ⊔ derivedSeries K L 1 = (⊤ : LieIdeal K L) := by
  have hrefl : (killingForm K L).IsRefl := (LieModule.traceForm_isSymm K L L).isRefl
  set Z : Submodule K L := LieSubmodule.toSubmodule (LieAlgebra.center K L) with hZ
  set U : Submodule K L :=
    LieSubmodule.toSubmodule (LieAlgebra.center K L ⊔ derivedSeries K L 1) with hU
  have hZU : Z ≤ U := by
    rw [hZ, hU, LieSubmodule.sup_toSubmodule]
    exact le_sup_left
  have hortho : (killingForm K L).orthogonal U = Z := by
    rw [hU, hZ, ← LieIdeal.toSubmodule_killingCompl,
      killingCompl_sup_center_derivedSeries_eq_center K L]
  have htop : (killingForm K L).orthogonal ⊤ = Z := by
    rw [hZ, ← LieSubmodule.top_toSubmodule (R := K) (L := L) (M := L),
      ← LieIdeal.toSubmodule_killingCompl, killingCompl_top_eq_center K L]
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (B := killingForm K L) hrefl U
  rw [hortho, htop, inf_eq_right.2 hZU] at hdim
  rw [← LieSubmodule.toSubmodule_eq_top, ← hU]
  exact Submodule.eq_top_of_finrank_eq (by omega)

/-- Every element of a reductive Lie algebra is a central element plus an element of the derived
ideal. -/
theorem exists_mem_center_add_mem_derivedSeries (x : L) :
    ∃ z ∈ LieAlgebra.center K L, ∃ d ∈ derivedSeries K L 1, z + d = x := by
  have hx : x ∈ (LieAlgebra.center K L ⊔ derivedSeries K L 1 : LieIdeal K L) := by
    rw [sup_center_derivedSeries_eq_top K L]
    exact LieSubmodule.mem_top x
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule] at hx
  exact Submodule.mem_sup.1 hx

/-- **The derived ideal of a reductive Lie algebra is perfect**: `⁅⁅L, L⁆, ⁅L, L⁆⁆ = ⁅L, L⁆`. A
central element contributes nothing to a bracket, so writing both arguments of a generating bracket
of `⁅L, L⁆` as a central element plus an element of `⁅L, L⁆` leaves only the brackets of the derived
ideal with itself. -/
theorem lie_derivedSeries_derivedSeries_eq_self :
    ⁅derivedSeries K L 1, derivedSeries K L 1⁆ = derivedSeries K L 1 := by
  refine le_antisymm (LieSubmodule.lie_le_right _ _) ?_
  have hDtop : derivedSeries K L 1 = ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := rfl
  rw [hDtop]
  refine (LieSubmodule.lie_le_iff _ _ _).2 fun y _ z _ ↦ ?_
  obtain ⟨zy, hzy, dy, hdy, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L y
  obtain ⟨zz, hzz, dz, hdz, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L z
  have hzy0 : ∀ w : L, ⁅zy, w⁆ = 0 := fun w ↦ by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule K L L zy).1 hzy w, neg_zero]
  have hzz0 : ∀ w : L, ⁅w, zz⁆ = 0 := (LieModule.mem_maxTrivSubmodule K L L zz).1 hzz
  rw [add_lie, hzy0, lie_add, hzz0, zero_add, zero_add]
  exact LieSubmodule.lie_mem_lie hdy hdz

end Span

/-! ### Modules over a reductive Lie algebra -/

section Modules

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasCentralRadical K L]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {N : Type w'} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

omit [LieModule K L M] [LieModule K L N] in
/-- **Equivariance is tested on the centre and on the derived ideal.** A linear map between
`L`-modules commuting with the action of every central element and of every element of `⁅L, L⁆`
commutes with the action of `L`, because those two ideals span
(`TauCeti.sup_center_derivedSeries_eq_top`). -/
theorem map_lie_of_forall_center_of_forall_derivedSeries (f : M →ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, f ⁅z, m⁆ = ⁅z, f m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, f ⁅d, m⁆ = ⁅d, f m⁆) (x : L) (m : M) :
    f ⁅x, m⁆ = ⁅x, f m⁆ := by
  obtain ⟨z, hz, d, hd, rfl⟩ := exists_mem_center_add_mem_derivedSeries K L x
  rw [add_lie, map_add, hZ z hz, hD d hd, add_lie]

/-- A linear equivalence which is equivariant for the derived ideal and for the centre is an
equivalence of `L`-modules. This is the dictionary through which the representation theory of the
derived ideal — the semisimple part — reaches `L`: the centre contributes only the scalars recorded
by `TauCeti.centralWeight`. -/
def lieModuleEquivOfCenterOfDerivedSeries (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) :
    M ≃ₗ⁅K, L⁆ N where
  __ := e
  map_lie' {x m} :=
    map_lie_of_forall_center_of_forall_derivedSeries K L (e : M →ₗ[K] N) hZ hD x m

omit [LieModule K L M] [LieModule K L N] in
@[simp]
theorem lieModuleEquivOfCenterOfDerivedSeries_apply (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) (m : M) :
    lieModuleEquivOfCenterOfDerivedSeries K L e hZ hD m = e m :=
  (rfl)

omit [LieModule K L M] [LieModule K L N] in
@[simp]
theorem lieModuleEquivOfCenterOfDerivedSeries_symm_apply (e : M ≃ₗ[K] N)
    (hZ : ∀ z ∈ LieAlgebra.center K L, ∀ m : M, e ⁅z, m⁆ = ⁅z, e m⁆)
    (hD : ∀ d ∈ derivedSeries K L 1, ∀ m : M, e ⁅d, m⁆ = ⁅d, e m⁆) (n : N) :
    (lieModuleEquivOfCenterOfDerivedSeries K L e hZ hD).symm n = e.symm n :=
  (rfl)

variable (M) [IsAlgClosed K] [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

/-- **The semisimple part acts irreducibly.** A finite-dimensional irreducible module over a
reductive Lie algebra, over an algebraically closed field, restricts to an irreducible module over
the derived ideal.

The centre acts by scalars (`TauCeti.exists_centralWeight_of_isIrreducible`), so every subspace of
`M` is stable under it; since the centre and the derived ideal span, a submodule for the derived
ideal is already a submodule for `L`. Algebraic closedness is essential and not a convenience: over
`ℝ` the one-dimensional abelian Lie algebra acting on `ℝ²` by the rotation generator is
irreducible, is its own centre, and has zero derived ideal.

Together with the central weight, this shows that every finite-dimensional irreducible determines
an irreducible restricted module and a functional on the centre; reconstruction and uniqueness are
not asserted here. -/
theorem isIrreducible_restrict_derivedSeries :
    LieModule.IsIrreducible K (derivedSeries K L 1) M :=
  isIrreducible_of_sup_center_eq_top K L M (derivedSeries K L 1) <| by
    have h := congrArg LieSubmodule.toSubmodule (sup_center_derivedSeries_eq_top K L)
    rw [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule] at h
    rw [← h, sup_comm]
    rfl

end Modules

end TauCeti
