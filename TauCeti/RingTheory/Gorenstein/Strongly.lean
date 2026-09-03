/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Strongly Gorenstein projective, injective and flat modules

Bennis–Mahdou, *Strongly Gorenstein projective, injective and flat modules*,
J. Pure Appl. Algebra **210** (2007), 437–445. DOI `10.1016/j.jpaa.2006.10.010`.
Formalization of Def. 1.1 (characterizations `⋯ → P -f→ P -f→ P → ⋯`).

A module `M` is **strongly Gorenstein projective** if there is a strongly
*complete* projective resolution `⋯ → P -f→ P -f→ P → ⋯`: `P` projective,
the complex exact (`ker f = range f`, since the complex is `f`-periodic a
single exactness condition at `P` suffices), **and** `Hom(-,Q)` leaves the
complex exact for every projective `Q` — this second condition is what makes
the resolution *complete* rather than merely exact, and it is not implied by
the first (an ordinary periodic exact complex of projectives need not stay
exact after `Hom(-,Q)`). Then `M ≃ Im(f)`. The injective and flat cases
(Def. 1.1(2), 1.1(3)) are dual: `Hom(E,-)` resp. `I ⊗ -` must leave the
complex exact, for every injective `E` resp. `I`.

The completeness conditions are stated intrinsically, as exactness of a `Hom`
or tensor complex, which keeps them inside `Module R`. They are equivalent to
the vanishing of `Ext¹(M, Q)` for projective `Q` (and its duals), which is how
Bennis–Mahdou state them; mathlib's `Ext` is defined for abelian categories,
so that comparison passes through `ModuleCat R`. The comparison itself, and
Thm 1.4's resulting `0 → M → P → M → 0` characterization, are a separate
milestone and are not proved here.

Every definition below is exercised: `isStronglyGorensteinProjective_of_projective`
constructs a witness, and the three `exists_` lemmas show the predicates are
restrictive rather than satisfied by every module.
-/

namespace TauCeti.RingTheory.Gorenstein

public section

universe u v

variable (R : Type u) [Ring R]

/-- Bennis–Mahdou 2007, Def. 1.1(1): a strongly complete projective resolution
`⋯ → P -f→ P -f→ P → ⋯`. `P` is projective, the complex is exact at `P`
(`ker f = range f`; periodicity makes this the only exactness condition
needed), and `Hom(-,Q)` leaves it exact for every projective `Q`. -/
structure StronglyCompleteProjectiveResolution (R : Type u) [Ring R] where
  /-- The underlying projective module `P` in `⋯ → P → P → ⋯`. -/
  P : Type v
  /-- `P` is an additive group. -/
  [addGroup : AddCommGroup P]
  /-- `P` is an `R`-module. -/
  [moduleInst : Module R P]
  /-- `P` is projective. -/
  [projective : Module.Projective R P]
  /-- The differential `f : P →ₗ[R] P`. -/
  f : P →ₗ[R] P
  /-- The complex `⋯ → P -f→ P -f→ P → ⋯` is exact at `P` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  exact : Function.Exact f f
  /-- Completeness: `Hom(-,Q)` leaves `⋯ → P -f→ P -f→ P → ⋯` exact, for every
  projective `Q` — precomposing `Q`-valued homs by `f` is itself an exact pair.
  Without this the resolution is merely exact, not *complete*. -/
  homExact : ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.Projective R Q],
    Function.Exact (fun g : P →ₗ[R] Q => g.comp f) (fun g : P →ₗ[R] Q => g.comp f)

/-- Def. 1.1(2) (dual): a strongly complete injective resolution
`⋯ → I -f→ I -f→ I → ⋯`. `I` is injective, the complex is exact at `I`, and
`Hom(E,-)` leaves it exact for every injective `E`. -/
structure StronglyCompleteInjectiveResolution (R : Type u) [Ring R] where
  /-- The underlying injective module `I` in `⋯ → I → I → ⋯`. -/
  I : Type v
  /-- `I` is an additive group. -/
  [addGroup : AddCommGroup I]
  /-- `I` is an `R`-module. -/
  [moduleInst : Module R I]
  /-- `I` is injective. -/
  [injective : Module.Injective R I]
  /-- The differential `f : I →ₗ[R] I`. -/
  f : I →ₗ[R] I
  /-- The complex `⋯ → I -f→ I -f→ I → ⋯` is exact at `I` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  exact : Function.Exact f f
  /-- Completeness: `Hom(E,-)` leaves `⋯ → I -f→ I -f→ I → ⋯` exact, for every
  injective `E` — postcomposing `E`-sourced homs by `f` is itself an exact
  pair. Without this the resolution is merely exact, not *complete*. -/
  homExact : ∀ (E : Type v) [AddCommGroup E] [Module R E] [Module.Injective R E],
    Function.Exact (fun g : E →ₗ[R] I => f.comp g) (fun g : E →ₗ[R] I => f.comp g)

/-- Def. 1.1(3) (dual): a strongly complete flat resolution
`⋯ → F -f→ F -f→ F → ⋯`. `F` is flat, the complex is exact at `F`, and `I ⊗ -`
leaves it exact for every injective `I`. `Mathlib`'s `Module.Flat` is stated
over a `CommSemiring`, so this structure (unlike the projective and injective
cases) needs `CommRing R`. -/
structure StronglyCompleteFlatResolution (R : Type u) [CommRing R] where
  /-- The underlying flat module `F` in `⋯ → F → F → ⋯`. -/
  F : Type v
  /-- `F` is an additive group. -/
  [addGroup : AddCommGroup F]
  /-- `F` is an `R`-module. -/
  [moduleInst : Module R F]
  /-- `F` is flat. -/
  [flat : Module.Flat R F]
  /-- The differential `f : F →ₗ[R] F`. -/
  f : F →ₗ[R] F
  /-- The complex `⋯ → F -f→ F -f→ F → ⋯` is exact at `F` (`ker f = range f`;
  this also gives `f.comp f = 0`, via `Function.Exact.linearMap_comp_eq_zero`). -/
  exact : Function.Exact f f
  /-- Completeness: `I ⊗ -` leaves `⋯ → F -f→ F -f→ F → ⋯` exact, for every
  injective `I` — `id ⊗ f` on `I ⊗[R] F` is itself an exact pair. Without this
  the resolution is merely exact, not *complete*. -/
  tensorExact : ∀ (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I],
    Function.Exact (TensorProduct.map (LinearMap.id (R := R) (M := I)) f)
      (TensorProduct.map (LinearMap.id (R := R) (M := I)) f)

/-- Def. 1.1(1): `M` is strongly Gorenstein projective if it is (isomorphic
to) the image of the differential of a strongly complete projective
resolution. -/
def IsStronglyGorensteinProjective (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteProjectiveResolution.{u, v} R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

/-- Def. 1.1(2): `M` is strongly Gorenstein injective, dually. -/
def IsStronglyGorensteinInjective (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteInjectiveResolution.{u, v} R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

/-- Def. 1.1(3): `M` is strongly Gorenstein flat, dually. Needs `CommRing R`
for the same reason `StronglyCompleteFlatResolution` does. -/
def IsStronglyGorensteinFlat (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ S : StronglyCompleteFlatResolution.{u, v} R,
    letI := S.addGroup; letI := S.moduleInst
    Nonempty (LinearMap.range S.f ≃ₗ[R] M)

/-- Introduction rule for `IsStronglyGorensteinProjective`: a resolution together
with an isomorphism from its image. Consumers should build the predicate through
this rather than through the anonymous constructor, so the `∃`/`Nonempty` encoding
stays an implementation detail. -/
theorem IsStronglyGorensteinProjective.of_rangeEquiv (M : Type v) [AddCommGroup M] [Module R M]
    (S : StronglyCompleteProjectiveResolution.{u, v} R)
    (e : letI := S.addGroup; letI := S.moduleInst; LinearMap.range S.f ≃ₗ[R] M) :
    IsStronglyGorensteinProjective R M :=
  ⟨S, ⟨e⟩⟩

/-- Introduction rule for `IsStronglyGorensteinInjective`. -/
theorem IsStronglyGorensteinInjective.of_rangeEquiv (M : Type v) [AddCommGroup M] [Module R M]
    (S : StronglyCompleteInjectiveResolution.{u, v} R)
    (e : letI := S.addGroup; letI := S.moduleInst; LinearMap.range S.f ≃ₗ[R] M) :
    IsStronglyGorensteinInjective R M :=
  ⟨S, ⟨e⟩⟩

/-- Introduction rule for `IsStronglyGorensteinFlat`. -/
theorem IsStronglyGorensteinFlat.of_rangeEquiv (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (S : StronglyCompleteFlatResolution.{u, v} R)
    (e : letI := S.addGroup; letI := S.moduleInst; LinearMap.range S.f ≃ₗ[R] M) :
    IsStronglyGorensteinFlat R M :=
  ⟨S, ⟨e⟩⟩

/-! ## Contractible periodic complexes

Every strongly complete resolution needs both an exact complex and a functor
that leaves it exact. Both follow at once from a contraction, since a
contraction is carried by any additive functor: `exact_of_homotopy` is stated
for plain functions so that the induced maps on a `Hom` complex use the same
lemma as the differential itself.
-/

/-- A contraction makes a periodic complex exact: if `F ∘ F = 0` and
`F ∘ S + S ∘ F = id` pointwise, then `⋯ → N -F→ N -F→ N → ⋯` is exact. -/
theorem exact_of_homotopy {N : Type*} [AddCommGroup N] {F S : N → N}
    (hFF : ∀ x, F (F x) = 0) (hS : S 0 = 0) (hFS : ∀ x, F (S x) + S (F x) = x) :
    Function.Exact F F := by
  intro y
  constructor
  · intro hy
    refine ⟨S y, ?_⟩
    have h := hFS y
    rw [hy, hS, add_zero] at h
    exact h
  · rintro ⟨x, rfl⟩
    exact hFF x

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The differential `(x, y) ↦ (y, 0)` of the contractible periodic complex on
`M × M`. Its image is the first summand, a copy of `M`. -/
def prodShift : M × M →ₗ[R] M × M :=
  (LinearMap.inl R M M).comp (LinearMap.snd R M M)

/-- The contraction `(x, y) ↦ (0, x)` of `prodShift`. -/
def prodContraction : M × M →ₗ[R] M × M :=
  (LinearMap.inr R M M).comp (LinearMap.fst R M M)

/-- `prodShift` unfolded, so that its body need not be exposed. -/
theorem prodShift_eq_comp :
    prodShift R M = (LinearMap.inl R M M).comp (LinearMap.snd R M M) := (rfl)

@[simp] theorem prodShift_apply (p : M × M) : prodShift R M p = (p.2, 0) := (rfl)

@[simp] theorem prodContraction_apply (p : M × M) : prodContraction R M p = (0, p.1) := (rfl)

theorem prodShift_prodShift (p : M × M) : prodShift R M (prodShift R M p) = 0 := (rfl)

theorem prodShift_prodContraction_add (p : M × M) :
    prodShift R M (prodContraction R M p) + prodContraction R M (prodShift R M p) = p := by
  obtain ⟨x, y⟩ := p
  exact Prod.ext (add_zero x) (zero_add y)

theorem prodContraction_prodShift_add (p : M × M) :
    prodContraction R M (prodShift R M p) + prodShift R M (prodContraction R M p) = p := by
  rw [add_comm]
  exact prodShift_prodContraction_add R M p

theorem range_prodShift :
    LinearMap.range (prodShift R M) = LinearMap.range (LinearMap.inl R M M) := by
  rw [prodShift_eq_comp]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top_of_surjective _ Prod.snd_surjective)

/-- The image of `prodShift` is a copy of `M`. -/
noncomputable def rangeProdShiftEquiv : LinearMap.range (prodShift R M) ≃ₗ[R] M :=
  (LinearEquiv.ofEq _ _ (range_prodShift R M)).trans
    (LinearEquiv.ofInjective (LinearMap.inl R M M) LinearMap.inl_injective).symm

/-- Every projective module is strongly Gorenstein projective: the contractible
complex `⋯ → M × M -f→ M × M → ⋯` with `f (x, y) = (y, 0)` is a strongly
complete projective resolution whose image is `M`. The `Hom(-,Q)` condition
holds for every `Q`, projective or not, because a contraction survives any
additive functor. -/
theorem isStronglyGorensteinProjective_of_projective [Module.Projective R M] :
    IsStronglyGorensteinProjective R M := by
  refine IsStronglyGorensteinProjective.of_rangeEquiv R M
    { P := M × M, f := prodShift R M, exact := ?_, homExact := ?_ }
    (rangeProdShiftEquiv R M)
  · exact exact_of_homotopy (S := prodContraction R M) (prodShift_prodShift R M)
      (map_zero _) (prodShift_prodContraction_add R M)
  · intro Q _ _ _
    refine exact_of_homotopy (S := fun g : (M × M) →ₗ[R] Q => g.comp (prodContraction R M))
      (fun g => ?_) (LinearMap.zero_comp _) (fun g => ?_)
    · refine LinearMap.ext fun p => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      rw [prodShift_prodShift, map_zero]
    · refine LinearMap.ext fun p => ?_
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add, prodContraction_prodShift_add]

/-- A strongly Gorenstein projective module embeds in a projective module,
being the image of a differential on one. This is what makes the predicate
restrictive: over `ℤ`, where projective modules are torsion free, `ZMod 2`
admits no such embedding. -/
theorem IsStronglyGorensteinProjective.exists_injective
    (h : IsStronglyGorensteinProjective R M) :
    ∃ S : StronglyCompleteProjectiveResolution.{u, v} R,
      letI := S.addGroup; letI := S.moduleInst
      ∃ i : M →ₗ[R] S.P, Function.Injective i := by
  obtain ⟨S, ⟨e⟩⟩ := h
  let _ := S.addGroup
  let _ := S.moduleInst
  exact ⟨S, (LinearMap.range S.f).subtype.comp e.symm.toLinearMap,
    (Submodule.injective_subtype _).comp e.symm.injective⟩

/-- A strongly Gorenstein injective module is a quotient of an injective module.
Dually to the projective case this is restrictive: over `ℤ` a quotient of an
injective module is divisible, and `ZMod 2` is not. -/
theorem IsStronglyGorensteinInjective.exists_surjective
    (h : IsStronglyGorensteinInjective R M) :
    ∃ S : StronglyCompleteInjectiveResolution.{u, v} R,
      letI := S.addGroup; letI := S.moduleInst
      ∃ p : S.I →ₗ[R] M, Function.Surjective p := by
  obtain ⟨S, ⟨e⟩⟩ := h
  let _ := S.addGroup
  let _ := S.moduleInst
  exact ⟨S, e.toLinearMap.comp S.f.rangeRestrict,
    e.surjective.comp S.f.surjective_rangeRestrict⟩

/-- A strongly Gorenstein flat module embeds in a flat module. Over `ℤ`, where
flat means torsion free, this again fails for `ZMod 2`. -/
theorem IsStronglyGorensteinFlat.exists_injective (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (h : IsStronglyGorensteinFlat R M) :
    ∃ S : StronglyCompleteFlatResolution.{u, v} R,
      letI := S.addGroup; letI := S.moduleInst
      ∃ i : M →ₗ[R] S.F, Function.Injective i := by
  obtain ⟨S, ⟨e⟩⟩ := h
  let _ := S.addGroup
  let _ := S.moduleInst
  exact ⟨S, (LinearMap.range S.f).subtype.comp e.symm.toLinearMap,
    (Submodule.injective_subtype _).comp e.symm.injective⟩

end

end TauCeti.RingTheory.Gorenstein
