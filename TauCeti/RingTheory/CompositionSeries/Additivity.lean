/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.RingTheory.CompositionSeries.Multiplicity

/-!
# Additivity of the Jordan-Hölder multiplicities

The Jordan-Hölder multiplicity `[M : S]` counts the factors isomorphic to `S` in a composition
series of `M`.  This file proves that it is **additive in a short exact sequence**: for a submodule
`p` of a module `M` of finite length,

`[M : S] = [p : S] + [M ⧸ p : S]`.

Both the composition factors of `p` and those of `M ⧸ p` are composition factors of `M`, and no
others are, so a single count splits in two.

The proof glues a composition series of `p` and a composition series of `M ⧸ p` into one series of
`M`: the lower half is carried along the *injective* map `p.subtype` by
`TauCeti.mapCompositionSeriesOfInjective` and the upper half along the *surjective* map `p.mkQ` by
`TauCeti.comapCompositionSeriesOfSurjective`, both of
`TauCeti/RingTheory/CompositionSeries/Basic.lean`; that these transports preserve every
multiplicity is `TauCeti.compositionMultiplicity_mapCompositionSeriesOfInjective` and
`TauCeti.compositionMultiplicity_comapCompositionSeriesOfSurjective`, of
`TauCeti/RingTheory/CompositionSeries/Multiplicity.lean`.  The two resulting series meet at `p` and
are glued with `RelSeries.smash`, whose `castAdd`/`natAdd` index lemmas split the count of factors
isomorphic to `S` into the two halves.

## Main results

* `TauCeti.compositionMultiplicity_smash`: the multiplicities of two composition series glued end
  to end add.
* `TauCeti.jordanHolderMultiplicity_eq_submodule_add_quotient`: **additivity**,
  `[M : S] = [p : S] + [M ⧸ p : S]`.
* `TauCeti.jordanHolderMultiplicity_eq_add_of_exact`: the same statement for a short exact sequence
  `0 → A → M → B → 0`.
* `TauCeti.jordanHolderMultiplicity_le_of_injective` and
  `TauCeti.jordanHolderMultiplicity_le_of_surjective`: a submodule and a quotient — more generally
  the source of an injective map into `M` and the target of a surjective map out of `M` — each
  contribute at most `M`'s multiplicity.
* `TauCeti.jordanHolderMultiplicity_prod`: `[M × N : S] = [M : S] + [N : S]`.

## References

This file refines Mathlib's `Module.length_eq_add_of_exact` (`Mathlib/RingTheory/Length.lean`, by
Andrew Yang) from counting the factors of a composition series to counting those isomorphic to a
fixed simple module `S`, and follows its proof plan: the same two transports along an injective and
a surjective map, the same `RelSeries.smash` gluing, and the same `map_bot`/`comap_top` endpoint
bookkeeping.  The monotonicity and product corollaries below are likewise the multiplicity
analogues of `Module.length_le_of_injective`, `Module.length_le_of_surjective` and
`Module.length_prod`.  What is new is that the transports are shown to preserve each factor's
isomorphism class and not merely the number of factors: the identification of the subquotients is
`TauCeti.mapSubquotientEquivOfInjective` and `TauCeti.comapSubquotientEquivOfSurjective` of
`TauCeti/Algebra/Module/Submodule/Quotient.lean`, and the resulting factor-by-factor comparison is
`TauCeti.isCompositionFactorAt_mapCompositionSeriesOfInjective_iff` and its surjective counterpart
in `TauCeti/RingTheory/CompositionSeries/Multiplicity.lean`;
`TauCeti/RingTheory/CompositionSeries/Basic.lean` supplies the transports themselves.

The additivity of `[Pᵢ : Sⱼ]` is what makes the Cartan matrix of a finite-dimensional algebra
computable, in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` ("The Cartan matrix of an
algebra"); `TauCeti/RingTheory/CompositionSeries/Multiplicity.lean` supplies the multiplicity
itself.

* Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  §I.4.
-/

public section

namespace TauCeti

universe u v v' v'' w w'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v'} [AddCommGroup N] [Module R N]
variable {S : Type v''} [AddCommGroup S] [Module R S]

/-! ### Gluing two composition series -/

section Smash

variable (p q : CompositionSeries (Submodule R M)) (h : p.last = q.head)

/-- The factors of the first half of a glued series are the factors of the first series. -/
@[simp]
theorem isCompositionFactorAt_smash_castAdd_iff (i : Fin p.length) :
    IsCompositionFactorAt (p.smash q h) (i.castAdd q.length) S ↔ IsCompositionFactorAt p i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_castAdd h i)
    (RelSeries.smash_castAdd h i)

/-- The factors of the second half of a glued series are the factors of the second series. -/
@[simp]
theorem isCompositionFactorAt_smash_natAdd_iff (i : Fin q.length) :
    IsCompositionFactorAt (p.smash q h) (i.natAdd p.length) S ↔ IsCompositionFactorAt q i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_natAdd h i)
    (RelSeries.smash_natAdd h i)

/-- **Gluing adds multiplicities.**  Two composition series joined end to end count every module as
often as the two of them together. -/
@[simp]
theorem compositionMultiplicity_smash :
    compositionMultiplicity (p.smash q h) S =
      compositionMultiplicity p S + compositionMultiplicity q S := by
  classical
  rw [compositionMultiplicity_eq_sum_ite, compositionMultiplicity_eq_sum_ite,
    compositionMultiplicity_eq_sum_ite]
  exact (Fin.sum_univ_add _).trans (by simp)

end Smash

/-! ### Additivity of the Jordan-Hölder multiplicity -/

/-- **The Jordan-Hölder multiplicity is additive.**  For a submodule `p` of a module of finite
length, `[M : S] = [p : S] + [M ⧸ p : S]`: a composition series of `p`, pushed into `M` along
`p.subtype`, and one of `M ⧸ p`, pulled back along `p.mkQ`, meet at `p` and glue to a composition
series of `M`. -/
theorem jordanHolderMultiplicity_eq_submodule_add_quotient [IsNoetherian R M] [IsArtinian R M]
    (p : Submodule R M) :
    jordanHolderMultiplicity R M S =
      jordanHolderMultiplicity R p S + jordanHolderMultiplicity R (M ⧸ p) S := by
  obtain ⟨t, htbot, httop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R p
  obtain ⟨u, hubot, hutop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R (M ⧸ p)
  have hconnect :
      (mapCompositionSeriesOfInjective p.subtype p.injective_subtype t).last =
        (comapCompositionSeriesOfSurjective p.mkQ p.mkQ_surjective u).head := by
    simp [httop, hubot]
  refine (compositionMultiplicity_eq_jordanHolderMultiplicity
    ((mapCompositionSeriesOfInjective p.subtype p.injective_subtype t).smash
      (comapCompositionSeriesOfSurjective p.mkQ p.mkQ_surjective u) hconnect)
    (by simp [RelSeries.head_smash, htbot]) (by simp [RelSeries.last_smash, hutop])
    S).symm.trans ?_
  rw [compositionMultiplicity_smash, compositionMultiplicity_mapCompositionSeriesOfInjective,
    compositionMultiplicity_comapCompositionSeriesOfSurjective,
    compositionMultiplicity_eq_jordanHolderMultiplicity t htbot httop S,
    compositionMultiplicity_eq_jordanHolderMultiplicity u hubot hutop S]

/-- **Additivity in a short exact sequence** `0 → A → M → B → 0`: the multiplicity of `S` in the
middle term is the sum of its multiplicities in the two ends.

Mathematically the finiteness of `A` and of `B` follows from that of `M`, through `A ≃ₗ[R] range f`
and `M ⧸ ker g ≃ₗ[R] B`.  The assumptions are nevertheless binders here rather than facts derived
in the proof, because `jordanHolderMultiplicity R A S` and `jordanHolderMultiplicity R B S` carry
them in their own signatures: the conclusion does not elaborate without them, so a caller holds
them already in order to state it. -/
theorem jordanHolderMultiplicity_eq_add_of_exact [IsNoetherian R M] [IsArtinian R M]
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    jordanHolderMultiplicity R M S =
      jordanHolderMultiplicity R A S + jordanHolderMultiplicity R B S := by
  rw [jordanHolderMultiplicity_eq_submodule_add_quotient (LinearMap.range f),
    jordanHolderMultiplicity_eq_of_linearEquiv (LinearEquiv.ofInjective f hf) S,
    ← jordanHolderMultiplicity_eq_of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hfg).symm).trans
        (g.quotKerEquivOfSurjective hg)) S]

/-- A module that embeds in `M` contributes at most `M`'s multiplicity.  As for
`TauCeti.jordanHolderMultiplicity_eq_add_of_exact`, the finiteness of `A` follows from that of `M`
and is a binder only because `jordanHolderMultiplicity R A S` — which already occurs in the
statement a caller is trying to prove — does not elaborate without it. -/
theorem jordanHolderMultiplicity_le_of_injective [IsNoetherian R M] [IsArtinian R M]
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    (f : A →ₗ[R] M) (hf : Function.Injective f) :
    jordanHolderMultiplicity R A S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact Nat.le_add_right _ _

/-- A quotient of `M` contributes at most `M`'s multiplicity.  As for
`TauCeti.jordanHolderMultiplicity_eq_add_of_exact`, the finiteness of `B` follows from that of `M`
and is a binder only because `jordanHolderMultiplicity R B S` — which already occurs in the
statement a caller is trying to prove — does not elaborate without it. -/
theorem jordanHolderMultiplicity_le_of_surjective [IsNoetherian R M] [IsArtinian R M]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (g : M →ₗ[R] B) (hg : Function.Surjective g) :
    jordanHolderMultiplicity R B S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
  exact Nat.le_add_left _ _

/-- **Additivity on a binary product**: `[M × N : S] = [M : S] + [N : S]`. -/
@[simp]
theorem jordanHolderMultiplicity_prod [IsNoetherian R M] [IsArtinian R M] [IsNoetherian R N]
    [IsArtinian R N] :
    jordanHolderMultiplicity R (M × N) S =
      jordanHolderMultiplicity R M S + jordanHolderMultiplicity R N S :=
  jordanHolderMultiplicity_eq_add_of_exact (LinearMap.inl R M N) (LinearMap.snd R M N)
    (LinearMap.inl_injective) (LinearMap.snd_surjective) Function.Exact.inl_snd

end TauCeti
