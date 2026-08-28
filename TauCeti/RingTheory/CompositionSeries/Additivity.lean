/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
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
`M`.  Neither half is transported along an isomorphism of the ambient module, so
`TauCeti.mapCompositionSeries` of `TauCeti/RingTheory/CompositionSeries/Basic.lean` does not apply:
the lower half is carried along the *injective* map `p.subtype` and the upper half along the
*surjective* map `p.mkQ`.  Those two transports are built here in the generality that makes them
symmetric — an arbitrary injective, respectively surjective, linear map — and each rests on the
identification of the subquotients it induces (`TauCeti.factorEquivMapOfInjective`,
`TauCeti.factorEquivComapOfSurjective`), which is also what turns coverings into coverings.  The
resulting series are glued with `RelSeries.smash`, whose index lemmas split the count.

## Main definitions

* `TauCeti.mapCompositionSeriesOfInjective`: the image of a composition series under an injective
  linear map.
* `TauCeti.comapCompositionSeriesOfSurjective`: the preimage of a composition series under a
  surjective linear map.

## Main results

* `TauCeti.factorEquivMapOfInjective` and `TauCeti.factorEquivComapOfSurjective`: an injective map
  identifies the subquotient `B ⧸ A` with the subquotient of its images, and a surjective map
  identifies the subquotient of the preimages with `B ⧸ A`.
* `TauCeti.compositionMultiplicity_smash`: the multiplicities of two composition series glued end
  to end add.
* `TauCeti.jordanHolderMultiplicity_eq_submodule_add_quotient`: **additivity**,
  `[M : S] = [p : S] + [M ⧸ p : S]`.
* `TauCeti.jordanHolderMultiplicity_eq_add_of_exact`: the same statement for a short exact sequence
  `0 → A → M → B → 0`.
* `TauCeti.jordanHolderMultiplicity_prod`: `[M × N : S] = [M : S] + [N : S]`.

## Implementation notes

`TauCeti.mapCompositionSeriesOfInjective` at a linear equivalence is definitionally
`TauCeti.mapCompositionSeries`; the latter stays in
`TauCeti/RingTheory/CompositionSeries/Basic.lean` because the transport lemmas of
`TauCeti/RingTheory/CompositionSeries/Multiplicity.lean` are stated against it, and replacing it by
the injective form is a refactor of its own.

Coverings are transported through `covBy_iff_quot_is_simple` rather than through an order
isomorphism: the two factor equivalences are needed anyway, and reading a covering as simplicity of
its subquotient turns both transports into one line.  The alternative, `Set.OrdConnected` ranges,
would need a separate argument for each of the two maps.

## References

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

/-! ### Subquotients along an injective linear map -/

section Injective

/-- An injective linear map carries the trace of `A` in `B` onto the trace of `A.map f` in
`B.map f`, so it descends to the subquotients. -/
theorem map_equivMapOfInjective_comap_subtype (f : M →ₗ[R] N) (hf : Function.Injective f)
    {A B : Submodule R M} (hAB : A ≤ B) :
    Submodule.map ((Submodule.equivMapOfInjective f hf B : ↥B ≃ₗ[R] ↥(B.map f)) :
        ↥B →ₗ[R] ↥(B.map f)) (Submodule.comap B.subtype A)
      = Submodule.comap (B.map f).subtype (A.map f) := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : M), hx, (Submodule.coe_equivMapOfInjective_apply f hf B x).symm⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨⟨a, hAB ha⟩, ha, Subtype.ext
      ((Submodule.coe_equivMapOfInjective_apply f hf B ⟨a, hAB ha⟩).trans hay)⟩

/-- **An injective linear map identifies subquotients.**  For `A ≤ B` the subquotient of the images
`A.map f ≤ B.map f` is the subquotient `B ⧸ A` itself. -/
noncomputable def factorEquivMapOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    {A B : Submodule R M} (hAB : A ≤ B) :
    (↥(B.map f) ⧸ Submodule.comap (B.map f).subtype (A.map f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf B)
    (map_equivMapOfInjective_comap_subtype f hf hAB)).symm

/-- An injective linear map preserves coverings of submodules: the subquotient at the image is the
subquotient itself, hence again simple. -/
theorem covBy_map_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) {A B : Submodule R M}
    (h : A ⋖ B) : A.map f ⋖ B.map f := by
  have hsimple : IsSimpleModule R (↥B ⧸ Submodule.comap B.subtype A) :=
    (covBy_iff_quot_is_simple h.le).mp h
  exact (covBy_iff_quot_is_simple (Submodule.map_mono h.le)).mpr
    (IsSimpleModule.congr (factorEquivMapOfInjective f hf h.le))

end Injective

/-! ### Subquotients along a surjective linear map -/

section Surjective

variable (f : M →ₗ[R] N)

/-- A linear map restricted to the preimage of a submodule. -/
def restrictComap (B : Submodule R N) : ↥(B.comap f) →ₗ[R] ↥B :=
  f.restrict fun _ hx => hx

@[simp]
theorem coe_restrictComap_apply (B : Submodule R N) (x : ↥(B.comap f)) :
    (restrictComap f B x : N) = f x :=
  (rfl)

theorem restrictComap_surjective (hf : Function.Surjective f) (B : Submodule R N) :
    Function.Surjective (restrictComap f B) := fun y => by
  obtain ⟨x, hx⟩ := hf (y : N)
  refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩ <;> simp [hx]

/-- The kernel of `X ↦ f X mod A`, on the preimage of `B`, is the trace of the preimage of `A`. -/
theorem ker_mkQ_comp_restrictComap (A B : Submodule R N) :
    LinearMap.ker ((Submodule.comap B.subtype A).mkQ ∘ₗ restrictComap f B)
      = Submodule.comap (B.comap f).subtype (A.comap f) := by
  ext x
  simp

/-- **A surjective linear map identifies subquotients.**  For `A ≤ B` the subquotient of the
preimages `A.comap f ≤ B.comap f` is the subquotient `B ⧸ A` itself. -/
noncomputable def factorEquivComapOfSurjective (hf : Function.Surjective f) (A B : Submodule R N) :
    (↥(B.comap f) ⧸ Submodule.comap (B.comap f).subtype (A.comap f)) ≃ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype A) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_restrictComap f A B).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp (restrictComap_surjective f hf B)))

/-- A surjective linear map preserves coverings of submodules: the subquotient at the preimage is
the subquotient itself, hence again simple. -/
theorem covBy_comap_of_surjective (hf : Function.Surjective f) {A B : Submodule R N} (h : A ⋖ B) :
    A.comap f ⋖ B.comap f := by
  have hsimple : IsSimpleModule R (↥B ⧸ Submodule.comap B.subtype A) :=
    (covBy_iff_quot_is_simple h.le).mp h
  exact (covBy_iff_quot_is_simple (Submodule.comap_mono h.le)).mpr
    (IsSimpleModule.congr (factorEquivComapOfSurjective f hf A B))

end Surjective

/-! ### Transporting a composition series along an injective or a surjective map -/

/-- The image of a composition series under an injective linear map.  As in
`TauCeti.mapCompositionSeries`, the body is `@[expose]`d so that
`mapCompositionSeriesOfInjective f hf s i` is definitionally `Submodule.map f (s i)`, which is what
the factor lemmas below rest on. -/
@[expose] def mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) : CompositionSeries (Submodule R N) :=
  s.map ⟨fun A => A.map f, fun h => covBy_map_of_injective f hf h⟩

@[simp]
theorem mapCompositionSeriesOfInjective_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) (i : Fin (s.length + 1)) :
    mapCompositionSeriesOfInjective f hf s i = (s i).map f :=
  (rfl)

@[simp]
theorem mapCompositionSeriesOfInjective_length (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).length = s.length :=
  (rfl)

@[simp]
theorem head_mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).head = s.head.map f :=
  (rfl)

@[simp]
theorem last_mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).last = s.last.map f :=
  (rfl)

/-- The preimage of a composition series under a surjective linear map.  The body is `@[expose]`d
for the same reason as `TauCeti.mapCompositionSeriesOfInjective`. -/
@[expose] def comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) : CompositionSeries (Submodule R M) :=
  s.map ⟨fun A => A.comap f, fun h => covBy_comap_of_surjective f hf h⟩

@[simp]
theorem comapCompositionSeriesOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) (i : Fin (s.length + 1)) :
    comapCompositionSeriesOfSurjective f hf s i = (s i).comap f :=
  (rfl)

@[simp]
theorem comapCompositionSeriesOfSurjective_length (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).length = s.length :=
  (rfl)

@[simp]
theorem head_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).head = s.head.comap f :=
  (rfl)

@[simp]
theorem last_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).last = s.last.comap f :=
  (rfl)

/-! ### The factors of the transported series -/

variable {S : Type v''} [AddCommGroup S] [Module R S]

/-- Two composition series with the same two submodules at an index have the same factor there.
The equalities are enough: the subquotient is built from the two submodules alone. -/
theorem isCompositionFactorAt_congr_of_eq {s t : CompositionSeries (Submodule R M)}
    {i : Fin s.length} {j : Fin t.length} (hsucc : s i.succ = t j.succ)
    (hcast : s i.castSucc = t j.castSucc) :
    IsCompositionFactorAt s i S ↔ IsCompositionFactorAt t j S := by
  rw [isCompositionFactorAt_iff, isCompositionFactorAt_iff, hcast, hsucc]

@[simp]
theorem isCompositionFactorAt_mapCompositionSeriesOfInjective_iff (f : M →ₗ[R] N)
    (hf : Function.Injective f) (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsCompositionFactorAt (mapCompositionSeriesOfInjective f hf s) i S ↔
      IsCompositionFactorAt s i S :=
  isCompositionFactorAt_iff.trans
    (Iff.trans
      ⟨fun ⟨g⟩ => ⟨(factorEquivMapOfInjective f hf (s.step i).le).symm.trans g⟩,
        fun ⟨g⟩ => ⟨(factorEquivMapOfInjective f hf (s.step i).le).trans g⟩⟩
      isCompositionFactorAt_iff.symm)

@[simp]
theorem isCompositionFactorAt_comapCompositionSeriesOfSurjective_iff (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (s : CompositionSeries (Submodule R N)) (i : Fin s.length) :
    IsCompositionFactorAt (comapCompositionSeriesOfSurjective f hf s) i S ↔
      IsCompositionFactorAt s i S :=
  isCompositionFactorAt_iff.trans
    (Iff.trans
      ⟨fun ⟨g⟩ => ⟨(factorEquivComapOfSurjective f hf (s i.castSucc) (s i.succ)).symm.trans g⟩,
        fun ⟨g⟩ => ⟨(factorEquivComapOfSurjective f hf (s i.castSucc) (s i.succ)).trans g⟩⟩
      isCompositionFactorAt_iff.symm)

/-- **An injective map preserves multiplicities**: the image of a composition series counts every
module the same number of times as the series itself. -/
@[simp]
theorem compositionMultiplicity_mapCompositionSeriesOfInjective (f : M →ₗ[R] N)
    (hf : Function.Injective f) (s : CompositionSeries (Submodule R M)) :
    compositionMultiplicity (mapCompositionSeriesOfInjective f hf s) S =
      compositionMultiplicity s S := by
  rw [compositionMultiplicity_def, compositionMultiplicity_def]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    isCompositionFactorAt_mapCompositionSeriesOfInjective_iff f hf s i)

/-- **A surjective map preserves multiplicities**: the preimage of a composition series counts
every module the same number of times as the series itself. -/
@[simp]
theorem compositionMultiplicity_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (s : CompositionSeries (Submodule R N)) :
    compositionMultiplicity (comapCompositionSeriesOfSurjective f hf s) S =
      compositionMultiplicity s S := by
  rw [compositionMultiplicity_def, compositionMultiplicity_def]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    isCompositionFactorAt_comapCompositionSeriesOfSurjective_iff f hf s i)

/-! ### Gluing two composition series -/

section Smash

variable (p q : CompositionSeries (Submodule R M)) (h : p.last = q.head)

theorem isCompositionFactorAt_smash_castAdd (i : Fin p.length) :
    IsCompositionFactorAt (p.smash q h) (i.castAdd q.length) S ↔ IsCompositionFactorAt p i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_castAdd h i)
    (RelSeries.smash_castAdd h i)

theorem isCompositionFactorAt_smash_natAdd (i : Fin q.length) :
    IsCompositionFactorAt (p.smash q h) (i.natAdd p.length) S ↔ IsCompositionFactorAt q i S :=
  isCompositionFactorAt_congr_of_eq (RelSeries.smash_succ_natAdd h i)
    (RelSeries.smash_natAdd h i)

/-- **Gluing adds multiplicities.**  Two composition series joined end to end count every module as
often as the two of them together. -/
theorem compositionMultiplicity_smash :
    compositionMultiplicity (p.smash q h) S =
      compositionMultiplicity p S + compositionMultiplicity q S := by
  classical
  have key : ∀ t : CompositionSeries (Submodule R M),
      compositionMultiplicity t S =
        ∑ i : Fin t.length, if IsCompositionFactorAt t i S then 1 else 0 := fun t => by
    rw [compositionMultiplicity_def, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_filter]
  have hsplit :
      (∑ i : Fin (p.length + q.length),
          if IsCompositionFactorAt (p.smash q h) i S then 1 else 0)
        = (∑ i : Fin p.length,
            if IsCompositionFactorAt (p.smash q h) (i.castAdd q.length) S then 1 else 0)
          + ∑ i : Fin q.length,
            if IsCompositionFactorAt (p.smash q h) (i.natAdd p.length) S then 1 else 0 :=
    Fin.sum_univ_add _
  rw [key, key, key]
  refine hsplit.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_))
  · exact if_congr (isCompositionFactorAt_smash_castAdd p q h i) rfl rfl
  · exact if_congr (isCompositionFactorAt_smash_natAdd p q h i) rfl rfl

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
  set t' := mapCompositionSeriesOfInjective p.subtype p.injective_subtype t with ht'
  set u' := comapCompositionSeriesOfSurjective p.mkQ p.mkQ_surjective u with hu'
  have hconnect : t'.last = u'.head := by
    rw [ht', hu', last_mapCompositionSeriesOfInjective, head_comapCompositionSeriesOfSurjective,
      httop, hubot, Submodule.map_top, Submodule.range_subtype, Submodule.comap_bot,
      Submodule.ker_mkQ]
  have hbot : (t'.smash u' hconnect).head = ⊥ := by
    rw [RelSeries.head_smash, ht', head_mapCompositionSeriesOfInjective, htbot, Submodule.map_bot]
  have htop : (t'.smash u' hconnect).last = ⊤ := by
    rw [RelSeries.last_smash, hu', last_comapCompositionSeriesOfSurjective, hutop,
      Submodule.comap_top]
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity _ hbot htop S,
    compositionMultiplicity_smash, ht', hu',
    compositionMultiplicity_mapCompositionSeriesOfInjective,
    compositionMultiplicity_comapCompositionSeriesOfSurjective,
    compositionMultiplicity_eq_jordanHolderMultiplicity t htbot httop S,
    compositionMultiplicity_eq_jordanHolderMultiplicity u hubot hutop S]

/-- A submodule contributes at most the whole module's multiplicity. -/
theorem jordanHolderMultiplicity_submodule_le [IsNoetherian R M] [IsArtinian R M]
    (p : Submodule R M) :
    jordanHolderMultiplicity R p S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_submodule_add_quotient p]
  exact Nat.le_add_right _ _

/-- A quotient contributes at most the whole module's multiplicity. -/
theorem jordanHolderMultiplicity_quotient_le [IsNoetherian R M] [IsArtinian R M]
    (p : Submodule R M) :
    jordanHolderMultiplicity R (M ⧸ p) S ≤ jordanHolderMultiplicity R M S := by
  rw [jordanHolderMultiplicity_eq_submodule_add_quotient p]
  exact Nat.le_add_left _ _

/-- **Additivity in a short exact sequence** `0 → A → M → B → 0`: the multiplicity of `S` in the
middle term is the sum of its multiplicities in the two ends. -/
theorem jordanHolderMultiplicity_eq_add_of_exact [IsNoetherian R M] [IsArtinian R M]
    {A : Type w} [AddCommGroup A] [Module R A] [IsNoetherian R A] [IsArtinian R A]
    {B : Type w'} [AddCommGroup B] [Module R B] [IsNoetherian R B] [IsArtinian R B]
    (f : A →ₗ[R] M) (g : M →ₗ[R] B) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    jordanHolderMultiplicity R M S =
      jordanHolderMultiplicity R A S + jordanHolderMultiplicity R B S := by
  rw [jordanHolderMultiplicity_eq_submodule_add_quotient (LinearMap.range f),
    jordanHolderMultiplicity_eq_of_linearEquiv (LinearEquiv.ofInjective f hf) S,
    ← jordanHolderMultiplicity_eq_of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ hfg).trans (g.quotKerEquivOfSurjective hg)) S]

/-- **Additivity on a binary product**: `[M × N : S] = [M : S] + [N : S]`. -/
theorem jordanHolderMultiplicity_prod [IsNoetherian R M] [IsArtinian R M] [IsNoetherian R N]
    [IsArtinian R N] :
    jordanHolderMultiplicity R (M × N) S =
      jordanHolderMultiplicity R M S + jordanHolderMultiplicity R N S :=
  jordanHolderMultiplicity_eq_add_of_exact (LinearMap.inl R M N) (LinearMap.snd R M N)
    (LinearMap.inl_injective) (LinearMap.snd_surjective) (LinearMap.range_inl R M N)

end TauCeti
