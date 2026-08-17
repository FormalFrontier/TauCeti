/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Jordan-Hölder multiplicities of a simple module

A composition series of a module `M` cuts `M` into simple subquotients, its *factors*, and the
Jordan-Hölder theorem says that two composition series with the same endpoints have the same
factors up to a permutation.  Counting how often a fixed simple module `S` occurs among them is
therefore an invariant of `M` alone: the **multiplicity** `[M : S]` of `S` in `M`.  This file
builds that count.

Mathlib has everything the construction rests on and nothing built on it: the Jordan-Hölder
theorem `CompositionSeries.jordan_holder` in the abstract lattice form, the recognition
`isFiniteLength_iff_exists_compositionSeries` of the modules that admit a composition series from
`⊥` to `⊤`, the identification `JordanHolderLattice.Iso.linearEquiv` of the abstract interval
isomorphism with a linear equivalence of subquotients, and `Module.length`, which records only the
*number* of factors.  The multiplicity of an individual simple module is not there.

The count is taken with `Nat.card`, over the subtype of indices whose factor is a copy of `S`, so
no decidability of "is a copy of `S`" is needed.  The factor at an index `i` is spelled out as the
subquotient `↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)`, in the exact form
that `JordanHolderLattice.Iso.linearEquiv` produces, rather than being wrapped in a definition of
its own; that keeps the interface between this file and Mathlib's Jordan-Hölder machinery a
definitional identity.

## Main definitions

* `TauCeti.IsCompositionFactorAt`: the factor of a composition series at an index is a copy of a
  given module.
* `TauCeti.compositionMultiplicity`: the number of indices of a composition series whose factor is
  a copy of a given module.
* `TauCeti.jordanHolderMultiplicity`: the multiplicity `[M : S]`, the same count for a composition
  series of `M` running from `⊥` to `⊤`.
* `TauCeti.mapCompositionSeries`: the image of a composition series under a linear equivalence of
  the ambient module, with `TauCeti.factorEquivMapCompositionSeries` identifying the factors of
  the two.

## Main results

* `TauCeti.compositionMultiplicity_eq_of_head_eq_of_last_eq`: **the multiplicity is a
  Jordan-Hölder invariant** — two composition series with the same endpoints count every module
  the same number of times.  This is what makes `TauCeti.jordanHolderMultiplicity` well defined,
  and `TauCeti.compositionMultiplicity_eq_jordanHolderMultiplicity` says that *every* composition
  series from `⊥` to `⊤` computes it.
* `TauCeti.IsCompositionFactorAt.isSimpleModule`: the factors are simple, so the multiplicity of a
  module that is not simple vanishes
  (`TauCeti.jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule`).
* `TauCeti.jordanHolderMultiplicity_of_linearEquiv`: **the multiplicity is an invariant of the
  isomorphism class of the ambient module**, which is what makes `[Pᵢ : Sⱼ]` well posed for a
  projective cover, an object defined only up to isomorphism.
* `TauCeti.jordanHolderMultiplicity_of_isSimpleModule` and
  `TauCeti.jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule`: a simple
  module contains itself once and nothing else, the anti-vacuity check on the count.
* `TauCeti.jordanHolderMultiplicity_congr`: the multiplicity depends on `S` only through its
  isomorphism class.

## References

The Jordan-Hölder multiplicities `[Pᵢ : Sⱼ]` are what the Cartan matrix of a finite-dimensional
algebra is defined by, in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` ("The Cartan matrix of an
algebra", *"defined primarily by the Jordan-Hölder multiplicities `Cᵢⱼ = [Pᵢ : Sⱼ]` of `Sⱼ` in the
projective cover `Pᵢ`, well-defined by Jordan-Hölder"*); this file supplies that multiplicity and
its well-definedness.

* Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
  §I.4 and §III.3.
-/

public section

open JordanHolderLattice

namespace TauCeti

universe u v v' w w'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-! ### The factors of a composition series -/

/-- The factor of the composition series `s` at the index `i` is a copy of `S`: the subquotient
`s i.succ / s i.castSucc` is linearly equivalent to `S`. -/
def IsCompositionFactorAt (s : CompositionSeries (Submodule R M)) (i : Fin s.length)
    (S : Type w) [AddCommGroup S] [Module R S] : Prop :=
  Nonempty ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R] S)

variable {s : CompositionSeries (Submodule R M)} {i : Fin s.length}
variable {S : Type w} [AddCommGroup S] [Module R S] {T : Type w'} [AddCommGroup T] [Module R T]

/-- Being a factor at a given index only depends on the isomorphism class of the module. -/
theorem IsCompositionFactorAt.congr (h : IsCompositionFactorAt s i S) (e : S ≃ₗ[R] T) :
    IsCompositionFactorAt s i T :=
  h.elim fun f => ⟨f.trans e⟩

/-- Being a factor at a given index only depends on the isomorphism class of the module. -/
theorem isCompositionFactorAt_congr (e : S ≃ₗ[R] T) :
    IsCompositionFactorAt s i S ↔ IsCompositionFactorAt s i T :=
  ⟨fun h => h.congr e, fun h => h.congr e.symm⟩

/-- **The factors of a composition series are simple**: each step of a composition series is a
covering, and a covering pair of submodules has simple quotient. -/
theorem isSimpleModule_subquotient (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
  have cov := s.step i
  (covBy_iff_quot_is_simple cov.le).mp cov

/-- A module that occurs as a factor of a composition series is simple. -/
theorem IsCompositionFactorAt.isSimpleModule (h : IsCompositionFactorAt s i S) :
    IsSimpleModule R S :=
  have := isSimpleModule_subquotient s i
  h.elim fun e => _root_.IsSimpleModule.congr e.symm

/-! ### The multiplicity along a fixed composition series -/

/-- The number of indices at which the composition series `s` has a factor isomorphic to `S`. -/
noncomputable def compositionMultiplicity (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] : ℕ :=
  Nat.card {i : Fin s.length // IsCompositionFactorAt s i S}

theorem compositionMultiplicity_le_length (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] : compositionMultiplicity s S ≤ s.length :=
  (Finite.card_subtype_le _).trans_eq (Nat.card_eq_fintype_card.trans (Fintype.card_fin _))

/-- Only simple modules occur as factors, so everything else has multiplicity zero. -/
theorem compositionMultiplicity_eq_zero_of_not_isSimpleModule
    (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] (hS : ¬ IsSimpleModule R S) :
    compositionMultiplicity s S = 0 := by
  have : IsEmpty {i : Fin s.length // IsCompositionFactorAt s i S} :=
    ⟨fun i => hS i.2.isSimpleModule⟩
  simp [compositionMultiplicity]

theorem compositionMultiplicity_congr (s : CompositionSeries (Submodule R M)) (e : S ≃ₗ[R] T) :
    compositionMultiplicity s S = compositionMultiplicity s T :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => isCompositionFactorAt_congr e)

/-- **Equivalent composition series have the same multiplicities.** The bijection of indices
underlying the equivalence matches the factors up to isomorphism, so it restricts to a bijection
between the indices carrying a copy of `S`. -/
theorem compositionMultiplicity_eq_of_equivalent {s₁ s₂ : CompositionSeries (Submodule R M)}
    (h : s₁.Equivalent s₂) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s₁ S = compositionMultiplicity s₂ S := by
  obtain ⟨f, hf⟩ := h
  refine Nat.card_congr (Equiv.subtypeEquiv f fun i => ?_)
  have e := (hf i).linearEquiv
  exact ⟨fun ⟨g⟩ => ⟨e.symm.trans g⟩, fun ⟨g⟩ => ⟨e.trans g⟩⟩

/-- **The multiplicity is a Jordan-Hölder invariant.** Two composition series with the same first
and last term count every module the same number of times. -/
theorem compositionMultiplicity_eq_of_head_eq_of_last_eq {s₁ s₂ : CompositionSeries (Submodule R M)}
    (hhead : s₁.head = s₂.head) (hlast : s₁.last = s₂.last)
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s₁ S = compositionMultiplicity s₂ S :=
  compositionMultiplicity_eq_of_equivalent (CompositionSeries.jordan_holder s₁ s₂ hhead hlast) S

/-! ### The multiplicity of a simple module in a module of finite length -/

variable (R M) in
/-- **The Jordan-Hölder multiplicity `[M : S]`**: the number of factors isomorphic to `S` in a
composition series of `M` running from `⊥` to `⊤`.  By
`TauCeti.compositionMultiplicity_eq_jordanHolderMultiplicity` any such series computes it, so the
choice of series below is immaterial. -/
noncomputable def jordanHolderMultiplicity [IsNoetherian R M] [IsArtinian R M]
    (S : Type w) [AddCommGroup S] [Module R S] : ℕ :=
  compositionMultiplicity (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose S

/-- **Every composition series from `⊥` to `⊤` computes the multiplicity.** -/
theorem compositionMultiplicity_eq_jordanHolderMultiplicity [IsNoetherian R M] [IsArtinian R M]
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = jordanHolderMultiplicity R M S :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_of_head_eq_of_last_eq (hbot.trans h.1.symm) (htop.trans h.2.symm) S

theorem jordanHolderMultiplicity_congr [IsNoetherian R M] [IsArtinian R M] (e : S ≃ₗ[R] T) :
    jordanHolderMultiplicity R M S = jordanHolderMultiplicity R M T :=
  compositionMultiplicity_congr _ e

/-- Only simple modules occur as composition factors. -/
theorem jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule [IsNoetherian R M] [IsArtinian R M]
    (S : Type w) [AddCommGroup S] [Module R S] (hS : ¬ IsSimpleModule R S) :
    jordanHolderMultiplicity R M S = 0 :=
  compositionMultiplicity_eq_zero_of_not_isSimpleModule _ S hS

/-! ### Transport along a linear equivalence of the ambient module -/

section Transport

variable {N : Type v'} [AddCommGroup N] [Module R N]

/-- The image of a composition series of `M` under a linear equivalence `M ≃ₗ[R] N`. -/
@[expose] def mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    CompositionSeries (Submodule R N) where
  length := s.length
  toFun i := Submodule.orderIsoMapComap e (s i)
  step i := (apply_covBy_apply_iff (Submodule.orderIsoMapComap e)).mpr (s.step i)

@[simp]
theorem mapCompositionSeries_apply (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M))
    (i : Fin (s.length + 1)) :
    mapCompositionSeries e s i = Submodule.map (e : M →ₗ[R] N) (s i) :=
  rfl

@[simp]
theorem length_mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeries e s).length = s.length :=
  rfl

theorem head_mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M))
    (hbot : s.head = ⊥) : (mapCompositionSeries e s).head = ⊥ := by
  have : s 0 = ⊥ := hbot
  change Submodule.map (e : M →ₗ[R] N) (s 0) = ⊥
  rw [this, Submodule.map_bot]

theorem last_mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M))
    (htop : s.last = ⊤) : (mapCompositionSeries e s).last = ⊤ := by
  have : s (Fin.last s.length) = ⊤ := htop
  change Submodule.map (e : M →ₗ[R] N) (s (Fin.last s.length)) = ⊤
  rw [this, Submodule.map_top, e.range]

/-- Restricting a linear equivalence to a submodule carries the trace of another submodule to the
trace of its image.  This is the compatibility that lets a linear equivalence be pushed through the
subquotients of a composition series. -/
theorem map_submoduleMap_comap_subtype (e : M ≃ₗ[R] N) (A B : Submodule R M) :
    Submodule.map (e.submoduleMap B).toLinearMap (Submodule.comap B.subtype A)
      = Submodule.comap (Submodule.map (e : M →ₗ[R] N) B).subtype
          (Submodule.map (e : M →ₗ[R] N) A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : M), hx, rfl⟩
  · rintro ⟨a, ha, hay⟩
    obtain ⟨b, hb, hby⟩ := y.2
    have hab : a = b := e.injective (hay.trans hby.symm)
    exact ⟨⟨a, hab ▸ hb⟩, ha, Subtype.ext hay⟩

/-- A linear equivalence identifies the factors of a composition series with those of its image. -/
noncomputable def factorEquivMapCompositionSeries (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R]
      (↥(mapCompositionSeries e s i.succ) ⧸
        Submodule.comap (mapCompositionSeries e s i.succ).subtype
          (mapCompositionSeries e s i.castSucc)) :=
  Submodule.Quotient.equiv _ _ (e.submoduleMap (s i.succ))
    (map_submoduleMap_comap_subtype e (s i.castSucc) (s i.succ))

theorem compositionMultiplicity_mapCompositionSeries (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity (mapCompositionSeries e s) S = compositionMultiplicity s S :=
  Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    ⟨fun ⟨f⟩ => ⟨(factorEquivMapCompositionSeries e s i).trans f⟩,
      fun ⟨f⟩ => ⟨(factorEquivMapCompositionSeries e s i).symm.trans f⟩⟩)

/-- **The multiplicity only depends on the isomorphism class of the ambient module.** -/
theorem jordanHolderMultiplicity_of_linearEquiv [IsNoetherian R M] [IsArtinian R M]
    [IsNoetherian R N] [IsArtinian R N] (e : M ≃ₗ[R] N)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S := by
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity (mapCompositionSeries e _)
      (head_mapCompositionSeries e _ h.1) (last_mapCompositionSeries e _ h.2) S,
    compositionMultiplicity_mapCompositionSeries]
  rfl

end Transport

/-! ### The two degenerate modules -/

/-- A composition series of a subsingleton module is a single point. -/
theorem length_eq_zero_of_subsingleton [Subsingleton M] (s : CompositionSeries (Submodule R M)) :
    s.length = 0 := by
  have : s 0 = s (Fin.last s.length) := Subsingleton.elim _ _
  simpa [Fin.ext_iff, eq_comm] using s.injective this

theorem compositionMultiplicity_of_subsingleton [Subsingleton M]
    (s : CompositionSeries (Submodule R M)) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = 0 :=
  Nat.le_zero.mp ((compositionMultiplicity_le_length s S).trans_eq
    (length_eq_zero_of_subsingleton s))

theorem jordanHolderMultiplicity_of_subsingleton [Subsingleton M] [IsNoetherian R M]
    [IsArtinian R M] (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = 0 :=
  compositionMultiplicity_of_subsingleton _ S

/-- The bottom-to-top subquotient of a module is the module itself. -/
theorem nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top {A B : Submodule R M} (hA : A = ⊥)
    (hB : B = ⊤) : Nonempty ((↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R] M) := by
  subst hA hB
  refine ⟨(Submodule.quotEquivOfEqBot _ ?_).trans Submodule.topEquiv⟩
  rw [Submodule.comap_bot, Submodule.ker_subtype]

/-- A composition series of a simple module from `⊥` to `⊤` has a single step. -/
theorem length_eq_one_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    s.length = 1 := by
  have hbot' : s 0 = ⊥ := hbot
  have htop' : s (Fin.last s.length) = ⊤ := htop
  -- The series is not constant, since `⊥ ≠ ⊤` in a simple module.
  have hlt : s 0 < s (Fin.last s.length) := by rw [hbot', htop']; exact bot_lt_top
  have hpos : 0 < s.length := by
    by_contra h
    exact absurd (congrArg s (Fin.ext (by omega : (0 : Fin (s.length + 1)).val =
      (Fin.last s.length).val))) hlt.ne
  by_contra h
  -- With at least two steps the term at index `1` is a submodule strictly between `⊥` and `⊤`.
  have h2 : 2 ≤ s.length := by omega
  set j : Fin (s.length + 1) := ⟨1, by omega⟩ with hj
  have h0j : (⊥ : Submodule R M) < s j := hbot' ▸ s.strictMono (by simp [hj, Fin.lt_def])
  have hjl : s j < (⊤ : Submodule R M) :=
    htop' ▸ s.strictMono (by simp [hj, Fin.lt_def]; omega)
  rcases IsSimpleOrder.eq_bot_or_eq_top (s j) with hb | ht
  · exact absurd hb h0j.ne'
  · exact absurd ht hjl.ne

/-- **The single factor of a simple module is that module.** Every index of a composition series
of a simple module running from `⊥` to `⊤` carries the module itself. -/
theorem isCompositionFactorAt_iff_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (i : Fin s.length) (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt s i S ↔ Nonempty (M ≃ₗ[R] S) := by
  have hbot' : s 0 = ⊥ := hbot
  have htop' : s (Fin.last s.length) = ⊤ := htop
  have hlen := length_eq_one_of_isSimpleModule hbot htop
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  have h0 : s i.castSucc = ⊥ := by
    rw [← hbot']
    exact congrArg s (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero, hi]))
  have h1 : s i.succ = ⊤ := by
    rw [← htop']
    exact congrArg s (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))
  obtain ⟨g⟩ := nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top h0 h1
  exact ⟨fun ⟨f⟩ => ⟨g.symm.trans f⟩, fun ⟨f⟩ => ⟨g.trans f⟩⟩

/-- **A simple module contains exactly one copy of itself.** -/
theorem compositionMultiplicity_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    compositionMultiplicity s S = 1 := by
  have hall : ∀ i : Fin s.length, IsCompositionFactorAt s i S := fun i =>
    (isCompositionFactorAt_iff_of_isSimpleModule hbot htop i S).mpr ⟨e⟩
  rw [compositionMultiplicity, Nat.card_congr (Equiv.subtypeUnivEquiv hall),
    Nat.card_eq_fintype_card, Fintype.card_fin, length_eq_one_of_isSimpleModule hbot htop]

/-- **A simple module contains no copy of a module it is not isomorphic to.** -/
theorem compositionMultiplicity_eq_zero_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    compositionMultiplicity s S = 0 := by
  have : IsEmpty {i : Fin s.length // IsCompositionFactorAt s i S} :=
    ⟨fun i => he.elim'
      ((isCompositionFactorAt_iff_of_isSimpleModule hbot htop i.1 S).mp i.2).some⟩
  simp [compositionMultiplicity]

/-- **A simple module contains exactly one copy of itself**, for the chosen composition series. -/
theorem jordanHolderMultiplicity_of_isSimpleModule [IsSimpleModule R M] [IsNoetherian R M]
    [IsArtinian R M] (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    jordanHolderMultiplicity R M S = 1 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_of_isSimpleModule h.1 h.2 S e

/-- **A simple module contains no copy of a module it is not isomorphic to.** -/
theorem jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule
    [IsSimpleModule R M] [IsNoetherian R M] [IsArtinian R M]
    (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    jordanHolderMultiplicity R M S = 0 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_zero_of_isSimpleModule h.1 h.2 S he

end TauCeti
