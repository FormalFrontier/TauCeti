/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import TauCeti.RingTheory.CompositionSeries.Basic

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
*number* of factors — and, with it, `Module.length_compositionSeries`, which is what pins down the
length of a composition series of a subsingleton or a simple module below.  The multiplicity of an
individual simple module is not there.

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

## Main results

* `TauCeti.compositionMultiplicity_eq_of_head_eq_of_last_eq`: **the multiplicity is a
  Jordan-Hölder invariant** — two composition series with the same endpoints count every module
  the same number of times.  This is what makes `TauCeti.jordanHolderMultiplicity` well defined,
  and `TauCeti.compositionMultiplicity_eq_jordanHolderMultiplicity` says that *every* composition
  series from `⊥` to `⊤` computes it.
* `TauCeti.IsCompositionFactorAt.isSimpleModule`: the factors are simple, so the multiplicity of a
  module that is not simple vanishes
  (`TauCeti.jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule`).
* `TauCeti.jordanHolderMultiplicity_eq_of_linearEquiv`: **the multiplicity is an invariant of the
  isomorphism class of the ambient module**, which is what makes `[Pᵢ : Sⱼ]` well posed for a
  projective cover, an object defined only up to isomorphism.  The transport of a composition
  series along a linear equivalence that this rests on is
  `TauCeti.RingTheory.CompositionSeries.Basic`.
* `TauCeti.jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv` and
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

/-- The defining property of `TauCeti.IsCompositionFactorAt`: it is the existence of a linear
equivalence between the subquotient at the index and the given module.  This is what introduces and
eliminates the predicate. -/
theorem isCompositionFactorAt_iff :
    IsCompositionFactorAt s i S ↔
      Nonempty ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R] S) :=
  (Iff.rfl)

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
@[grind →]
theorem IsCompositionFactorAt.isSimpleModule (h : IsCompositionFactorAt s i S) :
    IsSimpleModule R S :=
  have := isSimpleModule_subquotient s i
  h.elim fun e => _root_.IsSimpleModule.congr e.symm

/-! ### The multiplicity along a fixed composition series -/

/-- The number of indices at which the composition series `s` has a factor isomorphic to `S`. -/
noncomputable def compositionMultiplicity (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] : ℕ :=
  Nat.card {i : Fin s.length // IsCompositionFactorAt s i S}

/-- The defining formula for `TauCeti.compositionMultiplicity`, so that it can be evaluated on a
concrete composition series. -/
theorem compositionMultiplicity_def (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = Nat.card {i : Fin s.length // IsCompositionFactorAt s i S} :=
  (rfl)

/-- `S` occurs in `s` — the multiplicity is nonzero — exactly when some index carries a copy of
`S`. -/
theorem compositionMultiplicity_ne_zero_iff (s : CompositionSeries (Submodule R M))
    (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S ≠ 0 ↔ ∃ i, IsCompositionFactorAt s i S := by
  rw [compositionMultiplicity_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun i => ⟨i.1, i.2⟩, fun ⟨i, hi⟩ => ⟨⟨⟨i, hi⟩⟩, inferInstance⟩⟩

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
  simp [compositionMultiplicity_def]

/-- The multiplicity along a fixed composition series depends on `S` only through its isomorphism
class. -/
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

/-- `S` is a composition factor of `M` — the multiplicity `[M : S]` is nonzero — exactly when some
index of a composition series from `⊥` to `⊤` carries a copy of `S`. -/
theorem jordanHolderMultiplicity_ne_zero_iff [IsNoetherian R M] [IsArtinian R M]
    (s : CompositionSeries (Submodule R M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S ≠ 0 ↔ ∃ i, IsCompositionFactorAt s i S := by
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop,
    compositionMultiplicity_ne_zero_iff]

/-- The multiplicity `[M : S]` depends on `S` only through its isomorphism class. -/
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

/-- Transporting a composition series along a linear equivalence does not change which module sits
at an index. -/
@[simp]
theorem isCompositionFactorAt_mapCompositionSeries_iff (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length)
    (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt (mapCompositionSeries e s) i S ↔ IsCompositionFactorAt s i S :=
  ⟨fun ⟨f⟩ => ⟨(factorEquivMapCompositionSeries e s i).trans f⟩,
    fun ⟨f⟩ => ⟨(factorEquivMapCompositionSeries e s i).symm.trans f⟩⟩

/-- **Transport preserves multiplicities.** The image of a composition series under a linear
equivalence of the ambient module counts every module the same number of times as the series
itself. -/
@[simp]
theorem compositionMultiplicity_mapCompositionSeries (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity (mapCompositionSeries e s) S = compositionMultiplicity s S :=
  Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    isCompositionFactorAt_mapCompositionSeries_iff e s i S)

/-- **The multiplicity only depends on the isomorphism class of the ambient module.** -/
theorem jordanHolderMultiplicity_eq_of_linearEquiv [IsNoetherian R M] [IsArtinian R M]
    [IsNoetherian R N] [IsArtinian R N] (e : M ≃ₗ[R] N)
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S := by
  obtain ⟨s, hbot, htop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R M
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop S,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity (mapCompositionSeries e s)
      (by rw [head_mapCompositionSeries, hbot, Submodule.map_bot])
      (by rw [last_mapCompositionSeries, htop, Submodule.map_top, e.range]) S,
    compositionMultiplicity_mapCompositionSeries]

end Transport

/-! ### Modules of length zero and one -/

/-- A composition series of a subsingleton module is a single point. -/
theorem compositionSeries_length_eq_zero_of_subsingleton [Subsingleton M]
    (s : CompositionSeries (Submodule R M)) : s.length = 0 := by
  simpa using Module.length_compositionSeries s (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- A subsingleton module has no composition factors at all. -/
theorem compositionMultiplicity_eq_zero_of_subsingleton [Subsingleton M]
    (s : CompositionSeries (Submodule R M)) (S : Type w) [AddCommGroup S] [Module R S] :
    compositionMultiplicity s S = 0 :=
  Nat.le_zero.mp ((compositionMultiplicity_le_length s S).trans_eq
    (compositionSeries_length_eq_zero_of_subsingleton s))

/-- Every multiplicity `[M : S]` in a subsingleton module `M` vanishes. -/
theorem jordanHolderMultiplicity_eq_zero_of_subsingleton [Subsingleton M]
    (S : Type w) [AddCommGroup S] [Module R S] :
    jordanHolderMultiplicity R M S = 0 :=
  compositionMultiplicity_eq_zero_of_subsingleton _ S

/-- The bottom-to-top subquotient of a module is the module itself. -/
theorem nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top {A B : Submodule R M} (hA : A = ⊥)
    (hB : B = ⊤) : Nonempty ((↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R] M) := by
  subst hA hB
  refine ⟨(Submodule.quotEquivOfEqBot _ ?_).trans Submodule.topEquiv⟩
  rw [Submodule.comap_bot, Submodule.ker_subtype]

/-- A composition series of a simple module from `⊥` to `⊤` has a single step. -/
theorem compositionSeries_length_eq_one_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤) :
    s.length = 1 := by
  simpa using Module.length_compositionSeries s hbot htop

/-- **The single factor of a simple module is that module.** Every index of a composition series
of a simple module running from `⊥` to `⊤` carries the module itself. -/
theorem isCompositionFactorAt_iff_of_isSimpleModule [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (i : Fin s.length) (S : Type w) [AddCommGroup S] [Module R S] :
    IsCompositionFactorAt s i S ↔ Nonempty (M ≃ₗ[R] S) := by
  have hbot' : s 0 = ⊥ := s.apply_zero.trans hbot
  have htop' : s (Fin.last s.length) = ⊤ := s.apply_last.trans htop
  have hlen := compositionSeries_length_eq_one_of_isSimpleModule hbot htop
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  have h0 : s i.castSucc = ⊥ := by
    rw [← hbot']
    exact congrArg s (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero, hi]))
  have h1 : s i.succ = ⊤ := by
    rw [← htop']
    exact congrArg s (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))
  obtain ⟨g⟩ := nonempty_linearEquiv_subquotient_of_eq_bot_of_eq_top h0 h1
  exact ⟨fun ⟨f⟩ => ⟨g.symm.trans f⟩, fun ⟨f⟩ => ⟨g.trans f⟩⟩

/-- **A simple module contains exactly one copy of itself**, counted along a fixed composition
series of it running from `⊥` to `⊤`. -/
theorem compositionMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    compositionMultiplicity s S = 1 := by
  have hall : ∀ i : Fin s.length, IsCompositionFactorAt s i S := fun i =>
    (isCompositionFactorAt_iff_of_isSimpleModule hbot htop i S).mpr ⟨e⟩
  rw [compositionMultiplicity_def, Nat.card_congr (Equiv.subtypeUnivEquiv hall),
    Nat.card_eq_fintype_card, Fintype.card_fin,
    compositionSeries_length_eq_one_of_isSimpleModule hbot htop]

/-- **A simple module contains no copy of a module it is not isomorphic to**, counted along a fixed
composition series of it running from `⊥` to `⊤`. -/
theorem compositionMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule
    [IsSimpleModule R M]
    {s : CompositionSeries (Submodule R M)} (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    compositionMultiplicity s S = 0 := by
  have : IsEmpty {i : Fin s.length // IsCompositionFactorAt s i S} :=
    ⟨fun i => he.elim'
      ((isCompositionFactorAt_iff_of_isSimpleModule hbot htop i.1 S).mp i.2).some⟩
  simp [compositionMultiplicity_def]

/-- **A simple module contains exactly one copy of itself**: the multiplicity `[M : S]` of a simple
module `M` in itself is `1`. -/
theorem jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv [IsSimpleModule R M]
    (S : Type w) [AddCommGroup S] [Module R S] (e : M ≃ₗ[R] S) :
    jordanHolderMultiplicity R M S = 1 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv h.1 h.2 S e

/-- **A simple module contains no copy of a module it is not isomorphic to**: the multiplicity
`[M : S]` vanishes for a simple `M` admitting no linear equivalence with `S`. -/
theorem jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule
    [IsSimpleModule R M] (S : Type w) [AddCommGroup S] [Module R S] (he : IsEmpty (M ≃ₗ[R] S)) :
    jordanHolderMultiplicity R M S = 0 :=
  have h := (exists_compositionSeries_of_isNoetherian_isArtinian R M).choose_spec
  compositionMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule h.1 h.2 S he

end TauCeti
