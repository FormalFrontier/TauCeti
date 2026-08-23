/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.BoundedPaths
public import TauCeti.RepresentationTheory.Quiver.Radical
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Admissible ideals and bound quiver algebras

A two-sided ideal `I` of a path algebra `kQ` is *admissible* when it is squeezed between a power
of the arrow ideal `R` and its square, `R ^ N ≤ I ≤ R ^ 2`. The two bounds say complementary
things about the relations `I` imposes. The upper bound `I ≤ R ^ 2` says that every relation is a
combination of paths of length at least two: a relation involving a vertex idempotent or a single
arrow would change the quiver data itself — identifying or collapsing vertices or arrows — rather
than impose a relation on the paths of `Q`. The lower bound `R ^ N ≤ I` says that all long enough
paths are killed, which is what cuts the quotient down to finite dimension.

The quotient `kQ ⧸ I` by an admissible ideal is a *bound quiver algebra*, and the two main results
here are its two basic properties: it is **finite-dimensional** whenever the quiver has finitely
many vertices and arrows, even when `kQ` itself is not, and every element of the arrow ideal
becomes **nilpotent** in it.

## Main definitions

* `TauCeti.IsAdmissibleIdeal`: the predicate `R ^ N ≤ I ≤ R ^ 2` on a two-sided ideal of a path
  algebra, for the arrow ideal `R = TauCeti.arrowIdeal k Q` and some `N`.

## Main results

* `TauCeti.IsAdmissibleIdeal.finiteDimensional_quotient`: **a bound quiver algebra is
  finite-dimensional**, over a quiver with finitely many vertices and finitely many arrows. No
  acyclicity is needed, and the one-loop quiver shows that this is a genuine gain: its path
  algebra `k[X]` is infinite-dimensional (`TauCeti.not_finiteDimensional_pathAlgebra_oneLoop`)
  while the quotients `k[X] ⧸ (Xⁿ)` by the admissible ideals of
  `TauCeti.isAdmissibleIdeal_arrowIdeal_pow` are not.
* `TauCeti.IsAdmissibleIdeal.isNilpotent_mk_of_mem_arrowIdeal`: the image of an element of
  the arrow ideal in a bound quiver algebra is nilpotent.
* `TauCeti.IsAdmissibleIdeal.ofPath_notMem_of_length_lt_two`, together with
  `TauCeti.IsAdmissibleIdeal.vertexIdempotent_notMem` and
  `TauCeti.IsAdmissibleIdeal.ofArrow_notMem`: an admissible ideal contains no vertex idempotent and
  no arrow, so the quiver survives the passage to the quotient. In particular the quotient is
  nonzero, `TauCeti.IsAdmissibleIdeal.nontrivial_quotient`. More is true and is
  `TauCeti.IsAdmissibleIdeal.linearIndependent_mk_ofPath_of_length_lt_two`: the vertices and the
  arrows stay *linearly independent* in the quotient, so the quotient map is injective on their
  span.
* `TauCeti.isAdmissibleIdeal_iff`: admissibility checked entirely on the path basis.
* `TauCeti.isAdmissibleIdeal_arrowIdeal_pow`: the powers `R ^ n` with `2 ≤ n` are admissible, and
  `TauCeti.isAdmissibleIdeal_bot_of_isAcyclic`: over a finite acyclic quiver the zero ideal is
  admissible, so `kQ` is itself a bound quiver algebra, with no relations.

## Implementation notes

The exponent `N` of the lower bound is existentially quantified in the definition rather than
carried as data: no result below depends on a particular choice, and quantifying it makes
`TauCeti.isAdmissibleIdeal_arrowIdeal_pow` and `TauCeti.isAdmissibleIdeal_bot_of_isAcyclic` the
statements they should be. The usual textbook phrasing adds `2 ≤ N`, which is redundant: `R ^ N`
decreases in `N`, so `R ^ N ≤ I` for some `N` gives it for every larger one.

`Ideal R` means *left* ideal in Mathlib, two-sidedness being the separate typeclass
`Ideal.IsTwoSided` — which `TauCeti.arrowIdeal` carries. Admissibility is a notion about
*two-sided* ideals: it is the quotient *algebra* `kQ ⧸ I` that it exists to describe, and the two
inclusions `R ^ N ≤ I ≤ R ^ 2` alone do not force `I` to be two-sided. `TauCeti.IsAdmissibleIdeal`
therefore takes `[I.IsTwoSided]` as an argument of the predicate itself, so that the ideals it
speaks of are exactly the admissible ones, and every consequence — in particular those about the
quotient, where `Ideal.Quotient` asks for the same instance — is available from the predicate
alone. For the ideals of `TauCeti.isAdmissibleIdeal_arrowIdeal_pow` and
`TauCeti.isAdmissibleIdeal_bot_of_isAcyclic` the instance is found by synthesis.

Finite dimensionality is proved by spanning: the images of the paths of length less than `N` span
the quotient, because every longer path already lies in `I`, and there are finitely many of them
(`TauCeti.Quiver.finite_setOf_length_lt`). This is where the finiteness of the *arrow* types
enters — the rest of the file needs only finitely many vertices, that being what makes `kQ`
unital.

## References

This implements the "admissible ideal" part of Layer 3A of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, the finite-dimensional
algebra infrastructure that its `kQ/I` presentation theorem rests on. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. II.2.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

section Defs

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- A two-sided ideal of a path algebra is **admissible** when some power of the arrow ideal is
contained in it and it is contained in the square of the arrow ideal. The quotient of the path
algebra by an admissible ideal is a *bound quiver algebra*. -/
structure IsAdmissibleIdeal (I : Ideal (pathAlgebra k Q)) [I.IsTwoSided] : Prop where
  /-- Some power of the arrow ideal is contained in `I`: all long enough paths are killed. -/
  exists_arrowIdeal_pow_le : ∃ N, arrowIdeal k Q ^ N ≤ I
  /-- `I` is contained in the square of the arrow ideal: every relation is supported on the paths
  of length at least two. -/
  le_arrowIdeal_sq : I ≤ arrowIdeal k Q ^ 2

namespace IsAdmissibleIdeal

variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- An admissible ideal is contained in the arrow ideal. -/
theorem le_arrowIdeal (h : IsAdmissibleIdeal I) : I ≤ arrowIdeal k Q :=
  h.le_arrowIdeal_sq.trans (Ideal.pow_le_self (by norm_num))

/-- **An admissible ideal contains every long enough path**: this is the lower bound, read on the
path basis. -/
theorem exists_ofPath_mem (h : IsAdmissibleIdeal I) :
    ∃ N, ∀ x : Quiver.TotalPath Q, N ≤ x.2.2.length → (ofPath x : pathAlgebra k Q) ∈ I := by
  obtain ⟨N, hN⟩ := h.exists_arrowIdeal_pow_le
  exact ⟨N, fun x hx => hN (mem_arrowIdeal_pow.2 (ofPath_mem_pathSpan hx))⟩

/-- **An admissible ideal contains no short path**: this is the upper bound, read on the path
basis. It excludes one at a time the basis paths of length less than two, the vertex idempotents
and the arrows; that no nonzero combination of them is erased either is
`TauCeti.IsAdmissibleIdeal.linearIndependent_mk_ofPath_of_length_lt_two`. -/
theorem ofPath_notMem_of_length_lt_two [Nontrivial k] (h : IsAdmissibleIdeal I)
    {x : Quiver.TotalPath Q} (hx : x.2.2.length < 2) :
    (ofPath x : pathAlgebra k Q) ∉ I := by
  intro hmem
  have hx2 := ofPath_mem_arrowIdeal_pow_iff.1 (h.le_arrowIdeal_sq hmem)
  omega

/-- No vertex idempotent lies in an admissible ideal: the vertices survive in the quotient. -/
theorem vertexIdempotent_notMem [Nontrivial k] (h : IsAdmissibleIdeal I) (a : Q) :
    (vertexIdempotent k a : pathAlgebra k Q) ∉ I := fun hmem =>
  vertexIdempotent_notMem_arrowIdeal a (h.le_arrowIdeal hmem)

/-- No arrow lies in an admissible ideal: the arrows survive in the quotient. -/
theorem ofArrow_notMem [Nontrivial k] (h : IsAdmissibleIdeal I) {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) ∉ I := by
  rw [ofArrow_eq_ofPath]
  exact h.ofPath_notMem_of_length_lt_two (by simp [_root_.Quiver.Path.length_toPath])

/-- An admissible ideal of the path algebra of a nonempty quiver is proper. -/
theorem ne_top [Nontrivial k] [Nonempty Q] (h : IsAdmissibleIdeal I) : I ≠ ⊤ := by
  intro htop
  refine h.vertexIdempotent_notMem (Classical.arbitrary Q) ?_
  rw [htop]
  exact Submodule.mem_top

end IsAdmissibleIdeal

/-- **Admissibility, read entirely on the path basis**: the lower bound need only be checked on the
basis paths, since a `k`-submodule containing every path of length at least `N` contains their whole
span, which is `R ^ N`. This is how admissibility of a concretely given ideal of relations is
verified. -/
theorem isAdmissibleIdeal_iff {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided] :
    IsAdmissibleIdeal I ↔
      (∃ N, ∀ x : Quiver.TotalPath Q, N ≤ x.2.2.length → (ofPath x : pathAlgebra k Q) ∈ I) ∧
        I ≤ arrowIdeal k Q ^ 2 := by
  refine ⟨fun h => ⟨h.exists_ofPath_mem, h.le_arrowIdeal_sq⟩, fun ⟨⟨N, hN⟩, hsq⟩ => ⟨⟨N, ?_⟩, hsq⟩⟩
  intro f hf
  have hcoord := mem_pathSpan_iff.1 (mem_arrowIdeal_pow.1 hf)
  -- Expand `f` in the path basis: every path in its support is long enough, hence lies in `I`.
  suffices hsuff : f ∈ Submodule.restrictScalars k I from hsuff
  rw [← (pathAlgebraBasis k Q).linearCombination_repr f, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ ?_
  simpa [coe_pathAlgebraBasis] using hN x (hcoord x (Finsupp.mem_support_iff.1 hx))

variable (k Q)

/-- **The powers of the arrow ideal from the second on are admissible.** These are the *monomial*
relations: `R ^ n` is the ideal spanned by the paths of length at least `n`. -/
theorem isAdmissibleIdeal_arrowIdeal_pow {n : ℕ} (hn : 2 ≤ n) :
    IsAdmissibleIdeal (arrowIdeal k Q ^ n) where
  exists_arrowIdeal_pow_le := ⟨n, le_rfl⟩
  le_arrowIdeal_sq := Ideal.pow_le_pow_right hn

/-- **Over a finite acyclic quiver the zero ideal is admissible**: the path algebra is itself a
bound quiver algebra, with no relations. Acyclicity supplies the truncation by itself: every path
is shorter than the number of vertices, so the arrow ideal is already nilpotent. -/
theorem isAdmissibleIdeal_bot_of_isAcyclic (h : Quiver.IsAcyclic Q) :
    IsAdmissibleIdeal (⊥ : Ideal (pathAlgebra k Q)) where
  exists_arrowIdeal_pow_le := ⟨Nat.card Q, fun f hf => by
    have hbot : f ∈ (⊥ : Submodule k (pathAlgebra k Q)) := by
      rw [← pathSpan_eq_bot_of_isAcyclic k Q h]
      exact mem_arrowIdeal_pow.1 hf
    rw [Submodule.mem_bot] at hbot
    exact hbot ▸ Submodule.zero_mem _⟩
  le_arrowIdeal_sq := bot_le

end Defs

/-! ### The bound quiver algebra -/

section Quotient

variable {k : Type w} {Q : Type u} [CommRing k] [Quiver.{v} Q] [Finite Q]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

namespace IsAdmissibleIdeal

/-- **Every element of the arrow ideal is nilpotent in a bound quiver algebra**: its `N`-th power
is supported on the paths of length at least `N`, which the ideal has already killed. Over an
acyclic quiver this holds already in `kQ` (`TauCeti.isNilpotent_of_mem_arrowIdeal`); admissibility
is what replaces acyclicity in general. -/
theorem isNilpotent_mk_of_mem_arrowIdeal (h : IsAdmissibleIdeal I) {f : pathAlgebra k Q}
    (hf : f ∈ arrowIdeal k Q) : IsNilpotent (Ideal.Quotient.mk I f) := by
  obtain ⟨N, hN⟩ := h.exists_arrowIdeal_pow_le
  refine ⟨N, ?_⟩
  rw [← map_pow]
  refine Ideal.Quotient.eq_zero_iff_mem.2 (hN (mem_arrowIdeal_pow.2 ?_))
  exact pow_mem_pathSpan (mem_arrowIdeal_pow.1 (by rwa [Submodule.pow_one])) N

/-- **The vertices and the arrows stay independent in a bound quiver algebra**: the images of the
paths of length less than two are linearly independent over `k`, so the quotient map is injective
on their span. This is the upper bound `I ≤ R ^ 2` read on the quotient, and it says more than the
individual nonmemberships `TauCeti.IsAdmissibleIdeal.vertexIdempotent_notMem` and
`TauCeti.IsAdmissibleIdeal.ofArrow_notMem`: distinct vertices stay distinct, distinct arrows stay
distinct, and no nonzero combination of them is erased. -/
theorem linearIndependent_mk_ofPath_of_length_lt_two (h : IsAdmissibleIdeal I) :
    LinearIndependent k fun x : {x : Quiver.TotalPath Q // x.2.2.length < 2} =>
      Ideal.Quotient.mk I (ofPath x.1) := by
  -- The short paths span a complement of `R ^ 2`, which already contains `I`.
  have hdisj : Disjoint
      (Submodule.span k (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.length < 2} =>
        pathAlgebraBasis k Q x.1))
      (LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap) := by
    have hrange : (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.length < 2} =>
        pathAlgebraBasis k Q x.1)
        = pathAlgebraBasis k Q '' {x : Quiver.TotalPath Q | x.2.2.length < 2} := by
      ext y
      simp [Set.mem_image, Subtype.exists]
    rw [Submodule.disjoint_def, hrange]
    intro f hshort hmem
    -- Every path in the support of `f` is short, being in the span of the short ones, and long,
    -- `f` lying in `I ≤ R ^ 2`. So there is none, and `f = 0`.
    have hlt := (pathAlgebraBasis k Q).mem_span_image.1 hshort
    have hle : ∀ x : Quiver.TotalPath Q, (pathAlgebraBasis k Q).repr f x ≠ 0 →
        2 ≤ x.2.2.length := by
      refine mem_pathSpan_iff.1 (mem_arrowIdeal_pow.1 (h.le_arrowIdeal_sq ?_))
      rwa [LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem] at hmem
    refine (pathAlgebraBasis k Q).repr.map_eq_zero_iff.1 (Finsupp.ext fun x => ?_)
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hx
    have hxshort : x.2.2.length < 2 := hlt (Finsupp.mem_support_iff.2 hx)
    have hxlong : 2 ≤ x.2.2.length := hle x hx
    omega
  simpa [Function.comp_def, Ideal.Quotient.mkₐ_eq_mk] using
    ((pathAlgebraBasis k Q).linearIndependent.comp _ Subtype.val_injective).map hdisj

/-- A bound quiver algebra over a nonempty quiver is nonzero: an admissible ideal is proper, the
vertex idempotents escaping it. -/
theorem nontrivial_quotient [Nontrivial k] [Nonempty Q] (h : IsAdmissibleIdeal I) :
    Nontrivial (pathAlgebra k Q ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.2 h.ne_top

end IsAdmissibleIdeal

end Quotient

section FiniteDimensional

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Finite Q]
variable [∀ a b : Q, Finite (a ⟶ b)]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- **A bound quiver algebra is finite-dimensional.** The images of the paths of length less than
`N` span it, because a longer path already lies in the ideal, and a quiver with finitely many
vertices and finitely many arrows has only finitely many paths of bounded length. The path algebra
itself need not be finite-dimensional: that needs finitely many paths of *every* length, hence
acyclicity, whereas the bound `R ^ N ≤ I` supplies the missing truncation. -/
theorem IsAdmissibleIdeal.finiteDimensional_quotient (h : IsAdmissibleIdeal I) :
    FiniteDimensional k (pathAlgebra k Q ⧸ I) := by
  obtain ⟨N, hN⟩ := h.exists_ofPath_mem
  set π : pathAlgebra k Q →ₗ[k] pathAlgebra k Q ⧸ I := (Ideal.Quotient.mkₐ k I).toLinearMap with hπ
  have hπ_apply (f : pathAlgebra k Q) : π f = Ideal.Quotient.mk I f := by
    rw [hπ, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  -- The images of *all* the basis paths span the quotient, the quotient map being onto.
  have htop : Submodule.span k (Set.range fun x : Quiver.TotalPath Q => π (ofPath x)) = ⊤ := by
    have hmap : Submodule.map π ⊤ = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 (fun y => by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨f, rfl⟩)]
    rw [← hmap, ← (pathAlgebraBasis k Q).span_eq, Submodule.map_span, coe_pathAlgebraBasis,
      ← Set.range_comp]
    rfl
  -- Only the short ones are needed: the rest map to zero.
  have hshort : Submodule.span k
      ((fun x : Quiver.TotalPath Q => π (ofPath x)) '' {x | x.2.2.length < N}) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htop]
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun x => SetLike.mem_coe.2 ?_)
    by_cases hx : x.2.2.length < N
    · exact Submodule.subset_span ⟨x, hx, rfl⟩
    · have hzero : π (ofPath x) = 0 :=
        (hπ_apply _).trans (Ideal.Quotient.eq_zero_iff_mem.2 (hN x (by omega)))
      rw [hzero]
      exact Submodule.zero_mem _
  exact ⟨hshort ▸ Submodule.fg_span ((Quiver.finite_setOf_length_lt N).image _)⟩

end FiniteDimensional

end TauCeti
