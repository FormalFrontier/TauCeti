/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.Algebra.CentralSimple.Centralizer` is imported publicly: the identification
-- `TauCeti.centralizerAlgEquivEnd` of the centralizer of a subalgebra with an endomorphism algebra
-- is what the dimension count below runs on, and it carries with it the module structure on
-- `TauCeti.Bimodule` that the count is stated through. It re-exports
-- `Mathlib.Algebra.Algebra.Subalgebra.Basic`, hence `Subalgebra.centralizer`, which occurs in the
-- statements below.
public import TauCeti.Algebra.CentralSimple.Centralizer
-- `TauCeti.Algebra.CentralSimple.Subfield` is imported publicly: `TauCeti.Algebra.deg` and
-- `TauCeti.Algebra.IsSplittingField` occur in the statements below, and
-- `TauCeti.Algebra.isSplittingField_of_finrank_eq_deg` is the theorem the summit of this file
-- feeds. It re-exports `TauCeti.Algebra.CentralSimple.Splitting` and, through it, the degree API.
public import TauCeti.Algebra.CentralSimple.Subfield
-- Non-public: none of these appears in the type of an exported declaration. The lattice of
-- subalgebras supplies `Algebra.adjoin` and the commutativity of an adjunction of pairwise
-- commuting elements; the finite-dimensional comparison of nested subalgebras is what turns
-- maximal dimension into maximality; the Artinian criterion for a domain to be a field, and the
-- simplicity of a field, turn a maximal commutative subalgebra into a subfield; and the
-- endomorphism algebra of a module over a simple Artinian algebra is the engine of the dimension
-- count. The real quaternions and their centrality appear only in the worked examples.
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleRing.Field
import TauCeti.Algebra.Central.Quaternion
import TauCeti.RingTheory.Semisimple.EndAlgebra

/-!
# Maximal subfields of a central division algebra

Let `K` be a field and `D` a finite-dimensional central division algebra over `K`.
`TauCeti/Algebra/CentralSimple/Subfield.lean` proves that a subfield of `D` has degree at most
`TauCeti.Algebra.deg K D`, and that a subfield attaining that bound splits `D`; what it leaves
open, in as many words, is whether the bound is attained at all. This file settles that: **`D` has
a subfield of degree exactly `deg K D`**, so the splitting field produced there is never vacuous
and every central division algebra is split by a finite extension of its centre sitting inside it.

The subfield is produced by maximality, in three steps.

*A commutative subalgebra of maximal dimension exists.* Dimensions of subalgebras of `D` are
bounded by `finrank K D`, so among the commutative ones there is a subalgebra `L` of largest
dimension (`TauCeti.exists_isMulCommutative_forall_finrank_le`). Nothing about `D` is used here
beyond finite-dimensionality.

*It is its own centralizer.* If `x` centralizes `L` then `L` and `x` together generate a
commutative subalgebra `Algebra.adjoin K (insert x L)`, which contains `L`; maximal dimension makes
the containment an equality, so `x ∈ L`. This is
`TauCeti.centralizer_eq_self_of_forall_finrank_le`, and it is also what makes `L` a *maximal*
subfield rather than merely a large one.

*Its dimension is forced.* For any subfield `L` of a finite-dimensional central simple algebra `A`,

  `finrank K L * finrank K C_A(L) = finrank K A`

(`TauCeti.finrank_mul_finrank_centralizer_of_isField`). Applied to `C_D(L) = L` this reads
`(finrank K L)² = finrank K D = (deg K D)²`, so `finrank K L = deg K D`.

The dimension count is the argument of `TauCeti.finrank_mul_finrank_centralizer`, run with the
centrality hypothesis moved from the subalgebra to the ambient algebra: what
`TauCeti.centralizerAlgEquivEnd` and `TauCeti.IsSimpleRing.finrank_end_mul_finrank_eq_sq` between
them need is that `L ⊗[K] Aᵐᵒᵖ` be simple, and that follows from `L` being simple and `Aᵐᵒᵖ` central
simple just as well as from `L` being central simple and `Aᵐᵒᵖ` simple. A subfield is simple but
not central, so it is the first reading that applies here.

## Main results

* `TauCeti.exists_isMulCommutative_forall_finrank_le`: a finite-dimensional algebra has a
  commutative subalgebra of maximal dimension.
* `TauCeti.centralizer_eq_self_of_forall_finrank_le`: in a division algebra such a subalgebra is
  its own centralizer.
* `TauCeti.isField_of_isMulCommutative`: a commutative subalgebra of a division algebra, finite
  over the base field, is a field.
* `TauCeti.finrank_mul_finrank_centralizer_of_isField`: the centralizer of a **subfield** of a
  central simple algebra has the complementary dimension.
* `TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`: **a central division algebra has a
  subfield of degree `deg K D`.**
* `TauCeti.Algebra.exists_isSplittingField_finrank_eq_deg`: **a central division algebra is split
  by a subfield of degree `deg K D`.**

## Implementation notes

Commutativity of a subalgebra is Mathlib's `IsMulCommutative` on its coercion to a type, which is
what `Algebra.isMulCommutative_adjoin` produces and what the scoped instances of the
`IsMulCommutative` namespace turn into a `CommRing` structure; the file therefore opens that scope
rather than carrying a hand-rolled `∀ x ∈ L, ∀ y ∈ L, x * y = y * x`.

`TauCeti.finrank_mul_finrank_centralizer_of_isField` asks for `IsField ↥L` and not for the weaker
`IsSimpleRing ↥L`. The proof would go through unchanged for a merely simple subalgebra, but that
statement is the general centralizer theorem for a non-central simple subalgebra, which the Layer 5
bullet of the roadmap referenced below rules out in as many words: "the general form for a merely
simple subalgebra `B` (center `Z(B) ⊋ K`) needs a center-sensitive correction to the dimension
formula and is a **later** target, not this one", to be taken up together with the description of
the centralizer's centre. Only the subfield case, which is what the maximal-subfield theory needs,
is claimed here.

The existence statements are stated for a **division** algebra. The passage from there to an
arbitrary central simple algebra `A ≃ₐ[K] Mₙ(D)`, and with it the index `ind A`, needs the
uniqueness of the division algebra in a Wedderburn presentation and is not done here.

## References

This is the maximal-subfield existence half of the fourth bullet of Layer 6 ("Splitting fields,
maximal subfields, and the index": "a **maximal subfield** `L` of a central division algebra `D`
(with `finrank K L = deg D`) splits `D`") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
-/

public section

namespace TauCeti

open Module

open scoped IsMulCommutative TensorProduct

universe u

/-! ### A commutative subalgebra of maximal dimension -/

section Maximal

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **A finite-dimensional algebra has a commutative subalgebra of maximal dimension.**

The dimensions of commutative subalgebras form a set of naturals bounded by `finrank K A` and
containing `finrank K ⊥`, so it has a greatest element, and any subalgebra realizing it will do.
No hypothesis beyond finite-dimensionality is needed; it is in a division algebra that such a
subalgebra becomes interesting (`TauCeti.centralizer_eq_self_of_forall_finrank_le`). -/
theorem exists_isMulCommutative_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative ↥L ∧
      ∀ M : Subalgebra K A, IsMulCommutative ↥M → finrank K ↥M ≤ finrank K ↥L := by
  classical
  set P : ℕ → Prop := fun n ↦ ∃ M : Subalgebra K A, IsMulCommutative ↥M ∧ finrank K ↥M = n
  -- The bottom subalgebra is commutative, so `P` is satisfied below the bound `finrank K A`.
  have hbot : IsMulCommutative ↥(⊥ : Subalgebra K A) :=
    Algebra.adjoin_empty K A ▸ Algebra.isMulCommutative_adjoin K (by simp)
  have hle : ∀ M : Subalgebra K A, finrank K ↥M ≤ finrank K A := fun M ↦
    Submodule.finrank_le (Subalgebra.toSubmodule M)
  have hstart : P (finrank K ↥(⊥ : Subalgebra K A)) := ⟨⊥, hbot, rfl⟩
  obtain ⟨L, hL, hLn⟩ := Nat.findGreatest_spec (hle ⊥) hstart
  refine ⟨L, hL, fun M hM ↦ ?_⟩
  rw [hLn]
  exact Nat.le_findGreatest (hle M) ⟨M, hM, rfl⟩

end Maximal

/-! ### Maximal commutative subalgebras of a division algebra -/

section DivisionRing

variable {K D : Type*} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

/-- **A commutative subalgebra of maximal dimension in a division algebra is its own
centralizer.**

An element `x` of the centralizer commutes with every element of `L`, and the elements of `L`
commute with one another, so `Algebra.adjoin K (insert x L)` is a commutative subalgebra. It
contains `L`, and maximal dimension forces the containment to be an equality, so `x ∈ L`. -/
theorem centralizer_eq_self_of_forall_finrank_le {L : Subalgebra K D} [IsMulCommutative ↥L]
    (hmax : ∀ M : Subalgebra K D, IsMulCommutative ↥M → finrank K ↥M ≤ finrank K ↥L) :
    Subalgebra.centralizer K (L : Set D) = L := by
  refine le_antisymm (fun x hx ↦ ?_) (fun y hy z hz ↦ ?_)
  · -- The elements of `insert x L` commute pairwise.
    have hcomm : ∀ a ∈ insert x (L : Set D), ∀ b ∈ insert x (L : Set D), a * b = b * a := by
      rintro a (rfl | ha) b (rfl | hb)
      · rfl
      · exact ((Subalgebra.mem_centralizer_iff K).1 hx b hb).symm
      · exact (Subalgebra.mem_centralizer_iff K).1 hx a ha
      · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥L) ⟨b, hb⟩)
    have hM : IsMulCommutative ↥(Algebra.adjoin K (insert x (L : Set D))) :=
      Algebra.isMulCommutative_adjoin K hcomm
    have hsub : L ≤ Algebra.adjoin K (insert x (L : Set D)) := fun a ha ↦
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)
    have := Subalgebra.eq_of_le_of_finrank_le hsub (hmax _ hM)
    exact this ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  · exact congrArg Subtype.val (mul_comm (⟨z, hz⟩ : ↥L) ⟨y, hy⟩)

omit [FiniteDimensional K D] in
/-- **A commutative subalgebra of a division algebra is a field**, as soon as it is
finite-dimensional over the base field: it is a commutative domain, and an Artinian domain is a
field. Only `L` need be finite-dimensional; the ambient `D` need not be. -/
theorem isField_of_isMulCommutative (L : Subalgebra K D) [IsMulCommutative ↥L]
    [FiniteDimensional K ↥L] : IsField ↥L := by
  have : IsArtinianRing ↥L := IsArtinianRing.of_finite K ↥L
  exact IsArtinianRing.isField_of_isDomain ↥L

end DivisionRing

/-! ### The centralizer of a subfield -/

section Centralizer

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **The dimension of the centralizer of a subfield of a central simple algebra is the
complementary one**:

  `finrank K L * finrank K C_A(L) = finrank K A`.

This is the argument of `TauCeti.finrank_mul_finrank_centralizer` with the centrality hypothesis
moved from the subalgebra to the ambient algebra. Both proofs need only that `L ⊗[K] Aᵐᵒᵖ` be a
simple Artinian ring, which `TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` supplies from
the simplicity of the field `L` and the central simplicity of `Aᵐᵒᵖ`; `L` itself is not central
over `K` unless it is `K`, so the form proved there does not apply. -/
theorem finrank_mul_finrank_centralizer_of_isField (L : Subalgebra K A) (hL : IsField ↥L) :
    finrank K ↥L * finrank K ↥(Subalgebra.centralizer K (L : Set A)) = finrank K A := by
  have : FiniteDimensional K ↥L :=
    FiniteDimensional.of_injective L.val.toLinearMap Subtype.val_injective
  have : IsMulCommutative ↥L := ⟨⟨hL.mul_comm⟩⟩
  have : IsSimpleRing ↥L := (isSimpleRing_iff_isField ↥L).2 hL
  have key := IsSimpleRing.finrank_end_mul_finrank_eq_sq K (R := ↥L ⊗[K] Aᵐᵒᵖ)
    (M := Bimodule L.val)
  rw [(Bimodule.of (L.val)).finrank_eq.symm, Module.finrank_tensorProduct,
    (MulOpposite.opLinearEquiv K (M := A)).finrank_eq.symm,
    ← (centralizerAlgEquivEnd L).toLinearEquiv.finrank_eq] at key
  -- `key : c * (l * a) = a ^ 2`; cancel one factor of `a = finrank K A`.
  have ha : 0 < finrank K A := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_right ha ?_
  rw [sq] at key
  rw [mul_comm (finrank K ↥L), mul_assoc]
  exact key

end Centralizer

/-! ### The maximal subfield of a central division algebra -/

namespace Algebra

variable (K : Type*) [Field K] (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D]

/-- **A central division algebra has a subfield of degree `deg K D`.**

A commutative subalgebra `L` of maximal dimension is a field and its own centralizer, so the
dimension count for the centralizer of a subfield reads `(finrank K L)² = finrank K D`; the degree
is the square root of `finrank K D`, so `finrank K L = deg K D`.

Together with `TauCeti.Algebra.finrank_le_deg`, which bounds the degree of *every* subfield by
`deg K D`, this says `L` is a maximal subfield in the literal sense as well. -/
theorem exists_subalgebra_isField_finrank_eq_deg :
    ∃ L : Subalgebra K D, IsField ↥L ∧ finrank K ↥L = deg K D := by
  obtain ⟨L, hL, hmax⟩ := exists_isMulCommutative_forall_finrank_le K D
  refine ⟨L, isField_of_isMulCommutative L, ?_⟩
  -- The centralizer of `L` is `L` itself, so the dimension count becomes a square identity.
  have hcent := finrank_mul_finrank_centralizer_of_isField L (isField_of_isMulCommutative L)
  rw [centralizer_eq_self_of_forall_finrank_le hmax] at hcent
  have hsq : finrank K ↥L ^ 2 = deg K D ^ 2 := by rw [sq, hcent, deg_sq]
  exact Nat.pow_left_injective (by norm_num) hsq

/-- **A central division algebra is split by a subfield of degree `deg K D`.**

This is the maximal-subfield route to a splitting field: unlike the passage to an algebraic
closure (`TauCeti.Algebra.isSplittingField_of_isAlgClosed`), it produces a splitting field that is
a *finite* extension of `K`, and one realized inside `D` by the accompanying homomorphism. -/
theorem exists_isSplittingField_finrank_eq_deg :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : L →ₐ[K] D),
      FiniteDimensional K L ∧ finrank K L = deg K D ∧ IsSplittingField K D L := by
  obtain ⟨L, hL, hdeg⟩ := exists_subalgebra_isField_finrank_eq_deg K D
  let _ : Field ↥L := hL.toField
  exact ⟨↥L, inferInstance, inferInstance, L.val,
    FiniteDimensional.of_injective L.val.toLinearMap Subtype.val_injective, hdeg,
    isSplittingField_of_finrank_eq_deg L.val hdeg⟩

end Algebra

/-! ### Worked example: a maximal subfield of the real quaternions -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- **The real quaternions have a subfield of degree `2`.** The general theorem produces one
without exhibiting a copy of `ℂ` by hand. Which subfield it is takes the classification of the
finite extensions of `ℝ`, not proved here, to say: every degree-`2` extension of `ℝ` is
`ℝ`-isomorphic to `ℂ`. The example in `TauCeti/Algebra/CentralSimple/Subfield.lean` exhibits a
copy of `ℂ` inside `ℍ[ℝ]` by hand instead. -/
example : ∃ L : Subalgebra ℝ ℍ[ℝ], IsField ↥L ∧ Module.finrank ℝ ↥L = 2 := by
  have hdeg : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  exact hdeg ▸ Algebra.exists_subalgebra_isField_finrank_eq_deg ℝ ℍ[ℝ]

/-- **A subfield of `ℍ[ℝ]` of degree `2` is not the base field**, so the maximal subfield of a
central division algebra genuinely enlarges the centre; the existence theorem is not answered by
`K` itself. -/
example (L : Subalgebra ℝ ℍ[ℝ]) (h : Module.finrank ℝ ↥L = 2) : L ≠ ⊥ := by
  rintro rfl
  rw [Subalgebra.finrank_bot] at h
  omega

end Examples

end TauCeti
