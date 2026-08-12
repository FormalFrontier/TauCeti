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
-- Non-public: none of these appears in the type of an exported declaration. The Artinian criterion
-- for a domain to be a field, and the simplicity of a field, turn a maximal commutative subalgebra
-- into a subfield; the real quaternions and their centrality appear only in the worked examples.
-- The lattice of subalgebras, with `Algebra.adjoin` and the commutativity of an adjunction of
-- pairwise commuting elements, and the finite-dimensional comparison of nested subalgebras come
-- with the `Centralizer` import above and are not imported again.
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleRing.Field
import TauCeti.Algebra.Central.Quaternion

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

That last statement is `TauCeti.finrank_mul_finrank_centralizer` with the centrality hypothesis
moved from the subalgebra to the ambient algebra, and the count itself is not repeated: both are
instances of `TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct`, which asks
only that `L ⊗[K] Aᵐᵒᵖ` be simple. That follows from `L` being simple and `Aᵐᵒᵖ` central simple just
as well as from `L` being central simple and `Aᵐᵒᵖ` simple; a subfield is simple but not central, so
it is the first reading that applies here.

## Main results

* `TauCeti.exists_isMulCommutative_forall_finrank_le`: a finite-dimensional algebra has a
  commutative subalgebra of maximal dimension.
* `TauCeti.centralizer_eq_self_of_forall_finrank_le`: such a subalgebra is its own centralizer.
* `TauCeti.isField_of_isMulCommutative`: a commutative subalgebra of a domain, finite over the base
  field, is a field.
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
`IsSimpleRing ↥L`, which is all its proof uses. The restriction is a scope boundary and not a
mathematical one: stated for a merely simple subalgebra, this is the general centralizer theorem for
a non-central simple subalgebra, which the Layer 5 bullet of the roadmap referenced below defers —
"the general form for a merely simple subalgebra `B` (center `Z(B) ⊋ K`) ... is a **later** target,
not this one" — to be taken up together with the description of the centralizer's centre. Only the
subfield case, which is what the maximal-subfield theory needs, is claimed here.

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

open scoped IsMulCommutative

universe u

/-! ### Commutative subalgebras of maximal dimension -/

section Maximal

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- **A finite-dimensional algebra has a commutative subalgebra of maximal dimension.**

Maximality is in dimension over `K` and is stated as a bound on every commutative subalgebra of
`A`, not as maximality for inclusion.

No hypothesis beyond finite-dimensionality is needed; it is in a division algebra that such a
subalgebra becomes interesting
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`). -/
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

variable {K A}

/-- **A commutative subalgebra of maximal dimension is its own centralizer.**

Maximality enters as the hypothesis `hmax`, the dimension bound over all commutative subalgebras
of `A` that `TauCeti.exists_isMulCommutative_forall_finrank_le` produces.

Nothing beyond finite-dimensionality is asked of `A`; it is in a division algebra that the
conclusion becomes the maximality of a subfield
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`). -/
theorem centralizer_eq_self_of_forall_finrank_le {L : Subalgebra K A} [IsMulCommutative ↥L]
    (hmax : ∀ M : Subalgebra K A, IsMulCommutative ↥M → finrank K ↥M ≤ finrank K ↥L) :
    Subalgebra.centralizer K (L : Set A) = L := by
  refine le_antisymm (fun x hx ↦ ?_) (fun y hy z hz ↦ ?_)
  · -- The elements of `insert x L` commute pairwise.
    have hcomm : ∀ a ∈ insert x (L : Set A), ∀ b ∈ insert x (L : Set A), a * b = b * a := by
      rintro a (rfl | ha) b (rfl | hb)
      · rfl
      · exact ((Subalgebra.mem_centralizer_iff K).1 hx b hb).symm
      · exact (Subalgebra.mem_centralizer_iff K).1 hx a ha
      · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥L) ⟨b, hb⟩)
    have hM : IsMulCommutative ↥(Algebra.adjoin K (insert x (L : Set A))) :=
      Algebra.isMulCommutative_adjoin K hcomm
    have hsub : L ≤ Algebra.adjoin K (insert x (L : Set A)) := fun a ha ↦
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)
    have := Subalgebra.eq_of_le_of_finrank_le hsub (hmax _ hM)
    exact this ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  · exact congrArg Subtype.val (mul_comm (⟨z, hz⟩ : ↥L) ⟨y, hy⟩)

end Maximal

/-! ### Commutative subalgebras of a domain -/

section Domain

variable {K D : Type*} [Field K] [Ring D] [IsDomain D] [Algebra K D]

/-- **A commutative subalgebra of a domain is a field**, as soon as it is finite-dimensional over
the base field. Only `L` need be finite-dimensional; the ambient `D` need not be, and a division
ring is more than is asked of it. -/
theorem isField_of_isMulCommutative (L : Subalgebra K D) [IsMulCommutative ↥L]
    [FiniteDimensional K ↥L] : IsField ↥L := by
  have : IsArtinianRing ↥L := IsArtinianRing.of_finite K ↥L
  exact IsArtinianRing.isField_of_isDomain ↥L

end Domain

/-! ### The centralizer of a subfield -/

section Centralizer

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **The dimension of the centralizer of a subfield of a central simple algebra is the
complementary one**:

  `finrank K L * finrank K C_A(L) = finrank K A`.

This is `TauCeti.finrank_mul_finrank_centralizer` with the centrality hypothesis moved from the
subalgebra to the ambient algebra. The shared dimension count is
`TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct`, whose one hypothesis —
that `L ⊗[K] Aᵐᵒᵖ` be simple — `TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right` supplies here
from the simplicity of the field `L` and the central simplicity of `Aᵐᵒᵖ`; `L` itself is not central
over `K` unless it is `K`, so the orientation used by `TauCeti.finrank_mul_finrank_centralizer` does
not apply. -/
theorem finrank_mul_finrank_centralizer_of_isField (L : Subalgebra K A) (hL : IsField ↥L) :
    finrank K ↥L * finrank K ↥(Subalgebra.centralizer K (L : Set A)) = finrank K A := by
  have : IsMulCommutative ↥L := ⟨⟨hL.mul_comm⟩⟩
  have : IsSimpleRing ↥L := (isSimpleRing_iff_isField ↥L).2 hL
  exact finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct L

end Centralizer

/-! ### The maximal subfield of a central division algebra -/

namespace Algebra

variable (K : Type*) [Field K] (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D]

/-- **A central division algebra has a subfield of degree `deg K D`.**

The subfield is delivered as a `Subalgebra K D` carrying `IsField`;
`TauCeti.Algebra.exists_isSplittingField_finrank_eq_deg` is the same subfield packaged as a field
in its own right, together with its embedding in `D`.

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
