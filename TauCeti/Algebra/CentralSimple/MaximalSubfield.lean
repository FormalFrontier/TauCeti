/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.CentralSimple.Subfield` is imported publicly: `TauCeti.Algebra.deg` and
-- `TauCeti.Algebra.IsSplittingField` occur in the statements below, and
-- `TauCeti.Algebra.isSplittingField_of_finrank_eq_deg` is the theorem the summit of this file
-- feeds. It re-exports `TauCeti.Algebra.CentralSimple.Splitting` and, through it, the degree API,
-- as well as `Subalgebra` and `IsField.of_isDomain_of_finite`, which turns a commutative subalgebra
-- into a subfield.
public import TauCeti.Algebra.CentralSimple.Subfield
-- Non-public: none of these appears in the type of an exported declaration. A commutative
-- subalgebra of maximal dimension and the fact that it is its own centralizer come from the
-- subalgebra file, the dimension of the centralizer of a subfield from the centralizer file, and
-- the real quaternions and their centrality appear only in the worked examples.
import Mathlib.Data.Real.Basic
import TauCeti.Algebra.Algebra.Subalgebra.MaximalCommutative
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.Centralizer

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
dimension (`TauCeti.exists_isMulCommutative_forall_finrank_le`, in
`TauCeti/Algebra/Algebra/Subalgebra/MaximalCommutative.lean`). Nothing about `D` is used here
beyond finite-dimensionality.

*It is its own centralizer.* If `x` centralizes `L` then `L` and `x` together generate a
commutative subalgebra `Algebra.adjoin K (insert x L)`, which contains `L`; maximal dimension makes
the containment an equality, so `x ∈ L`. This is
`TauCeti.centralizer_eq_self_of_forall_finrank_le`, in the same file, and it is also what makes `L`
a *maximal* subfield rather than merely a large one.

Being a commutative domain, finite-dimensional over `K`, `L` is then a field
(`IsField.of_isDomain_of_finite`).

*Its dimension is forced.* For any subfield `L` of a finite-dimensional central simple algebra `A`,

  `finrank K L * finrank K C_A(L) = finrank K A`

(`TauCeti.finrank_mul_finrank_centralizer_of_isField`, in
`TauCeti/Algebra/CentralSimple/Centralizer.lean`). Applied to `C_D(L) = L` this reads
`(finrank K L)² = finrank K D = (deg K D)²`, so `finrank K L = deg K D`.

## Main results

* `TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`: **a central division algebra has a
  subfield of degree `deg K D`.**
* `TauCeti.Algebra.exists_isSplittingField_finrank_eq_deg`: **a central division algebra is split
  by a subfield of degree `deg K D`.**

## Implementation notes

Commutativity of a subalgebra is Mathlib's `IsMulCommutative` on its coercion to a type, which is
what `Algebra.isMulCommutative_adjoin` produces and what the scoped instances of the
`IsMulCommutative` namespace turn into a `CommRing` structure; the file therefore opens that scope,
which is what lets `IsField.of_isDomain_of_finite` apply to a commutative subalgebra of `D`.

The two ingredients that use nothing of the central simple theory are stated where they belong and
consumed here: the existence of a commutative subalgebra of maximal dimension and its being its own
centralizer in `TauCeti/Algebra/Algebra/Subalgebra/MaximalCommutative.lean`, the dimension of the
centralizer of a subfield beside the centralizer theorem it specializes in
`TauCeti/Algebra/CentralSimple/Centralizer.lean`.

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

/-! ### A maximal subfield of a central division algebra -/

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
  -- A commutative subalgebra of `D` is a domain, and one finite over `K` is therefore a field.
  have hfield : IsField ↥L := IsField.of_isDomain_of_finite K ↥L
  refine ⟨L, hfield, ?_⟩
  -- The centralizer of `L` is `L` itself, so the dimension count becomes a square identity.
  have hcent := finrank_mul_finrank_centralizer_of_isField L hfield
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

/-- **A subalgebra of `ℍ[ℝ]` of degree `2` is not the base field**, so when `deg K D > 1` the
subfield produced above genuinely enlarges the centre; the existence theorem is not answered by
`K` itself. -/
example (L : Subalgebra ℝ ℍ[ℝ]) (h : Module.finrank ℝ ↥L = 2) : L ≠ ⊥ := by
  rintro rfl
  rw [Subalgebra.finrank_bot] at h
  omega

end Examples

end TauCeti
