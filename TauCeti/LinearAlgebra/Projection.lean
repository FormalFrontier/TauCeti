/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# Projections onto the summands of an internal direct sum

Mathlib's `Submodule.projectionOnto` projects a module onto one of two complementary submodules.
A family `Q` of submodules that is `iSupIndep` and spans the whole module presents each `Q i` as
complementary to the supremum of the other summands, so each summand inherits such a projection.

This file records that complement, `TauCeti.isCompl_biSup_ne`, and the projections it produces,
`TauCeti.internalProjection`. Their pointwise behaviour and kernel are Mathlib's lemmas about
`Submodule.projectionOnto`, restated for the specialization. The one fact that goes beyond a
single projection is that over a finite index type the projections sum to the identity,
`TauCeti.sum_coe_internalProjection`.

## Main definitions

* `TauCeti.internalProjection`: the projection of `M` onto the summand `Q i` of an internal direct
  sum decomposition, as a linear map `M →ₗ[A] Q i`.

## Main results

* `TauCeti.isCompl_biSup_ne`: a summand of an internal direct sum decomposition is complementary to
  the supremum of the other summands.
* `TauCeti.internalProjection_surjective`: the projection onto `Q i` is surjective.
* `TauCeti.ker_internalProjection`: the kernel of the projection onto `Q i` is the supremum of the
  other summands.
* `TauCeti.sum_coe_internalProjection`: over a finite index type the projections onto the summands
  sum to the identity.

## Implementation notes

The decomposition is spelled as `iSupIndep Q` together with `⨆ i, Q i = ⊤` rather than as
`DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on the index type that nothing
here needs; `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` converts between the two.
-/

public section

namespace TauCeti

universe u v w

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
variable {ι : Type w} {Q : ι → Submodule A M}

/-- A summand of an internal direct sum decomposition is complementary to the supremum of the other
summands: independence gives disjointness, and spanning gives codisjointness. -/
theorem isCompl_biSup_ne (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    IsCompl (Q i) (⨆ j, ⨆ (_ : j ≠ i), Q j) :=
  ⟨hQi i, codisjoint_iff.mpr (by rw [← hQt]; exact (iSup_split_single Q i).symm)⟩

/-- The projection of `M` onto the summand `Q i` of an internal direct sum decomposition, along the
supremum of the other summands. -/
noncomputable def internalProjection (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    M →ₗ[A] Q i :=
  (Q i).projectionOnto _ (isCompl_biSup_ne hQi hQt i)

/-- The projection onto `Q i` fixes the elements of `Q i`. -/
theorem internalProjection_apply_of_mem (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i : ι} {x : M}
    (hx : x ∈ Q i) : internalProjection hQi hQt i x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

/-- The projection onto `Q i` restricts to the identity on `Q i`. -/
@[simp]
theorem internalProjection_apply (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i : ι} (x : Q i) :
    internalProjection hQi hQt i (x : M) = x :=
  Submodule.projectionOnto_apply_left _ x

/-- The projection onto `Q j` kills the elements of any other summand `Q i`. -/
theorem internalProjection_apply_eq_zero_of_mem_of_ne (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ Q i) : internalProjection hQi hQt j x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _
    (le_iSup₂ (f := fun k (_ : k ≠ j) ↦ Q k) i hij hx)

/-- The projection onto `Q j` restricts to `0` on any other summand `Q i`.

This is the form `simp` can use: the summand index `i` is read off the type of `x`, whereas in
`TauCeti.internalProjection_apply_eq_zero_of_mem_of_ne` it appears only in the hypotheses. -/
@[simp]
theorem internalProjection_apply_of_ne (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) {i j : ι}
    (hij : i ≠ j) (x : Q i) : internalProjection hQi hQt j (x : M) = 0 :=
  internalProjection_apply_eq_zero_of_mem_of_ne hQi hQt hij x.2

/-- The projection onto `Q i` is surjective, being the identity on `Q i`. -/
theorem internalProjection_surjective (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    Function.Surjective (internalProjection hQi hQt i) :=
  Submodule.projectionOnto_surjective (isCompl_biSup_ne hQi hQt i)

/-- The kernel of the projection onto `Q i` is the supremum of the other summands. -/
@[simp]
theorem ker_internalProjection (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (i : ι) :
    LinearMap.ker (internalProjection hQi hQt i) = ⨆ j, ⨆ (_ : j ≠ i), Q j :=
  Submodule.ker_projectionOnto _

/-- Over a finite index type the projections onto the summands sum to the identity.

The sum of the projections is a linear map agreeing with the identity on each summand, and the
summands span `M`. -/
theorem sum_coe_internalProjection [Fintype ι] (hQi : iSupIndep Q) (hQt : ⨆ i, Q i = ⊤) (x : M) :
    ∑ i, ((internalProjection hQi hQt i x : M)) = x := by
  have hker : ∀ k : ι, Q k ≤ LinearMap.ker
      ((∑ i, (Q i).subtype ∘ₗ internalProjection hQi hQt i) - LinearMap.id) := by
    intro k y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k), sub_eq_zero]
    · simp [internalProjection_apply_of_mem hQi hQt hy]
    · intro j _ hjk
      simp [internalProjection_apply_eq_zero_of_mem_of_ne hQi hQt (Ne.symm hjk) hy]
  have htop : (⊤ : Submodule A M) ≤ LinearMap.ker
      ((∑ i, (Q i).subtype ∘ₗ internalProjection hQi hQt i) - LinearMap.id) := by
    rw [← hQt]
    exact iSup_le hker
  have hx := htop (Submodule.mem_top (x := x))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    sub_eq_zero] at hx
  simpa using hx

end TauCeti
