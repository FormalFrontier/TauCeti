/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Integrality
public import TauCeti.Algebra.Lie.Weights.Sl2System

/-!
# The integral span of root vectors and coroots

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form, let `H` be a
splitting Cartan subalgebra, and let `x` be a normalized system of root vectors. This file defines
the `ℤ`-span in `L` of the root vectors `x α` and the coroots `α∨`.

The only bracket coefficients not already known to be integers are those between two root
vectors. If these coefficients are integral, `IsSl2System.lie_mem_rootCorootSpan` proves that the
span is closed under the Lie bracket and `IsSl2System.rootCorootLieSubalgebra` packages it as a Lie
subalgebra over `ℤ`. The other three generator pairs need no hypothesis:

* the bracket of opposite root vectors is a coroot by the normalization of `x`;
* a coroot acts on a root vector through the integral Cartan number `TauCeti.rootCartanWeight`;
* two coroots commute because a splitting Cartan subalgebra in a Killing-semisimple Lie algebra is
  abelian.

For a Chevalley-normalized system the remaining coefficients are `±(p + 1)`, so the resulting
`rootCorootLieSubalgebra` is the integral Chevalley form of `L`. This is the Lie-algebra input to
the Kostant `ℤ`-form used in the explicit Chevalley--Demazure construction of Layer 9 of the
ReductiveGroups roadmap, which is in turn consumed by CFSGStatement milestone L0.

## Main definitions and results

* `TauCeti.rootCorootGenerators`: the root vectors and coroots as a set in `L`.
* `TauCeti.mem_rootCorootGenerators_iff`: characteristic membership in the generator set.
* `TauCeti.rootCorootSpan`: their span over `ℤ`.
* `TauCeti.corootFamily`: the coroots as a family indexed by the weights of `L`.
* `TauCeti.rootCartanWeight`: the Cartan integers `β α∨` as a `ℤ`-valued weight of `β`.
* `TauCeti.lie_coroot_coroot_eq_zero` and `TauCeti.IsSl2System.lie_coroot_rootVector`: the two
  bracket computations against a coroot, in their integral form.
* `TauCeti.IsSl2System.lie_mem_rootCorootSpan`: closure under the bracket when the root-vector
  coefficients are integral.
* `TauCeti.IsSl2System.rootCorootLieSubalgebra`: the resulting integral Lie subalgebra.
* `TauCeti.IsSl2System.mem_rootCorootLieSubalgebra_iff`: membership in the Lie subalgebra.
* `TauCeti.IsSl2System.rootCorootLieSubalgebra_le_iff`: the universal property of the Lie
  subalgebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- The set consisting of a weight-indexed family `x` and all coroots, regarded as elements of the
ambient Lie algebra. When `x` is a normalized system (such as `IsSl2System x`), its zero-weight
value vanishes alongside the zero coroot. -/
def rootCorootGenerators (x : Weight K H L → L) : Set L :=
  Set.range x ∪ Set.range fun α : Weight K H L => (coroot α : L)

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- Membership in the set of root--coroot generators. -/
@[simp]
theorem mem_rootCorootGenerators_iff {x : Weight K H L → L} {v : L} :
    v ∈ rootCorootGenerators x ↔
      (∃ α, x α = v) ∨ ∃ α, (IsKilling.coroot (K := K) (L := L) (H := H) α : L) = v := by
  rw [rootCorootGenerators, Set.mem_union, Set.mem_range, Set.mem_range]

/-- The integral span of a weight-indexed family `x` and all coroots in the ambient Lie algebra. -/
def rootCorootSpan (x : Weight K H L → L) : Submodule ℤ L :=
  Submodule.span ℤ (rootCorootGenerators x)

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- A root vector belongs to its root--coroot span. -/
@[simp]
theorem rootVector_mem_rootCorootSpan (x : Weight K H L → L) (α : Weight K H L) :
    x α ∈ rootCorootSpan x :=
  Submodule.subset_span (Or.inl (Set.mem_range_self α))

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- A coroot belongs to every root--coroot span. -/
@[simp]
theorem coroot_mem_rootCorootSpan (x : Weight K H L → L) (α : Weight K H L) :
    (coroot α : L) ∈ rootCorootSpan x :=
  Submodule.subset_span (Or.inr (Set.mem_range_self α))

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- The universal property of the integral root--coroot span. -/
@[simp]
theorem rootCorootSpan_le_iff {x : Weight K H L → L} {P : Submodule ℤ L} :
    rootCorootSpan x ≤ P ↔
      (∀ α, x α ∈ P) ∧
        ∀ α, (IsKilling.coroot (K := K) (L := L) (H := H) α : L) ∈ P := by
  rw [rootCorootSpan, Submodule.span_le, rootCorootGenerators, Set.union_subset_iff,
    Set.range_subset_iff, Set.range_subset_iff]
  rfl

/-! ## The coroot family and its Cartan integers -/

variable (H) in
/-- The coroots of `L`, as a family indexed by the **weights** of `L`. The index runs over all
weights and not only the roots: the zero weight has `coroot 0 = 0` and so contributes nothing to
any span or product taken over this family.

This is the family of distinguished Cartan vectors of `TauCeti.chevalleyKostantForm`. -/
noncomputable def corootFamily : Weight K H L → L := fun α => (coroot α : L)

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- The coroot family evaluates to the coroot of the weight indexing it. -/
@[simp] theorem corootFamily_apply (α : Weight K H L) :
    corootFamily H α = ((coroot α : H) : L) := (rfl)

/-- The Cartan integers `β α∨` collected as the integral weight of the root `β` against the family
of all coroots, written through the root-chain coefficients that
`LieAlgebra.IsKilling.apply_coroot_eq_cast` uses to exhibit that pairing as an integer.

Like `TauCeti.corootFamily`, this is indexed by all weights: at the zero weight the coroot is zero
and the value is `0`. -/
noncomputable def rootCartanWeight (β : Weight K H L) : Weight K H L → ℤ :=
  fun α => (chainBotCoeff (α : H → K) β : ℤ) - (chainTopCoeff (α : H → K) β : ℤ)

/-- The defining property of `TauCeti.rootCartanWeight`: it is the Cartan integer `β α∨`, read in
`K`. -/
@[simp] theorem intCast_rootCartanWeight (α β : Weight K H L) :
    ((rootCartanWeight β α : ℤ) : K) = β (coroot α) := by
  rw [rootCartanWeight, apply_coroot_eq_cast α β]

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- **Two coroots commute**: a splitting Cartan subalgebra of a Killing-semisimple Lie algebra is
abelian. -/
theorem lie_coroot_coroot_eq_zero (α β : Weight K H L) :
    ⁅(coroot α : L), (coroot β : L)⁆ = 0 := by
  have h := trivial_lie_zero H H (coroot α) (coroot β)
  simpa only [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using congrArg Subtype.val h

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

include hx

omit [CharZero K] in
/-- If every bracket of root vectors whose weights sum to a root has an integral coefficient, then
the bracket of any two root-vector generators belongs to the integral root--coroot span.

The cases in which one weight is zero, the sum is zero, or the sum is not a root are discharged by
the normalized-system API; only the genuine root-sum case uses `hIntegral`. -/
theorem lie_rootVector_rootVector_mem_rootCorootSpan
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    (α β : Weight K H L) : ⁅x α, x β⁆ ∈ rootCorootSpan x := by
  by_cases hα : α.IsNonZero
  · by_cases hβ : β.IsNonZero
    · by_cases hsum : (α : H → K) + (β : H → K) = 0
      · have hβα : β = -α := by
          apply Weight.ext
          intro h
          have h := congrFun (add_eq_zero_iff_neg_eq.mp hsum) h
          simpa using h.symm
        rw [hβα, hx.lie_neg α hα]
        exact coroot_mem_rootCorootSpan x α
      · by_cases hroot : rootSpace H ((α : H → K) + β) = ⊥
        · rw [hx.lie_eq_zero_of_rootSpace_add_eq_bot α β hroot]
          exact Submodule.zero_mem _
        · let γ : Weight K H L := ⟨(α : H → K) + β, hroot⟩
          have hγ : γ.IsNonZero := hsum
          obtain ⟨z, hz⟩ := hIntegral α β γ hα hβ hγ rfl
          rw [hz, Int.cast_smul_eq_zsmul]
          exact Submodule.smul_mem _ z (rootVector_mem_rootCorootSpan x γ)
    · rw [hx.eq_zero_of_isZero β (not_not.mp hβ), lie_zero]
      exact Submodule.zero_mem _
  · rw [hx.eq_zero_of_isZero α (not_not.mp hα), zero_lie]
    exact Submodule.zero_mem _

/-- **A coroot acts on a root vector through a Cartan integer.** This is the Cartan relation
`TauCeti.IsSl2System.lie_coroot` with its coefficient in the integral form
`TauCeti.rootCartanWeight`. -/
theorem lie_coroot_rootVector (α β : Weight K H L) :
    ⁅(coroot α : L), x β⁆ = ((rootCartanWeight β α : ℤ) : K) • x β := by
  rw [hx.lie_coroot β α, intCast_rootCartanWeight]

/-- The bracket of a coroot with a root vector belongs to the integral root--coroot span. Its
coefficient is the corresponding integral Cartan number. -/
theorem lie_coroot_rootVector_mem_rootCorootSpan (α β : Weight K H L) :
    ⁅(coroot α : L), x β⁆ ∈ rootCorootSpan x := by
  rw [hx.lie_coroot_rootVector α β, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (rootVector_mem_rootCorootSpan x β)

/-- The bracket of a root vector with a coroot belongs to the integral root--coroot span. -/
theorem lie_rootVector_coroot_mem_rootCorootSpan (α β : Weight K H L) :
    ⁅x α, (coroot β : L)⁆ ∈ rootCorootSpan x := by
  rw [← lie_skew]
  exact Submodule.neg_mem _ (hx.lie_coroot_rootVector_mem_rootCorootSpan β α)

omit [CharZero K] [LieModule.IsTriangularizable K H L] hx in
/-- Two coroots have zero bracket, hence their bracket belongs to the integral root--coroot span. -/
theorem lie_coroot_coroot_mem_rootCorootSpan (α β : Weight K H L) :
    ⁅(coroot α : L), (coroot β : L)⁆ ∈ rootCorootSpan x := by
  rw [lie_coroot_coroot_eq_zero]
  exact Submodule.zero_mem _

/-- **The integral root--coroot span is closed under the Lie bracket** when all root-vector
structure constants are integers. -/
theorem lie_mem_rootCorootSpan
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    {a b : L} (ha : a ∈ rootCorootSpan x) (hb : b ∈ rootCorootSpan x) :
    ⁅a, b⁆ ∈ rootCorootSpan x := by
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem _ _ ha hb =>
      rcases ha with ⟨α, rfl⟩ | ⟨α, rfl⟩
      · rcases hb with ⟨β, rfl⟩ | ⟨β, rfl⟩
        · exact hx.lie_rootVector_rootVector_mem_rootCorootSpan hIntegral α β
        · exact hx.lie_rootVector_coroot_mem_rootCorootSpan α β
      · rcases hb with ⟨β, rfl⟩ | ⟨β, rfl⟩
        · exact hx.lie_coroot_rootVector_mem_rootCorootSpan α β
        · exact lie_coroot_coroot_mem_rootCorootSpan (x := x) α β
  | zero_left => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left _ _ _ _ _ _ h₁ h₂ => rw [add_lie]; exact Submodule.add_mem _ h₁ h₂
  | add_right _ _ _ _ _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
  | smul_left z _ _ _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ z h
  | smul_right z _ _ _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ z h

/-- The integral Lie subalgebra spanned by a normalized root-vector system and the coroots, under
the hypothesis that every root-vector structure constant is integral. For a
Chevalley-normalized system this is the Chevalley `ℤ`-form of the ambient Lie algebra. -/
noncomputable def rootCorootLieSubalgebra
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ) : LieSubalgebra ℤ L :=
  { rootCorootSpan x with lie_mem' := hx.lie_mem_rootCorootSpan hIntegral }

/-- The underlying integer submodule of `rootCorootLieSubalgebra` is the root--coroot span. -/
@[simp]
theorem rootCorootLieSubalgebra_toSubmodule
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ) :
    (hx.rootCorootLieSubalgebra hIntegral).toSubmodule = rootCorootSpan x :=
  (rfl)

/-- Membership in `rootCorootLieSubalgebra` coincides with membership in `rootCorootSpan`. -/
@[simp]
theorem mem_rootCorootLieSubalgebra_iff
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    {v : L} :
    v ∈ hx.rootCorootLieSubalgebra hIntegral ↔ v ∈ rootCorootSpan x :=
  Iff.rfl

/-- The universal property of `rootCorootLieSubalgebra`: it is the least Lie subalgebra containing
the root vectors and coroots. -/
@[simp]
theorem rootCorootLieSubalgebra_le_iff
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    {M : LieSubalgebra ℤ L} :
    hx.rootCorootLieSubalgebra hIntegral ≤ M ↔
      (∀ α, x α ∈ M) ∧ ∀ α, (IsKilling.coroot (K := K) (L := L) (H := H) α : L) ∈ M := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, rootCorootLieSubalgebra_toSubmodule,
    rootCorootSpan_le_iff]
  simp_rw [LieSubalgebra.mem_toSubmodule]

/-- A root vector belongs to the integral root--coroot Lie subalgebra. -/
theorem rootVector_mem_rootCorootLieSubalgebra
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    (α : Weight K H L) :
    x α ∈ hx.rootCorootLieSubalgebra hIntegral :=
  rootVector_mem_rootCorootSpan x α

/-- A coroot belongs to the integral root--coroot Lie subalgebra. -/
theorem coroot_mem_rootCorootLieSubalgebra
    (hIntegral : ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → γ.IsNonZero →
      (γ : H → K) = (α : H → K) + (β : H → K) →
        ∃ z : ℤ, ⁅x α, x β⁆ = (z : K) • x γ)
    (α : Weight K H L) :
    (coroot α : L) ∈ hx.rootCorootLieSubalgebra hIntegral :=
  coroot_mem_rootCorootSpan x α

end IsSl2System

end TauCeti
