/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Sheaf
import Mathlib.Tactic.Abel

/-!
# Locally principal Weil divisors on a scheme

Let `X` be a locally Noetherian integral scheme. A Weil divisor `D` on `X` is locally principal when
every point has an open neighbourhood on which the coefficients of `D` agree with the orders of one
nonzero rational function. On a scheme regular in codimension one (expressed in
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean` by the codimension-one stalks being
discrete valuation rings), this is the local condition used to compare Weil divisors with the
Cartier divisors defined in `TauCeti/AlgebraicGeometry/CartierDivisor/Basic.lean`.

The predicate and its additive subgroup require only `IsLocallyNoetherian X`. Results involving
the globally assembled principal Weil divisors and linear equivalence require `IsNoetherian X`,
which supplies the finite-support condition for `orderAt`. The local triviality of `𝒪_X(D)`
additionally requires the codimension-one stalks to be discrete valuation rings, which is the
hypothesis under which that sheaf is built.

## Main declarations

* `SchemeWeilDivisor.IsLocallyPrincipal D` is the local-principality predicate;
* `SchemeWeilDivisor.locallyPrincipalSubgroup X` is the subgroup of locally principal Weil
  divisors;
* `SchemeWeilDivisor.principalSubgroup_le_locallyPrincipalSubgroup` records that principal
  divisors are locally principal;
* `WeilDivisor.OrderSystem.LinearlyEquivalent.isLocallyPrincipal_iff` shows that local
  principality depends only on the divisor class;
* `SchemeWeilDivisor.IsLocallyPrincipal.exists_sections_sub_principalDivisor_eq_sections_zero`
  and `SchemeWeilDivisor.IsLocallyPrincipal.exists_iso_sheaf_sections_eq_sections_zero` consume
  the predicate: the sheaf `𝒪_X(D)` of
  `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean` is isomorphic, near every point, to
  the sheaf of a divisor whose sections there are those of `𝒪_X(0)`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, target "Divisors on a curve:
Weil divisors and Cartier divisors; the dictionaries `Cartier ≃ line bundles` and (smooth curve)
`Weil ≃ Cartier`". It isolates the exact local condition needed next: the construction of
`𝒪_X(D)` can prove invertibility by reducing on a trivializing cover to the already constructed
principal-divisor multiplication isomorphism, while the smooth-curve comparison must prove that
every Weil divisor satisfies this predicate.

The local-equation formulation follows Hartshorne, *Algebraic Geometry*, II.6. The Stacks
Project, *Divisors*, Tags 0BE0 and 0BE9, supplies the principal-Weil-divisor and Picard/class-group
comparison context. No formalization is vendored. The proofs reuse Tau Ceti's scheme-theoretic
principal-divisor and linear-equivalence API.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

section LocallyNoetherian

variable [IsLocallyNoetherian X]

/-- A Weil divisor on a locally Noetherian integral scheme is locally principal if every point
has an open neighbourhood on which its coefficients agree with a principal divisor.

The local equation is allowed to vary with the point. It is a nonzero rational function, encoded
as an element of the additive group `Additive X.functionFieldˣ`. -/
def IsLocallyPrincipal (D : SchemeWeilDivisor X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ g : Additive X.functionFieldˣ,
    ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff D y = orderAt y g

/-- The defining characterization of local principality: every point of `X` has an open
neighbourhood on which the coefficients of `D` are the orders of a single nonzero rational
function.

This is the convenient introduction and elimination rule for `IsLocallyPrincipal`. -/
lemma isLocallyPrincipal_iff {D : SchemeWeilDivisor X} :
    IsLocallyPrincipal D ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ g : Additive X.functionFieldˣ,
      ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
        WeilDivisor.coeff D y = orderAt y g :=
  (Iff.rfl)

/-- A Weil divisor whose coefficients globally equal the orders of one rational function is
locally principal. -/
lemma isLocallyPrincipal_of_forall_coeff_eq {D : SchemeWeilDivisor X}
    (g : Additive X.functionFieldˣ)
    (h : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff D y = orderAt y g) :
    IsLocallyPrincipal D := by
  intro x
  exact ⟨⊤, Opens.mem_top x, g, fun y _ ↦ h y⟩

/-- The zero Weil divisor is locally principal. -/
@[simp]
lemma isLocallyPrincipal_zero : IsLocallyPrincipal (0 : SchemeWeilDivisor X) := by
  apply isLocallyPrincipal_of_forall_coeff_eq 0
  intro y
  rw [WeilDivisor.coeff_zero, map_zero]

namespace IsLocallyPrincipal

variable {D E : SchemeWeilDivisor X}

/-- The sum of two locally principal Weil divisors is locally principal. Local equations add on
the intersection of their neighbourhoods. -/
lemma add (hD : IsLocallyPrincipal D) (hE : IsLocallyPrincipal E) :
    IsLocallyPrincipal (D + E) := by
  intro x
  obtain ⟨U, hxU, g, hg⟩ := hD x
  obtain ⟨V, hxV, h, hh⟩ := hE x
  refine ⟨U ⊓ V, Opens.mem_inf.mpr ⟨hxU, hxV⟩, g + h, ?_⟩
  intro y hy
  obtain ⟨hyU, hyV⟩ := Opens.mem_inf.mp hy
  rw [WeilDivisor.coeff_add, hg y hyU, hh y hyV, map_add]

/-- The negation of a locally principal Weil divisor is locally principal. -/
lemma neg (hD : IsLocallyPrincipal D) : IsLocallyPrincipal (-D) := by
  intro x
  obtain ⟨U, hxU, g, hg⟩ := hD x
  refine ⟨U, hxU, -g, ?_⟩
  intro y hy
  rw [WeilDivisor.coeff_neg, hg y hy, map_neg]

/-- The difference of two locally principal Weil divisors is locally principal. -/
lemma sub (hD : IsLocallyPrincipal D) (hE : IsLocallyPrincipal E) :
    IsLocallyPrincipal (D - E) := by
  rw [sub_eq_add_neg]
  exact hD.add hE.neg

end IsLocallyPrincipal

/-- A Weil divisor is locally principal exactly when its negation is. -/
@[simp]
lemma isLocallyPrincipal_neg {D : SchemeWeilDivisor X} :
    IsLocallyPrincipal (-D) ↔ IsLocallyPrincipal D :=
  ⟨fun hD ↦ by simpa using hD.neg, IsLocallyPrincipal.neg⟩

/-- The additive subgroup of locally principal Weil divisors on `X`. -/
def locallyPrincipalSubgroup (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    AddSubgroup (SchemeWeilDivisor X) where
  carrier := IsLocallyPrincipal
  zero_mem' := isLocallyPrincipal_zero
  add_mem' := IsLocallyPrincipal.add
  neg_mem' := IsLocallyPrincipal.neg

/-- Membership in the subgroup of locally principal Weil divisors is local principality. -/
@[simp]
lemma mem_locallyPrincipalSubgroup {D : SchemeWeilDivisor X} :
    D ∈ locallyPrincipalSubgroup X ↔ IsLocallyPrincipal D :=
  (Iff.rfl)

end LocallyNoetherian

section Noetherian

variable [IsNoetherian X]

/-- A principal Weil divisor is locally principal, with the same equation on the whole scheme. -/
@[simp]
lemma isLocallyPrincipal_principalDivisor (g : Additive X.functionFieldˣ) :
    IsLocallyPrincipal ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) := by
  apply isLocallyPrincipal_of_forall_coeff_eq g
  intro y
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord]

/-- Every principal divisor is locally principal. Equivalently, the principal subgroup is
contained in the subgroup of locally principal divisors. -/
lemma principalSubgroup_le_locallyPrincipalSubgroup :
    (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup ≤ locallyPrincipalSubgroup X := by
  intro D hD
  obtain ⟨g, hg⟩ :=
    (WeilDivisor.OrderSystem.ofScheme X).mem_principalSubgroup.mp hD
  rw [← hg]
  exact isLocallyPrincipal_principalDivisor g

/-- A divisor linearly equivalent to a locally principal divisor is locally principal. -/
lemma IsLocallyPrincipal.of_linearlyEquivalent {D E : SchemeWeilDivisor X}
    (hD : IsLocallyPrincipal D)
    (hDE : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    IsLocallyPrincipal E := by
  have hDiff : IsLocallyPrincipal (D - E) :=
    mem_locallyPrincipalSubgroup.mp
      (principalSubgroup_le_locallyPrincipalSubgroup
        ((WeilDivisor.OrderSystem.ofScheme X).linearlyEquivalent_iff.mp hDE))
  have hE : E = D - (D - E) := by abel
  rw [hE]
  exact hD.sub hDiff

end Noetherian

section Sheaf

variable [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  {D : SchemeWeilDivisor X}

/-- **A local equation trivializes the divisor near its point.** If `D` is locally principal then
every point of `X` has an open neighbourhood `U` and a local equation `g` such that, over every
open subset of `U`, the sheaf `𝒪_X(D - div g)` has the same sections as `𝒪_X(0)`.

Together with `SchemeWeilDivisor.sheafMulIso g D : 𝒪_X(D) ≅ 𝒪_X(D - div g)` this is the local
triviality of `𝒪_X(D)`, which is what invertibility of `𝒪_X(D)` needs. -/
theorem IsLocallyPrincipal.exists_sections_sub_principalDivisor_eq_sections_zero
    (hD : IsLocallyPrincipal D) (x : X) :
    ∃ (U : X.Opens) (g : Additive X.functionFieldˣ), x ∈ U ∧ ∀ V ≤ U,
      sections (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) V =
        sections (0 : SchemeWeilDivisor X) V := by
  obtain ⟨U, hxU, g, hg⟩ := hD x
  refine ⟨U, g, hxU, fun V hV ↦ ?_⟩
  ext s
  simp only [mem_sections]
  refine forall_congr' fun y ↦ forall_congr' fun hy ↦ ?_
  rw [WeilDivisor.coeff_sub, WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord, hg y (hV hy), sub_self, WeilDivisor.coeff_zero]

/-- **The sheaf of a locally principal Weil divisor is locally trivial.** Every point of `X` has
an open neighbourhood `U` together with a divisor `E` such that `𝒪_X(D) ≅ 𝒪_X(E)` and the sections
of `𝒪_X(E)` over every open subset of `U` are those of `𝒪_X(0)`. -/
theorem IsLocallyPrincipal.exists_iso_sheaf_sections_eq_sections_zero
    (hD : IsLocallyPrincipal D) (x : X) :
    ∃ (U : X.Opens) (E : SchemeWeilDivisor X), x ∈ U ∧ Nonempty (sheaf D ≅ sheaf E) ∧
      ∀ V ≤ U, sections E V = sections (0 : SchemeWeilDivisor X) V := by
  obtain ⟨U, g, hxU, hUV⟩ := hD.exists_sections_sub_principalDivisor_eq_sections_zero x
  exact ⟨U, _, hxU, ⟨sheafMulIso g D⟩, hUV⟩

end Sheaf

end

end SchemeWeilDivisor

namespace WeilDivisor.OrderSystem.LinearlyEquivalent

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  {D E : SchemeWeilDivisor X}

/-- Linearly equivalent scheme Weil divisors are locally principal simultaneously. -/
lemma isLocallyPrincipal_iff
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    SchemeWeilDivisor.IsLocallyPrincipal D ↔ SchemeWeilDivisor.IsLocallyPrincipal E := by
  constructor
  · exact fun hD ↦ hD.of_linearlyEquivalent h
  · exact fun hE ↦ hE.of_linearlyEquivalent h.symm

end WeilDivisor.OrderSystem.LinearlyEquivalent

end AlgebraicGeometry

end TauCeti
