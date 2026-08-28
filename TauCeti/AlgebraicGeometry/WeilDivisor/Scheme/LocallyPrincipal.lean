/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
import Mathlib.Tactic.Abel

/-!
# Locally principal Weil divisors on a scheme

Let `X` be a locally Noetherian integral scheme. A Weil divisor `D` on `X` is locally principal when
every point has an open neighbourhood on which the coefficients of `D` agree with those of the
principal divisor of one nonzero rational function. This is the condition which identifies a
Weil divisor with a Cartier divisor when the comparison between the two kinds of divisor is
available.

## Main declarations

* `SchemeWeilDivisor.IsLocallyPrincipal D` is the local-principality predicate;
* `SchemeWeilDivisor.locallyPrincipalSubgroup X` is the subgroup of locally principal Weil
  divisors;
* `SchemeWeilDivisor.principalSubgroup_le_locallyPrincipalSubgroup` records that principal
  divisors are locally principal;
* `WeilDivisor.OrderSystem.LinearlyEquivalent.isLocallyPrincipal_iff` shows that local
  principality depends only on the divisor class.

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

open AlgebraicGeometry TopologicalSpace

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

/-- Local principality, unfolded into its neighbourhood-and-equation formulation. -/
lemma isLocallyPrincipal_iff {D : SchemeWeilDivisor X} :
    IsLocallyPrincipal D ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ g : Additive X.functionFieldˣ,
        ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
          WeilDivisor.coeff D y = orderAt y g :=
  Iff.rfl

/-- The zero Weil divisor is locally principal. -/
lemma isLocallyPrincipal_zero : IsLocallyPrincipal (0 : SchemeWeilDivisor X) := by
  rw [isLocallyPrincipal_iff]
  intro x
  refine ⟨⊤, Set.mem_univ x, 0, fun y _ ↦ ?_⟩
  rw [WeilDivisor.coeff_zero, map_zero]

namespace IsLocallyPrincipal

variable {D E : SchemeWeilDivisor X}

/-- The sum of two locally principal Weil divisors is locally principal. Local equations add on
the intersection of their neighbourhoods. -/
lemma add (hD : IsLocallyPrincipal D) (hE : IsLocallyPrincipal E) :
    IsLocallyPrincipal (D + E) := by
  rw [isLocallyPrincipal_iff] at hD hE ⊢
  intro x
  obtain ⟨U, hxU, g, hg⟩ := hD x
  obtain ⟨V, hxV, h, hh⟩ := hE x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, g + h, ?_⟩
  intro y hy
  rw [WeilDivisor.coeff_add, hg y hy.1, hh y hy.2, map_add]

/-- The negation of a locally principal Weil divisor is locally principal. -/
lemma neg (hD : IsLocallyPrincipal D) : IsLocallyPrincipal (-D) := by
  rw [isLocallyPrincipal_iff] at hD ⊢
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

/-- The additive subgroup of locally principal Weil divisors on `X`. -/
def locallyPrincipalSubgroup (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    AddSubgroup (SchemeWeilDivisor X) where
  carrier := IsLocallyPrincipal
  zero_mem' := isLocallyPrincipal_zero
  add_mem' := IsLocallyPrincipal.add
  neg_mem' := IsLocallyPrincipal.neg

/-- Membership in the subgroup of locally principal Weil divisors is local principality. -/
@[simp]
lemma mem_locallyPrincipalSubgroup_iff {D : SchemeWeilDivisor X} :
    D ∈ locallyPrincipalSubgroup X ↔ IsLocallyPrincipal D :=
  Iff.rfl

end LocallyNoetherian

section Noetherian

variable [IsNoetherian X]

/-- On a Noetherian scheme, local principality can be stated using the globally assembled
principal Weil divisor of each local equation. -/
lemma isLocallyPrincipal_iff_exists_principalDivisor {D : SchemeWeilDivisor X} :
    IsLocallyPrincipal D ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ g : Additive X.functionFieldˣ,
        ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
          WeilDivisor.coeff D y =
            WeilDivisor.coeff
              ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) y := by
  rw [isLocallyPrincipal_iff]
  simp only [WeilDivisor.OrderSystem.coeff_principalDivisor,
    WeilDivisor.OrderSystem.ofScheme_ord]

/-- A principal Weil divisor is locally principal, with the same equation on the whole scheme. -/
lemma isLocallyPrincipal_principalDivisor (g : Additive X.functionFieldˣ) :
    IsLocallyPrincipal ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) := by
  rw [isLocallyPrincipal_iff_exists_principalDivisor]
  intro x
  exact ⟨⊤, Set.mem_univ x, g, fun _ _ ↦ rfl⟩

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
  have hDiff : D - E ∈ locallyPrincipalSubgroup X :=
    principalSubgroup_le_locallyPrincipalSubgroup
      ((WeilDivisor.OrderSystem.ofScheme X).linearlyEquivalent_iff.mp hDE)
  have hE : E = D - (D - E) := by abel
  rw [hE]
  exact hD.sub hDiff

end Noetherian

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
