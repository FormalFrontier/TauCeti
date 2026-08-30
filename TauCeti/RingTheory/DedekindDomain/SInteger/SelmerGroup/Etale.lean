/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic

/-!
# Selmer groups of a finite etale algebra

The finiteness of the Selmer group proved in
`TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic` is stated for a Dedekind domain
with a fraction *field*. The arithmetic application needs it for a finite etale algebra `A` over a
number field, which is not a field but a product of them. This file makes that step: it forms the
product of the Selmer groups of the factors and transports it along a decomposition of `A` into
fields. The number-field case, where both finiteness hypotheses are theorems of Mathlib, is
`TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.NumberField`.

## Main definitions

* `IsDedekindDomain.selmerGroupPi`: the product of the Selmer groups of the factors.
* `IsDedekindDomain.selmerGroupOfEquiv`: the Selmer group of `A`, defined by pulling
  `selmerGroupPi` back along a decomposition of `A` into a product of fields.

## Main results

* `IsDedekindDomain.finite_selmerGroupPi` and `IsDedekindDomain.finite_selmerGroupOfEquiv`: both
  are finite, for finitely many factors each with finite class group and finitely generated units.

## Implementation notes

The decomposition `e` is an input rather than something extracted from an `Algebra.IsEtale`
hypothesis: Mathlib does not provide the splitting of an etale algebra into fields, and at the
application site the decomposition is already in hand.

Where the source this follows takes the finiteness of each factor's Selmer group as an explicit
argument, here it is found by instance resolution: `IsDedekindDomain.selmerGroup.finite` is an
`instance` whose two hypotheses are supplied by `IsDedekindDomain.finite_integer_classGroup` and
`Set.unit_fg_of_units`, which are themselves instances. So a caller holding
`[Finite (ClassGroup (B i))]`, `[Monoid.FG (B i)ˣ]` and the finiteness of `S i` gets it unaided;
the `Set.Finite` hypotheses are converted to `Finite` instances with `Set.Finite.to_subtype`.

## References

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
`EllipticCurves` roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), whose treatment this
follows. The names differ: that source abbreviates the quotient `Kˣ ⧸ (Kˣ)ⁿ` as `Units.modPow` and
states the per-factor finiteness as an explicit `finite_selmerGroup`, whereas here the quotient is
spelled out as Mathlib does and the finiteness is the instance
`IsDedekindDomain.selmerGroup.finite`.
-/

public section

namespace IsDedekindDomain

open IsDedekindDomain.HeightOneSpectrum

section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)

/-- The product of the Selmer groups of the field factors. -/
noncomputable def selmerGroupPi :
    Subgroup ((i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range) :=
  Subgroup.pi Set.univ fun i ↦ selmerGroup (R := B i) (K := L i) (S := S i) (n := n)

/-- Membership in the product is membership in each factor. -/
@[simp]
lemma mem_selmerGroupPi_iff
    (x : (i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range) :
    x ∈ selmerGroupPi L B S n ↔
      ∀ i, x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupPi, Subgroup.mem_pi]

/-- A finite product of Selmer groups is finite. -/
theorem finite_selmerGroupPi [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Monoid.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n] :
    Finite (selmerGroupPi L B S n) := by
  have (i : ι) : Finite (S i) := (hS i).to_subtype
  have (i : ι) : Finite (selmerGroup (R := B i) (K := L i) (S := S i) (n := n)) := inferInstance
  exact .of_injective (fun x i ↦ (⟨x.1 i, (mem_selmerGroupPi_iff L B S n x.1).mp x.2 i⟩ :
    selmerGroup (R := B i) (K := L i) (S := S i) (n := n)))
    fun x y hxy ↦ Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun hxy i)

variable {A : Type*} [CommRing A]

/-- The Selmer group of the etale algebra `A`, transported along a decomposition of `A` into a
product of fields. -/
noncomputable def selmerGroupOfEquiv
    (e : Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range ≃*
      ((i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range)) :
    Subgroup (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) :=
  (selmerGroupPi L B S n).comap e.toMonoidHom

/-- Membership in the transported Selmer group is the Selmer condition on each factor. -/
@[simp]
lemma mem_selmerGroupOfEquiv_iff
    (e : Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range ≃*
      ((i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range))
    (x : Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) :
    x ∈ selmerGroupOfEquiv L B S n e ↔
      ∀ i, e x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupOfEquiv, selmerGroupPi, Subgroup.mem_pi]

/-- The Selmer group of a finite etale algebra is finite. -/
theorem finite_selmerGroupOfEquiv [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Monoid.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n]
    (e : Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range ≃*
      ((i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range)) :
    Finite (selmerGroupOfEquiv L B S n e) := by
  have := finite_selmerGroupPi L B S n hS
  exact .of_injective (fun x ↦ (⟨e x.1, x.2⟩ : selmerGroupPi L B S n))
    fun x y hxy ↦ Subtype.ext <| e.injective <| congrArg Subtype.val hxy

end Etale

end IsDedekindDomain

end
