/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Huber pairs

A *ring of integral elements* of a Huber ring `A` is an open subring `A⁺` which is integrally
closed in `A` and consists of power-bounded elements, and a *Huber pair* `(A, A⁺)` is a Huber
ring together with such a subring. Huber pairs are the affine objects of the theory: the adic
spectrum of the next layer is built from one.

A Huber ring has many rings of integral elements, so `A⁺` is carried as data rather than
selected by a typeclass; this is the roadmap's standing convention that the plus ring is
explicit.

## Main definitions

* `TauCeti.Huber.IsRingOfIntegralElements`: `A⁺` is open, integrally closed in `A` in the
  sense of Mathlib's `IsIntegrallyClosedIn`, and contained in `A°`.
* `TauCeti.Huber.Pair`: a Huber pair, that is, a choice of `A⁺`.
* `TauCeti.Huber.Pair.Hom`: a continuous ring homomorphism carrying `A⁺` into `B⁺`.

## Main results

* `TauCeti.Huber.IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent`: `A°° ⊆ A⁺` for
  every ring of integral elements.
* `TauCeti.Huber.Pair.powerBounded`: `A⁺ = A°` is a ring of integral elements, the largest one.
* `TauCeti.Huber.Pair.discrete`: a discrete ring is a Huber pair with `A⁺ = A`, so the
  definitions above are not vacuous.
* `TauCeti.Huber.Pair.Hom.id`, `TauCeti.Huber.Pair.Hom.comp`: morphisms of Huber pairs compose,
  associatively and unitally (`TauCeti.Huber.Pair.Hom.comp_assoc`,
  `TauCeti.Huber.Pair.Hom.id_comp`, `TauCeti.Huber.Pair.Hom.comp_id`).
* `TauCeti.Huber.Pair.isRingOfIntegralElements_integralClosure`: the integral closure of an open
  subring contained in the power-bounded subring is a ring of integral elements.
* `TauCeti.Huber.Pair.quotient`: the quotient Huber pair, whose plus ring is the integral closure
  of the image of the original plus ring.
* `TauCeti.Huber.Pair.Hom.quotientLift`: the universal factorisation of a morphism annihilating
  the quotient ideal.

## Provenance

The shape of these declarations follows the roadmap's own prototype in
`TauCetiRoadmap/AdicSpaces/Suggested.lean`, which fixes the design choice that the plus ring is
explicit data rather than a typeclass, and the selection of results follows AINTLIB's
`AffinoidRings.lean`; neither's proofs were used. That AINTLIB file was also consulted for the
quotient-pair construction and its universal property. Its quotient uses the same integral closure
of the image plus ring; this file bundles the construction with the current Tau Ceti Huber-pair API.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 7.14, Remark 7.15, and Definition 7.22.
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  `projects/AdicSpaces/Adic spaces/AffinoidRings.lean`.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A subring `A⁺` of a nonarchimedean ring is a *ring of integral elements* if it is open,
integrally closed in `A`, and contained in the power-bounded subring `A°`. -/
structure IsRingOfIntegralElements [NonarchimedeanRing A] (Aplus : Subring A) : Prop where
  /-- `A⁺` is open in `A`. -/
  isOpen : IsOpen (Aplus : Set A)
  /-- `A⁺` is integrally closed in `A`. -/
  isIntegrallyClosedIn : IsIntegrallyClosedIn Aplus A
  /-- Every element of `A⁺` is power-bounded. -/
  le_powerBoundedSubring : Aplus ≤ powerBoundedSubring A

omit [IsTopologicalRing A] in
/-- Wedhorn: an open integrally closed subring contains every topologically nilpotent element.

Neither power-boundedness nor a nonarchimedean topology plays any part, so this is stated for an
arbitrary open subring integrally closed in `A`, not just for a ring of integral elements. -/
theorem mem_of_isTopologicallyNilpotent_of_isIntegrallyClosedIn {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) [IsIntegrallyClosedIn Aplus A] {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ Aplus := by
  obtain ⟨n, hmem, hn⟩ :=
    ((ha.eventually_mem (hopen.mem_nhds Aplus.zero_mem)).and (eventually_gt_atTop 0)).exists
  have hpow : IsIntegral Aplus (a ^ n) :=
    isIntegral_algebraMap (R := Aplus) (x := (⟨a ^ n, hmem⟩ : Aplus))
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hpow
  exact hy ▸ y.2

omit [IsTopologicalRing A] in
/-- `A°° ⊆ A⁺` for every ring of integral elements. -/
theorem IsRingOfIntegralElements.mem_of_isTopologicallyNilpotent [NonarchimedeanRing A]
    {Aplus : Subring A} (h : IsRingOfIntegralElements Aplus) {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ Aplus :=
  have := h.isIntegrallyClosedIn
  mem_of_isTopologicallyNilpotent_of_isIntegrallyClosedIn h.isOpen ha

variable (A) in
/-- A *Huber pair* `(A, A⁺)`: a Huber ring together with a ring of integral elements. Only the
noncanonical subring `A⁺` is stored; the Huber structure on `A` is a parameter. -/
structure Pair [IsHuberRing A] where
  /-- The ring of integral elements `A⁺`. -/
  plus : Subring A
  /-- `A⁺` really is a ring of integral elements. -/
  isRingOfIntegralElements : IsRingOfIntegralElements plus

namespace Pair

/-- Two Huber pairs on the same Huber ring agree as soon as their rings of integral elements
do: `A⁺` is the only data a Huber pair carries. -/
@[ext]
theorem ext [IsHuberRing A] {S T : Pair A} (h : S.plus = T.plus) : S = T := by
  cases S; cases T; congr

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A morphism of Huber pairs is a continuous ring homomorphism carrying `A⁺` into `B⁺`. -/
structure Hom [IsHuberRing A] [IsHuberRing B] (S : Pair A) (T : Pair B) where
  /-- The underlying ring homomorphism. -/
  toRingHom : A →+* B
  /-- The underlying ring homomorphism is continuous. -/
  continuous_toRingHom : Continuous toRingHom
  /-- The underlying ring homomorphism carries `A⁺` into `B⁺`. -/
  map_mem_plus : ∀ a ∈ S.plus, toRingHom a ∈ T.plus

variable {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
variable [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]

/-- The identity morphism of a Huber pair. -/
def Hom.id (S : Pair A) : Hom S S where
  toRingHom := RingHom.id A
  continuous_toRingHom := continuous_id
  map_mem_plus _ ha := ha

/-- Morphisms of Huber pairs compose. -/
def Hom.comp {S : Pair A} {T : Pair B} {U : Pair C} (g : Hom T U) (f : Hom S T) :
    Hom S U where
  toRingHom := g.toRingHom.comp f.toRingHom
  continuous_toRingHom := g.continuous_toRingHom.comp f.continuous_toRingHom
  map_mem_plus _ ha := g.map_mem_plus _ (f.map_mem_plus _ ha)

@[simp]
theorem Hom.toRingHom_id (S : Pair A) : (Hom.id S).toRingHom = RingHom.id A := (rfl)

@[simp]
theorem Hom.toRingHom_comp {S : Pair A} {T : Pair B} {U : Pair C} (g : Hom T U) (f : Hom S T) :
    (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom := (rfl)

@[ext]
theorem Hom.ext {S : Pair A} {T : Pair B} {f g : Hom S T}
    (h : f.toRingHom = g.toRingHom) : f = g := by
  cases f; cases g; congr

/-- Composition of morphisms of Huber pairs is associative. -/
theorem Hom.comp_assoc {D : Type*} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D]
    [IsHuberRing D] {S : Pair A} {T : Pair B} {U : Pair C} {V : Pair D}
    (h : Hom U V) (g : Hom T U) (f : Hom S T) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext; simp

/-- The identity morphism is a left unit for composition of morphisms of Huber pairs. -/
@[simp]
theorem Hom.id_comp {S : Pair A} {T : Pair B} (f : Hom S T) : (Hom.id T).comp f = f := by
  ext; simp

/-- The identity morphism is a right unit for composition of morphisms of Huber pairs. -/
@[simp]
theorem Hom.comp_id {S : Pair A} {T : Pair B} (f : Hom S T) : f.comp (Hom.id S) = f := by
  ext; simp

variable (A) in
/-- A discrete ring is a Huber pair with `A⁺ = A`: every element is power-bounded, the whole
ring is open, and `⊤` is trivially integrally closed. This is the witness that the definitions
above are satisfiable. -/
def discrete [DiscreteTopology A] : Pair A where
  plus := ⊤
  isRingOfIntegralElements :=
    { isOpen := by simp
      isIntegrallyClosedIn := Subring.isIntegrallyClosedIn_iff.mpr fun _ _ ↦ trivial
      le_powerBoundedSubring := by simp }

/-- The ring of integral elements of the discrete Huber pair is the whole ring. -/
@[simp]
theorem discrete_plus [DiscreteTopology A] : (discrete A).plus = ⊤ := (rfl)

variable (A) in
/-- The Huber pair with `A⁺ = A°`. This is a ring of integral elements because `A°` is open
(`TauCeti.Huber.isOpen_powerBoundedSubring`) and integrally closed in `A`
(`TauCeti.Huber.isPowerBounded_of_isIntegral`, Wedhorn Proposition 5.30(4)). Since every ring of
integral elements is contained in `A°`, this is the largest one. -/
def powerBounded : Pair A where
  plus := powerBoundedSubring A
  isRingOfIntegralElements :=
    { isOpen := isOpen_powerBoundedSubring A
      isIntegrallyClosedIn := inferInstance
      le_powerBoundedSubring := le_rfl }

/-- The ring of integral elements of the largest Huber pair is `A°`. -/
@[simp]
theorem powerBounded_plus : (powerBounded A).plus = powerBoundedSubring A := (rfl)

omit [IsTopologicalRing A] in
/-- The integral closure of an open subring contained in `powerBoundedSubring` is a ring of
integral elements. -/
theorem isRingOfIntegralElements_integralClosure [NonarchimedeanRing A] {R : Subring A}
    (hopen : IsOpen (R : Set A)) (hpb : R ≤ powerBoundedSubring A) :
    IsRingOfIntegralElements (integralClosure R A).toSubring where
  -- `R` is open, and it sits inside its own integral closure via `algebraMap`, so the closure
  -- contains an open additive subgroup.
  isOpen := isOpen_integralClosure_toSubring hopen
  isIntegrallyClosedIn := inferInstance
  le_powerBoundedSubring := Subring.integralClosure_subring_le_iff.mpr hpb

section Quotient

/-- The quotient of a Huber pair by `J` (Wedhorn Definition 7.22). Its plus ring is the
integral closure of the image of the original plus ring in the quotient. -/
noncomputable def quotient (S : Pair A) (J : Ideal A) : Pair (A ⧸ J) where
  plus := (integralClosure (S.plus.map (Ideal.Quotient.mk J)) (A ⧸ J)).toSubring
  isRingOfIntegralElements := by
    let q : A →+* A ⧸ J := Ideal.Quotient.mk J
    let R : Subring (A ⧸ J) := S.plus.map q
    have hR_open : IsOpen (R : Set (A ⧸ J)) := by
      rw [Subring.coe_map]
      exact QuotientRing.isOpenMap_coe J _ S.isRingOfIntegralElements.isOpen
    have hR_power : R ≤ powerBoundedSubring (A ⧸ J) := by
      rintro x hx
      obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hx
      have ha_power :=
        mem_powerBoundedSubring.mp (S.isRingOfIntegralElements.le_powerBoundedSubring ha)
      exact mem_powerBoundedSubring.mpr <|
        ha_power.map_of_isOpenMap continuous_quotient_mk'.continuousAt
          (QuotientRing.isOpenMap_coe J)
    exact isRingOfIntegralElements_integralClosure hR_open hR_power

/-- The plus ring of the quotient pair is the integral closure of the image plus ring. -/
@[simp]
theorem quotient_plus (S : Pair A) (J : Ideal A) :
    (S.quotient J).plus =
      (integralClosure (S.plus.map (Ideal.Quotient.mk J)) (A ⧸ J)).toSubring := (rfl)

/-- The canonical morphism from a Huber pair to its quotient by `J`. -/
noncomputable def quotientHom (S : Pair A) (J : Ideal A) : Hom S (S.quotient J) where
  toRingHom := Ideal.Quotient.mk J
  continuous_toRingHom := continuous_quotient_mk'
  map_mem_plus a ha :=
    algebraMap_mem (integralClosure (S.plus.map (Ideal.Quotient.mk J)) (A ⧸ J))
      ⟨Ideal.Quotient.mk J a, Subring.mem_map.mpr ⟨a, ha, rfl⟩⟩

/-- The underlying map of the canonical quotient-pair morphism is the quotient map. -/
@[simp]
theorem Hom.toRingHom_quotientHom (S : Pair A) (J : Ideal A) :
    (quotientHom S J).toRingHom = Ideal.Quotient.mk J := (rfl)

/-- A morphism of Huber pairs annihilating `J` factors through the quotient pair. -/
noncomputable def Hom.quotientLift {S : Pair A} {T : Pair B} (J : Ideal A) (f : Hom S T)
    (hJ : J ≤ RingHom.ker f.toRingHom) : Hom (S.quotient J) T where
  toRingHom := Ideal.Quotient.lift J f.toRingHom fun a ha ↦ RingHom.mem_ker.mp (hJ ha)
  continuous_toRingHom := continuous_coinduced_dom.mpr f.continuous_toRingHom
  map_mem_plus := by
    let ψ : A ⧸ J →+* B := Ideal.Quotient.lift J f.toRingHom fun a ha ↦
      RingHom.mem_ker.mp (hJ ha)
    let R : Subring (A ⧸ J) := S.plus.map (Ideal.Quotient.mk J)
    let φ : R →+* T.plus :=
      (ψ.comp R.subtype).codRestrict T.plus fun x ↦ by
        obtain ⟨a, ha, hax⟩ := Subring.mem_map.mp x.2
        have hψx : ψ x = f.toRingHom a := by
          rw [← hax]
          exact Ideal.Quotient.lift_mk J f.toRingHom _
        have hψx' : ψ (R.subtype x) = f.toRingHom a := by
          simpa only [Subring.coe_subtype] using hψx
        rw [RingHom.comp_apply, hψx']
        exact f.map_mem_plus a ha
    intro x hx
    apply Subring.isIntegrallyClosedIn_iff.mp T.isRingOfIntegralElements.isIntegrallyClosedIn
    rw [quotient_plus, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hx
    exact hx.map_of_comp_eq φ ψ (by ext y; rfl)

/-- The underlying ring homomorphism of the quotient factorisation is `Ideal.Quotient.lift`. -/
@[simp]
theorem Hom.toRingHom_quotientLift {S : Pair A} {T : Pair B} (J : Ideal A) (f : Hom S T)
    (hJ : J ≤ RingHom.ker f.toRingHom) :
    (f.quotientLift J hJ).toRingHom =
      Ideal.Quotient.lift J f.toRingHom (fun _a ha ↦ RingHom.mem_ker.mp (hJ ha)) := (rfl)

/-- The factorisation through the quotient pair recovers the original morphism. -/
@[simp]
theorem Hom.quotientLift_comp_quotientHom {S : Pair A} {T : Pair B} (J : Ideal A)
    (f : Hom S T) (hJ : J ≤ RingHom.ker f.toRingHom) :
    (f.quotientLift J hJ).comp (quotientHom S J) = f := by
  apply Hom.ext
  rw [Hom.toRingHom_comp, Hom.toRingHom_quotientLift, Hom.toRingHom_quotientHom]
  exact Ideal.Quotient.lift_comp_mk J f.toRingHom _

/-- The factorisation through a quotient Huber pair is unique. -/
theorem Hom.quotientLift_unique {S : Pair A} {T : Pair B} (J : Ideal A) (f : Hom S T)
    (hJ : J ≤ RingHom.ker f.toRingHom) (g : Hom (S.quotient J) T)
    (hg : g.comp (quotientHom S J) = f) : g = f.quotientLift J hJ := by
  apply Hom.ext
  apply Ideal.Quotient.ringHom_ext
  calc
    g.toRingHom.comp (Ideal.Quotient.mk J) = f.toRingHom := congr_arg Hom.toRingHom hg
    _ = (f.quotientLift J hJ).toRingHom.comp (Ideal.Quotient.mk J) :=
      (by
        rw [Hom.toRingHom_quotientLift]
        exact (Ideal.Quotient.lift_comp_mk J f.toRingHom _).symm)

end Quotient

end Pair

end TauCeti.Huber
