/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.Huber.Basic

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
* `TauCeti.Huber.Pair.quotient`: the quotient Huber pair, whose plus ring is the integral closure
  of the image of the original plus ring.
* `TauCeti.Huber.Pair.Hom.quotientLift`: the universal factorisation of a morphism annihilating
  the quotient ideal.

## Provenance

The shape of these declarations follows the roadmap's own prototype in
`TauCetiRoadmap/AdicSpaces/Suggested.lean`, which fixes the design choice that the plus ring is
explicit data rather than a typeclass, and the selection of results follows AINTLIB's
`AffinoidRings.lean`; neither's proofs were used.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 7.14 and Remark 7.15.
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

section Quotient

/-- The image of a pair of definition in a quotient ring is again a pair of definition. -/
def _root_.TauCeti.Huber.PairOfDefinition.quotient (P : PairOfDefinition A) (J : Ideal A) :
    PairOfDefinition (A ⧸ J) := by
  let q : A →+* A ⧸ J := Ideal.Quotient.mk J
  let A₀ : Subring (A ⧸ J) := P.ringOfDefinition.map q
  let q₀ : P.ringOfDefinition →+* A₀ :=
    (q.comp P.ringOfDefinition.subtype).codRestrict A₀ fun a ↦
      Subring.mem_map.mpr ⟨a, a.2, rfl⟩
  have hq₀_cont : Continuous q₀ := by
    dsimp [q₀]
    exact (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _
  have hq₀_open : IsOpenMap q₀ := by
    dsimp [q₀]
    exact
      (QuotientRing.isOpenMap_coe J).subtype_map P.isOpen_ringOfDefinition
        (fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩)
  have hq₀_surj : Function.Surjective q₀ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hx
    exact ⟨⟨a, ha⟩, rfl⟩
  refine
    { ringOfDefinition := A₀
      isOpen_ringOfDefinition := by
        rw [show (A₀ : Set (A ⧸ J)) = q '' (P.ringOfDefinition : Set A) by
          exact Subring.coe_map q P.ringOfDefinition]
        exact QuotientRing.isOpenMap_coe J _ P.isOpen_ringOfDefinition
      idealOfDefinition := P.idealOfDefinition.map q₀
      fg_idealOfDefinition := P.fg_idealOfDefinition.map q₀
      isAdic_idealOfDefinition := isAdic_iff.mpr ⟨?_, ?_⟩ }
  · intro n
    rw [← Ideal.map_pow]
    have hset : ((P.idealOfDefinition ^ n).map q₀ : Set A₀) =
        q₀ '' ((P.idealOfDefinition ^ n : Ideal P.ringOfDefinition) :
          Set P.ringOfDefinition) := by
      ext y
      exact Ideal.mem_map_iff_of_surjective q₀ hq₀_surj
    rw [hset]
    exact hq₀_open _ ((isAdic_iff.mp P.isAdic_idealOfDefinition).1 n)
  · intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.mp P.isAdic_idealOfDefinition).2
      (q₀ ⁻¹' s) (hq₀_cont.continuousAt.preimage_mem_nhds (by simpa using hs))
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow]
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_map_iff_of_surjective q₀ hq₀_surj |>.mp hy
    exact hn hx

/-- Quotients of Huber rings, with the quotient topology, are Huber rings. -/
instance _root_.TauCeti.Huber.IsHuberRing.quotient (J : Ideal A) : IsHuberRing (A ⧸ J) :=
  ⟨IsHuberRing.nonempty_pairOfDefinition.elim fun P ↦ ⟨P.quotient J⟩⟩

/-- The quotient of a Huber pair by `J`. Its plus ring is the integral closure of the image of
the original plus ring in the quotient. -/
noncomputable def quotient (S : Pair A) (J : Ideal A) : Pair (A ⧸ J) where
  plus := (integralClosure (S.plus.map (Ideal.Quotient.mk J)) (A ⧸ J)).toSubring
  isRingOfIntegralElements := by
    let q : A →+* A ⧸ J := Ideal.Quotient.mk J
    let R : Subring (A ⧸ J) := S.plus.map q
    have hR_open : IsOpen (R : Set (A ⧸ J)) := by
      rw [show (R : Set (A ⧸ J)) = q '' (S.plus : Set A) by exact Subring.coe_map q S.plus]
      exact QuotientRing.isOpenMap_coe J _ S.isRingOfIntegralElements.isOpen
    have hR_power : R ≤ powerBoundedSubring (A ⧸ J) := by
      rintro x hx
      obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hx
      have ha_power :=
        mem_powerBoundedSubring.mp (S.isRingOfIntegralElements.le_powerBoundedSubring ha)
      exact mem_powerBoundedSubring.mpr <|
        ha_power.map_of_isOpenMap continuous_quotient_mk'.continuousAt
          (QuotientRing.isOpenMap_coe J)
    refine
      { isOpen := AddSubgroup.isOpen_of_mem_nhds
          (integralClosure R (A ⧸ J)).toSubring.toAddSubgroup <|
          Filter.mem_of_superset (hR_open.mem_nhds R.zero_mem) fun x hx ↦
            algebraMap_mem (integralClosure R (A ⧸ J)) ⟨x, hx⟩
        isIntegrallyClosedIn := inferInstance
        le_powerBoundedSubring := ?_ }
    exact Subring.integralClosure_subring_le_iff.mpr hR_power

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
theorem quotientHom_toRingHom (S : Pair A) (J : Ideal A) :
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
        change ψ x ∈ T.plus
        rw [← hax]
        change f.toRingHom a ∈ T.plus
        exact f.map_mem_plus a ha
    intro x hx
    apply Subring.isIntegrallyClosedIn_iff.mp T.isRingOfIntegralElements.isIntegrallyClosedIn
    exact (show IsIntegral R x from hx).map_of_comp_eq φ ψ (by ext y; rfl)

@[simp]
theorem Hom.quotientLift_comp_quotientHom {S : Pair A} {T : Pair B} (J : Ideal A)
    (f : Hom S T) (hJ : J ≤ RingHom.ker f.toRingHom) :
    (f.quotientLift J hJ).comp (quotientHom S J) = f := by
  apply Hom.ext
  dsimp [Hom.quotientLift, quotientHom]
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
        dsimp [Hom.quotientLift]
        exact (Ideal.Quotient.lift_comp_mk J f.toRingHom _).symm)

end Quotient

end Pair

end TauCeti.Huber
