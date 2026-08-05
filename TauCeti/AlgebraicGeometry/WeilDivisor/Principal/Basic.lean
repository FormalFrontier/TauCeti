/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

/-!
# Principal divisors and the divisor class group of an order system

This file adds the next piece of the Jacobian roadmap's Layer A on top of the formal Weil
divisor group: **principal divisors**, the **divisor class group** `Cl(X)`, and the abstract
degree-zero subgroup `Pic⁰`.

The geometric input is packaged as an `OrderSystem`: a family of `ℤ`-valued order-of-vanishing
homomorphisms `ord x : G →+ ℤ` indexed by the points `X`, with the finiteness condition that
each `g : G` has nonzero order at only finitely many points. Instantiating `G` with
`Additive Kˣ` for the multiplicative group of a function field, `ord x` is the order of
vanishing `ord_x(f)` of a rational function `f` at the point `x`, and the principal divisor of
`f` is the finite formal sum `Σ_x ord_x(f) · [x]`. The finiteness condition is exactly the
statement that a rational function has zeros and poles at only finitely many points.

From this data we build:

* `OrderSystem.principalDivisor` and `OrderSystem.principalHom`, the principal divisor of a
  function and its packaging as a homomorphism `G →+ WeilDivisor X`;
* `OrderSystem.principalSubgroup`, the subgroup of principal divisors, and
  `OrderSystem.LinearlyEquivalent`, the equivalence relation "differ by a principal divisor";
* `OrderSystem.ClassGroup`, the divisor class group `WeilDivisor X ⧸ principal`, with its
  quotient map `OrderSystem.divisorClass` and the characterization of equal classes;
* `OrderSystem.weightedDegreeClass` and `OrderSystem.picZero`: when principal divisors have
  weighted degree zero (the geometric fact that a rational function has as many zeros as poles,
  counted with residue-field degrees on a curve over a non-algebraically-closed field, recorded
  here as the hypothesis `IsWeightedDegreeZero`), the weighted degree descends to the class
  group, and `Pic⁰` is the kernel of that descended weighted degree.

This advances the Layer A roadmap item "principal divisors" and constructs the abstract
"`Pic⁰ X = ker deg` (as an abstract group, with the geometric degree supplied as a weight)" of
`TauCetiRoadmap/JacobianChallenge/README.md`. It builds only the divisor-class side `Cl(X)` of
the later "`Cl(X) ≅ Pic X`" comparison: the Picard group and the equivalence to it are not
constructed here, but are later geometric work, before the Picard functor and Picard scheme
exist. The geometric `ord_x` (residue-field valuations of a function field) and the proof that
a principal divisor has weighted degree zero are later geometric constructions; here both are
abstracted to the data of an `OrderSystem`, a weight function, and the predicate
`IsWeightedDegreeZero`.

No external mathematics is vendored. This reuses Tau Ceti's existing `WeilDivisor` API and
Mathlib's `Finsupp.ofSupportFinite` (to assemble a finitely supported function from
coordinatewise data) and `QuotientAddGroup` quotient machinery.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

/-- An *order system* on a type of points `X` with values in a group `G`: a family of
`ℤ`-valued homomorphisms `ord x : G →+ ℤ`, the orders of vanishing at each point, such that
every `g : G` vanishes to nonzero order at only finitely many points.

Instantiate `G` with `Additive Kˣ` for the multiplicative group of a function field `K`: then
`ord x` is the order of vanishing `ord_x(f)` of a rational function at the point `x`, and the
finiteness condition records that a rational function has zeros and poles at only finitely many
points. The principal divisor of `f` is `Σ_x ord_x(f) · [x]`. -/
structure OrderSystem (X G : Type*) [AddCommGroup G] where
  /-- The order of vanishing at each point, as a homomorphism `G →+ ℤ`. -/
  ord : X → G →+ ℤ
  /-- Each group element has nonzero order at only finitely many points. -/
  finite_support : ∀ g, (Function.support fun x => ord x g).Finite

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

/-- The principal divisor `Σ_x ord_x(g) · [x]` attached to `g : G`. -/
noncomputable def principalDivisor (g : G) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x => S.ord x g) (S.finite_support g)

@[simp]
lemma coeff_principalDivisor (g : G) (x : X) :
    coeff (S.principalDivisor g) x = S.ord x g := by
  rw [principalDivisor, coeff, Finsupp.ofSupportFinite_coe]

/-- Principal divisors as a homomorphism `G →+ WeilDivisor X`. -/
noncomputable def principalHom : G →+ WeilDivisor X where
  toFun := S.principalDivisor
  map_zero' := by ext x; simp
  map_add' g₁ g₂ := by ext x; simp

@[simp]
lemma principalHom_apply (g : G) : S.principalHom g = S.principalDivisor g := by
  rw [principalHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

@[simp]
lemma principalDivisor_zero : S.principalDivisor 0 = 0 :=
  map_zero S.principalHom

lemma principalDivisor_add (g₁ g₂ : G) :
    S.principalDivisor (g₁ + g₂) = S.principalDivisor g₁ + S.principalDivisor g₂ :=
  map_add S.principalHom g₁ g₂

@[simp]
lemma principalDivisor_neg (g : G) : S.principalDivisor (-g) = -S.principalDivisor g :=
  map_neg S.principalHom g

lemma principalDivisor_sub (g₁ g₂ : G) :
    S.principalDivisor (g₁ - g₂) = S.principalDivisor g₁ - S.principalDivisor g₂ :=
  map_sub S.principalHom g₁ g₂

/-- The subgroup of principal divisors. -/
noncomputable def principalSubgroup : AddSubgroup (WeilDivisor X) :=
  S.principalHom.range

lemma mem_principalSubgroup {D : WeilDivisor X} :
    D ∈ S.principalSubgroup ↔ ∃ g, S.principalDivisor g = D :=
  AddMonoidHom.mem_range

/-- The subgroup of principal divisors is the range of the principal-divisor homomorphism. -/
lemma principalSubgroup_eq_range : S.principalSubgroup = S.principalHom.range := by
  ext D
  rw [mem_principalSubgroup, AddMonoidHom.mem_range]
  simp only [principalHom_apply]

@[simp]
lemma principalDivisor_mem_principalSubgroup (g : G) :
    S.principalDivisor g ∈ S.principalSubgroup :=
  ⟨g, rfl⟩

/-- Two Weil divisors are *linearly equivalent* with respect to `S` when their difference is a
principal divisor. This is the equivalence relation whose quotient is the divisor class
group. -/
def LinearlyEquivalent (D E : WeilDivisor X) : Prop :=
  D - E ∈ S.principalSubgroup

lemma linearlyEquivalent_iff {D E : WeilDivisor X} :
    S.LinearlyEquivalent D E ↔ D - E ∈ S.principalSubgroup :=
  Iff.rfl

/-- Two Weil divisors are linearly equivalent exactly when their difference is the principal
divisor of some `g : G`. This is the direct introduction/elimination form of
`LinearlyEquivalent`, exposing the witnessing function. -/
lemma linearlyEquivalent_iff_exists_principalDivisor {D E : WeilDivisor X} :
    S.LinearlyEquivalent D E ↔ ∃ g, S.principalDivisor g = D - E :=
  S.mem_principalSubgroup

lemma LinearlyEquivalent.refl (D : WeilDivisor X) : S.LinearlyEquivalent D D := by
  simp [LinearlyEquivalent]

variable {S}

lemma LinearlyEquivalent.symm {D E : WeilDivisor X} (h : S.LinearlyEquivalent D E) :
    S.LinearlyEquivalent E D := by
  have := S.principalSubgroup.neg_mem h
  rwa [neg_sub] at this

lemma LinearlyEquivalent.trans {D E F : WeilDivisor X} (h₁ : S.LinearlyEquivalent D E)
    (h₂ : S.LinearlyEquivalent E F) : S.LinearlyEquivalent D F := by
  have := S.principalSubgroup.add_mem h₁ h₂
  rwa [sub_add_sub_cancel] at this

variable (S)

/-- Linear equivalence is compatible with adding equivalent divisors on both sides. -/
lemma LinearlyEquivalent.add {D D' E E' : WeilDivisor X} (hD : S.LinearlyEquivalent D D')
    (hE : S.LinearlyEquivalent E E') : S.LinearlyEquivalent (D + E) (D' + E') := by
  rw [linearlyEquivalent_iff] at hD hE ⊢
  have hsum := S.principalSubgroup.add_mem hD hE
  convert hsum using 1
  abel

/-- Adding the same divisor on the right preserves linear equivalence. -/
lemma LinearlyEquivalent.add_right {D D' : WeilDivisor X} (hD : S.LinearlyEquivalent D D')
    (E : WeilDivisor X) : S.LinearlyEquivalent (D + E) (D' + E) :=
  LinearlyEquivalent.add S hD (LinearlyEquivalent.refl S E)

/-- Adding the same divisor on the left preserves linear equivalence. -/
lemma LinearlyEquivalent.add_left {E E' : WeilDivisor X} (hE : S.LinearlyEquivalent E E')
    (D : WeilDivisor X) : S.LinearlyEquivalent (D + E) (D + E') :=
  LinearlyEquivalent.add S (LinearlyEquivalent.refl S D) hE

/-- A divisor plus a principal divisor is linearly equivalent to the original divisor. -/
lemma linearlyEquivalent_add_principalDivisor (D : WeilDivisor X) (g : G) :
    S.LinearlyEquivalent (D + S.principalDivisor g) D := by
  rw [linearlyEquivalent_iff]
  convert S.principalDivisor_mem_principalSubgroup g using 1
  abel

/-- Subtracting a principal divisor from a divisor is linearly equivalent to the original
divisor. -/
lemma linearlyEquivalent_sub_principalDivisor (D : WeilDivisor X) (g : G) :
    S.LinearlyEquivalent (D - S.principalDivisor g) D := by
  rw [linearlyEquivalent_iff]
  convert S.principalDivisor_mem_principalSubgroup (-g) using 1
  rw [S.principalDivisor_neg]
  abel

lemma equivalence_linearlyEquivalent : Equivalence S.LinearlyEquivalent :=
  ⟨LinearlyEquivalent.refl S, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The *divisor class group* `Cl(X) = WeilDivisor X ⧸ (principal divisors)` of an order
system `S`. -/
abbrev ClassGroup : Type _ :=
  WeilDivisor X ⧸ S.principalSubgroup

/-- The divisor class of a Weil divisor in the divisor class group. -/
noncomputable def divisorClass : WeilDivisor X →+ S.ClassGroup :=
  QuotientAddGroup.mk' S.principalSubgroup

/-- The divisor-class map is the canonical additive quotient projection
`WeilDivisor X → Cl(X)`. This is the definitional equation, exposed so that downstream files can
rewrite between `divisorClass` and `QuotientAddGroup.mk'`. -/
lemma divisorClass_eq_mk' (D : WeilDivisor X) :
    S.divisorClass D = QuotientAddGroup.mk' S.principalSubgroup D := by
  unfold OrderSystem.divisorClass
  rfl

lemma divisorClass_surjective : Function.Surjective S.divisorClass :=
  QuotientAddGroup.mk'_surjective S.principalSubgroup

@[simp]
lemma divisorClass_principalDivisor (g : G) :
    S.divisorClass (S.principalDivisor g) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (S.principalDivisor_mem_principalSubgroup g)

/-- Two Weil divisors have the same divisor class exactly when they are linearly equivalent,
that is, when their difference is a principal divisor. -/
lemma divisorClass_eq_iff {D E : WeilDivisor X} :
    S.divisorClass D = S.divisorClass E ↔ S.LinearlyEquivalent D E :=
  QuotientAddGroup.eq_iff_sub_mem

lemma divisorClass_eq_zero_iff {D : WeilDivisor X} :
    S.divisorClass D = 0 ↔ D ∈ S.principalSubgroup :=
  QuotientAddGroup.eq_zero_iff D

/-- The universal property of the divisor class group: a homomorphism `φ : WeilDivisor X →+ H`
that sends every principal divisor to `0` descends to a homomorphism `Cl(X) →+ H`. -/
noncomputable def ClassGroup.lift {H : Type*} [AddCommGroup H] (φ : WeilDivisor X →+ H)
    (hφ : ∀ g, φ (S.principalDivisor g) = 0) : S.ClassGroup →+ H :=
  QuotientAddGroup.lift S.principalSubgroup φ (by
    rintro _ ⟨g, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact hφ g)

@[simp]
lemma ClassGroup.lift_divisorClass {H : Type*} [AddCommGroup H] (φ : WeilDivisor X →+ H)
    (hφ : ∀ g, φ (S.principalDivisor g) = 0) (D : WeilDivisor X) :
    ClassGroup.lift S φ hφ (S.divisorClass D) = φ D :=
  QuotientAddGroup.lift_mk' S.principalSubgroup _ D

/-- An order system has *weighted-degree-zero principal divisors* for a weight `w : X → ℤ` when
every principal divisor has weighted degree zero.

For a smooth proper curve over a field `k`, the intended weight is the residue-field degree
`x ↦ [κ(x) : k]`; this is the geometric fact that a rational function has as many zeros as
poles, counted with residue-field degrees. -/
@[expose] def IsWeightedDegreeZero (w : X → ℤ) : Prop :=
  ∀ g, weightedDegree w (S.principalDivisor g) = 0

variable {S}

lemma IsWeightedDegreeZero.principalSubgroup_le_weightedDegree_ker {w : X → ℤ}
    (h : S.IsWeightedDegreeZero w) :
    S.principalSubgroup ≤ (weightedDegree w : WeilDivisor X →+ ℤ).ker := by
  rintro D ⟨g, rfl⟩
  rw [AddMonoidHom.mem_ker]
  exact h g

/-- When principal divisors have weighted degree zero, the weighted degree map descends to the
divisor class group: linearly equivalent divisors have the same weighted degree. -/
noncomputable def weightedDegreeClass (w : X → ℤ) (h : S.IsWeightedDegreeZero w) :
    S.ClassGroup →+ ℤ :=
  QuotientAddGroup.lift S.principalSubgroup (weightedDegree w)
    h.principalSubgroup_le_weightedDegree_ker

@[simp]
lemma weightedDegreeClass_divisorClass (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (D : WeilDivisor X) :
    weightedDegreeClass w h (S.divisorClass D) = weightedDegree w D :=
  QuotientAddGroup.lift_mk' S.principalSubgroup h.principalSubgroup_le_weightedDegree_ker D

/-- The weighted-degree-zero part of the divisor class group, the abstract `Pic⁰` of the
Jacobian roadmap: the kernel of the weighted degree map on divisor classes. -/
@[expose] noncomputable def picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w) :
    AddSubgroup S.ClassGroup :=
  (weightedDegreeClass w h).ker

lemma mem_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {c : S.ClassGroup} :
    c ∈ picZero w h ↔ weightedDegreeClass w h c = 0 :=
  AddMonoidHom.mem_ker

/-- The class of a Weil divisor lies in `picZero` exactly when that representative has weighted
degree zero; the value is well defined because the weighted degree descends to the class. -/
@[simp]
lemma divisorClass_mem_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {D : WeilDivisor X} :
    S.divisorClass D ∈ picZero w h ↔ weightedDegree w D = 0 := by
  rw [mem_picZero, weightedDegreeClass_divisorClass]

/-- An order system has *unweighted-degree-zero principal divisors* when every principal
divisor has unweighted degree zero. This is the specialization of `IsWeightedDegreeZero` to the
constant weight `1`, appropriate for the algebraically closed/unweighted formal setting. -/
@[expose] def IsUnweightedDegreeZero : Prop :=
  S.IsWeightedDegreeZero fun _ => (1 : ℤ)

lemma IsUnweightedDegreeZero.principalSubgroup_le_ker (h : S.IsUnweightedDegreeZero) :
    S.principalSubgroup ≤ (degree : WeilDivisor X →+ ℤ).ker := by
  intro D hD
  rw [AddMonoidHom.mem_ker, ← weightedDegree_one_eq_degree D]
  exact h.principalSubgroup_le_weightedDegree_ker hD

/-- The unweighted degree map on divisor classes, for the algebraically closed/unweighted
specialization: the descended degree `weightedDegreeClass` at the constant weight `1`. For
curves over a general field, use `weightedDegreeClass`. -/
@[expose]
noncomputable def unweightedDegreeClass (h : S.IsUnweightedDegreeZero) : S.ClassGroup →+ ℤ :=
  weightedDegreeClass (fun _ => (1 : ℤ)) h

@[simp]
lemma unweightedDegreeClass_divisorClass (h : S.IsUnweightedDegreeZero) (D : WeilDivisor X) :
    unweightedDegreeClass h (S.divisorClass D) = degree D := by
  exact (weightedDegreeClass_divisorClass (S := S) (fun _ => 1) h D).trans
    (weightedDegree_one_eq_degree D)

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
