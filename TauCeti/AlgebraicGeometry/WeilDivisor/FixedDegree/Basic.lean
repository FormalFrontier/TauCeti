/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# Effective Weil divisors of fixed degree

This file packages the fixed-degree part of the effective Weil-divisor monoid.  For a type of
points `X`, the type `EffectiveDivisorOfDegree X d` consists of effective formal divisors of
degree `d`.  It is equivalent to Mathlib's symmetric power `Sym X d`, by reading a multiset as
its finitely supported multiplicity function and conversely reading an effective divisor by its
natural-number coefficients.

This is the formal divisor model behind the Jacobian roadmap's Layer C symmetric-power lane:
the scheme-level construction of `Symᵈ X` and relative effective Cartier divisors is later
geometry, but the Abel-map input already needs the divisor represented by an unordered
degree-`d` collection of points.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer C, "Relative effective
Cartier divisors and symmetric powers `Symᵈ X`", as a small prerequisite built from the
existing Layer A `WeilDivisor` API.  No external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

/-- The effective Weil divisors of degree `d`. -/
abbrev EffectiveDivisorOfDegree (X : Type*) (d : ℕ) : Type _ :=
  {D : WeilDivisor X // IsEffective D ∧ degree D = d}

namespace EffectiveDivisorOfDegree

@[ext]
lemma ext {D E : EffectiveDivisorOfDegree X d} (h : (D : WeilDivisor X) = E) : D = E :=
  Subtype.ext h

/-- The zero effective divisor, regarded as the unique effective divisor of degree `0`. -/
abbrev zero (X : Type*) : EffectiveDivisorOfDegree X 0 :=
  ⟨0, isEffective_zero, degree_zero⟩

/-- The underlying Weil divisor of the degree-zero effective divisor is zero. -/
@[simp]
lemma coe_zero : (zero X : WeilDivisor X) = 0 :=
  rfl

/-- Change the degree index of a fixed-degree effective divisor along an equality. -/
protected def cast {d e : ℕ} (h : d = e) :
    EffectiveDivisorOfDegree X d ≃ EffectiveDivisorOfDegree X e where
  toFun D := ⟨D, D.property.1, D.property.2.trans (by exact_mod_cast h)⟩
  invFun D := ⟨D, D.property.1, D.property.2.trans (by exact_mod_cast h.symm)⟩

/-- Changing the degree index along `rfl` leaves a fixed-degree divisor unchanged. -/
@[simp]
lemma cast_rfl (D : EffectiveDivisorOfDegree X d) :
    EffectiveDivisorOfDegree.cast rfl D = D :=
  Subtype.ext rfl

/-- Changing the degree index does not change the underlying Weil divisor. -/
@[simp]
lemma coe_cast {d e : ℕ} (h : d = e) (D : EffectiveDivisorOfDegree X d) :
    (EffectiveDivisorOfDegree.cast h D : WeilDivisor X) = D := by
  subst e
  simp

@[simp]
lemma isEffective (D : EffectiveDivisorOfDegree X d) : IsEffective (D : WeilDivisor X) :=
  D.property.1

@[simp]
lemma degree_eq (D : EffectiveDivisorOfDegree X d) : degree (D : WeilDivisor X) = d :=
  D.property.2

lemma mem_effectiveSubmonoid (D : EffectiveDivisorOfDegree X d) :
    (D : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (WeilDivisor.mem_effectiveSubmonoid _).mpr D.isEffective

/-- An effective divisor of degree `d` from finitely supported natural multiplicities whose
total multiplicity is `d`. -/
abbrev ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    EffectiveDivisorOfDegree X d :=
  ⟨WeilDivisor.ofFinsupp m, isEffective_ofFinsupp m, by
    rw [degree_ofFinsupp]
    exact_mod_cast hm⟩

@[simp]
lemma coe_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    (ofFinsupp m hm : WeilDivisor X) = WeilDivisor.ofFinsupp m :=
  rfl

lemma coeff_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) (x : X) :
    coeff (ofFinsupp m hm : WeilDivisor X) x = m x :=
  WeilDivisor.coeff_ofFinsupp m x

/-- The finitely supported natural multiplicity function underlying an effective divisor. -/
abbrev multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) : X →₀ ℕ :=
  Finsupp.ofSupportFinite (fun x => (coeff (D : WeilDivisor X) x).toNat) <|
    (D : WeilDivisor X).support.finite_toSet.subset <| by
      intro x hx
      -- `support.finite_toSet` exposes membership in the set coercion of the finset support;
      -- switch to finset membership before using the coefficient support lemma.
      change x ∈ (D : WeilDivisor X).support
      rw [WeilDivisor.mem_support_iff]
      intro hcoeff
      exact hx (by simp [hcoeff])

@[simp]
lemma multiplicityFinsupp_apply (D : EffectiveDivisorOfDegree X d) (x : X) :
    D.multiplicityFinsupp x = (coeff (D : WeilDivisor X) x).toNat :=
  by
    rw [multiplicityFinsupp, Finsupp.ofSupportFinite_coe]

/-- Rebuilding an effective divisor from its natural multiplicity function recovers the
underlying Weil divisor. -/
@[simp]
lemma ofFinsupp_multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) :
    WeilDivisor.ofFinsupp D.multiplicityFinsupp = (D : WeilDivisor X) := by
  ext x
  rw [WeilDivisor.coeff_ofFinsupp, multiplicityFinsupp_apply]
  exact Int.toNat_of_nonneg ((isEffective_iff (D : WeilDivisor X)).mp D.property.1 x)

/-- The natural multiplicity function of a degree-`d` effective divisor has total mass `d`. -/
lemma sum_multiplicityFinsupp (D : EffectiveDivisorOfDegree X d) :
    D.multiplicityFinsupp.sum (fun _ n => n) = d := by
  have hcast :
      (D.multiplicityFinsupp.sum fun _ n => (n : ℤ)) = degree (D : WeilDivisor X) := by
    rw [← ofFinsupp_multiplicityFinsupp D, degree_ofFinsupp]
    simp [Finsupp.sum]
  exact_mod_cast hcast.trans D.degree_eq

/-- Rebuilding an effective divisor from its natural multiplicity function recovers the
original fixed-degree divisor. -/
@[simp]
lemma ofFinsupp_multiplicityFinsupp_eq (D : EffectiveDivisorOfDegree X d) :
    ofFinsupp D.multiplicityFinsupp D.sum_multiplicityFinsupp = D := by
  exact Subtype.ext (ofFinsupp_multiplicityFinsupp D)

/-- The natural multiplicity function of a divisor built from a finitely supported function is
that function. -/
@[simp]
lemma multiplicityFinsupp_ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    (ofFinsupp m hm).multiplicityFinsupp = m := by
  ext x
  simp

/-- Fixed-degree effective divisors are equivalently finitely supported natural multiplicities
with total mass `d`. -/
abbrev equivFinsupp :
    EffectiveDivisorOfDegree X d ≃ {m : X →₀ ℕ // m.sum (fun _ n => n) = d} where
  toFun D := ⟨D.multiplicityFinsupp, D.sum_multiplicityFinsupp⟩
  invFun m := ofFinsupp m.1 m.2
  left_inv D := by simp
  right_inv m := by
    ext x
    simp

@[simp]
lemma equivFinsupp_apply_coe (D : EffectiveDivisorOfDegree X d) :
    (equivFinsupp D : X →₀ ℕ) = D.multiplicityFinsupp :=
  rfl

@[simp]
lemma equivFinsupp_symm_apply (m : {m : X →₀ ℕ // m.sum (fun _ n => n) = d}) :
    (equivFinsupp.symm m : WeilDivisor X) = WeilDivisor.ofFinsupp m.1 :=
  rfl

section Sym

/-- The effective divisor associated to an unordered degree-`d` collection of points. -/
def ofSym (s : Sym X d) : EffectiveDivisorOfDegree X d :=
  letI := Classical.decEq X
  equivFinsupp.symm (Sym.equivNatSum X d s)

@[simp]
lemma coe_ofSym (s : Sym X d) : (ofSym s : WeilDivisor X) =
      WeilDivisor.ofFinsupp (letI := Classical.decEq X; (Sym.equivNatSum X d s).1) := by
  classical
  rfl

/-- The symmetric-power divisor has coefficient equal to the multiplicity of the point in the
unordered collection. -/
lemma coeff_ofSym (s : Sym X d) (x : X) :
    coeff (ofSym s : WeilDivisor X) x =
      (letI := Classical.decEq X; (s : Multiset X).count x) := by
  classical
  rw [coe_ofSym, WeilDivisor.coeff_ofFinsupp]
  exact_mod_cast Sym.coe_equivNatSum_apply_apply X d s x

/-- Effective degree-`d` divisors are the same data as the `d`-th symmetric power of the
underlying point type. -/
def equivSym : EffectiveDivisorOfDegree X d ≃ Sym X d := by
  letI := Classical.decEq X
  exact equivFinsupp.trans (Sym.equivNatSum X d).symm

/-- Applying the symmetric-power equivalence is the same as applying Mathlib's multiplicity
equivalence to the fixed-degree divisor's multiplicity function. -/
lemma equivSym_apply (D : EffectiveDivisorOfDegree X d) :
    equivSym D =
      (letI := Classical.decEq X; (Sym.equivNatSum X d).symm (equivFinsupp D)) := by
  classical
  rfl

/-- The inverse of the symmetric-power equivalence is `ofSym`. -/
@[simp]
lemma equivSym_symm_apply (s : Sym X d) :
    (equivSym.symm s : EffectiveDivisorOfDegree X d) = ofSym s := by
  classical
  rfl

/-- Converting a divisor to the symmetric power and back gives the original divisor. -/
@[simp]
lemma ofSym_equivSym (D : EffectiveDivisorOfDegree X d) :
    ofSym (equivSym D) = D := by
  classical
  exact equivSym.left_inv D

/-- Converting a symmetric-power point to a divisor and back gives the original symmetric-power
point. -/
@[simp]
lemma equivSym_ofSym (s : Sym X d) :
    equivSym (ofSym s) = s := by
  classical
  exact equivSym.right_inv s

end Sym

/-- Pushing forward a fixed-degree effective divisor preserves its degree. -/
abbrev pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    EffectiveDivisorOfDegree Y d :=
  ⟨WeilDivisor.pushforward f D, D.isEffective.pushforward f, by
    rw [degree_pushforward, D.degree_eq]⟩

@[simp]
lemma coe_pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    (D.pushforward f : WeilDivisor Y) = WeilDivisor.pushforward f D :=
  rfl

/-- Pushing forward along the identity function is the identity on fixed-degree divisors. -/
@[simp]
lemma pushforward_id (D : EffectiveDivisorOfDegree X d) :
    D.pushforward (fun x : X => x) = D := by
  ext
  rw [coe_pushforward, WeilDivisor.pushforward_id]
  rfl

/-- Pushforwards of fixed-degree divisors compose functorially. -/
@[simp]
lemma pushforward_comp {Z : Type*} (g : Y → Z) (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    (D.pushforward f).pushforward g = D.pushforward (g ∘ f) := by
  ext
  rw [coe_pushforward, coe_pushforward, coe_pushforward, WeilDivisor.pushforward_comp]
  rfl

/-- Pushing forward a divisor built from multiplicities corresponds to `Finsupp.mapDomain`. -/
@[simp]
lemma pushforward_ofFinsupp (f : X → Y) (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    (ofFinsupp m hm).pushforward f = ofFinsupp (m.mapDomain f) (by
      exact (Finsupp.sum_mapDomain_index_addMonoidHom
        (f := f) (s := m) (fun _ : Y => AddMonoidHom.id ℕ)).trans hm) := by
  classical
  apply Subtype.ext
  ext y
  rw [coe_pushforward, coe_ofFinsupp, coe_ofFinsupp, WeilDivisor.coeff_pushforward,
    WeilDivisor.coeff_ofFinsupp]
  simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply, Finset.sum_ite]

/-- The multiplicity function of a pushforward is the pushed-forward multiplicity function. -/
@[simp]
lemma multiplicityFinsupp_pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    (D.pushforward f).multiplicityFinsupp = D.multiplicityFinsupp.mapDomain f := by
  have h := pushforward_ofFinsupp f D.multiplicityFinsupp D.sum_multiplicityFinsupp
  rw [ofFinsupp_multiplicityFinsupp_eq D] at h
  rw [h, multiplicityFinsupp_ofFinsupp]

/-- The symmetric-power equivalence sends divisor pushforward to `Sym.map`. -/
@[simp]
lemma equivSym_pushforward (f : X → Y) (D : EffectiveDivisorOfDegree X d) :
    equivSym (D.pushforward f) = Sym.map f (equivSym D) := by
  classical
  apply (Sym.equivNatSum Y d).injective
  ext y
  simp [equivSym_apply, Finsupp.toMultiset_map]

end EffectiveDivisorOfDegree

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti
