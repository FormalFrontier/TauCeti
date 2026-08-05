/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Data.Sym.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegree.Basic

/-!
# Addition of fixed-degree effective Weil divisors

This file records the degree-indexed addition operation on effective Weil divisors of fixed
degree.  Adding an effective divisor of degree `d` to one of degree `e` gives an effective
divisor of degree `d + e`; under the equivalence with Mathlib's symmetric powers, this is
exactly `Sym.append`.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`").  It supplies the additive compatibility between unordered
collections of points and the effective-divisor model used by Abel-map statements.  No external
mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X Y : Type*} {d e : ℕ}

noncomputable section

/-- Add fixed-degree effective divisors.  The degree index records additivity of degree. -/
abbrev add (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (d + e) :=
  ⟨(D : WeilDivisor X) + E, D.isEffective.add E.isEffective, by
    simp [degree_add, D.degree_eq, E.degree_eq]⟩

/-- The underlying Weil divisor of a fixed-degree sum is the sum of the underlying divisors. -/
@[simp]
lemma coe_add (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (add D E : WeilDivisor X) = (D : WeilDivisor X) + E :=
  rfl

/-- The coefficient of a fixed-degree sum is the sum of the coefficients. -/
@[simp]
lemma coeff_add (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (add D E : WeilDivisor X) x = coeff (D : WeilDivisor X) x + coeff E x := by
  rw [coe_add, WeilDivisor.coeff_add]

/-- Zero is a left identity for fixed-degree effective-divisor addition. -/
@[simp]
lemma zero_add (D : EffectiveDivisorOfDegree X d) :
    add (zero X) D = EffectiveDivisorOfDegree.cast (Nat.zero_add d).symm D := by
  ext
  simp

/-- Zero is a right identity for fixed-degree effective-divisor addition. -/
@[simp]
lemma add_zero (D : EffectiveDivisorOfDegree X d) :
    add D (zero X) = EffectiveDivisorOfDegree.cast (Nat.add_zero d).symm D := by
  ext
  simp

/-- Fixed-degree effective-divisor addition is commutative, up to the degree-index cast. -/
lemma add_comm (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    add D E = EffectiveDivisorOfDegree.cast (Nat.add_comm e d) (add E D) := by
  ext
  simp [Int.add_comm]

/-- Fixed-degree effective-divisor addition is associative, up to the degree-index cast. -/
lemma add_assoc {n : ℕ} (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) (F : EffectiveDivisorOfDegree X n) :
    add (add D E) F =
      EffectiveDivisorOfDegree.cast (Nat.add_assoc d e n).symm (add D (add E F)) := by
  ext
  simp [Int.add_assoc]

/-- Adding divisors built from finitely supported multiplicities corresponds to adding their
multiplicity functions. -/
@[simp]
lemma add_ofFinsupp (m n : X →₀ ℕ) (hm : m.sum (fun _ k => k) = d) (hn : n.sum (fun _ k => k) = e) :
    add (ofFinsupp m hm) (ofFinsupp n hn) =
      ofFinsupp (m + n) (by
        rw [Finsupp.sum_add_index']
        · simp [hm, hn]
        · simp
        · simp) := by
  apply Subtype.ext
  ext x
  simp

/-- The multiplicity function of a sum is the sum of the multiplicity functions. -/
@[simp]
lemma multiplicityFinsupp_add (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (add D E).multiplicityFinsupp = D.multiplicityFinsupp + E.multiplicityFinsupp := by
  have h := add_ofFinsupp D.multiplicityFinsupp E.multiplicityFinsupp
    D.sum_multiplicityFinsupp E.sum_multiplicityFinsupp
  rw [ofFinsupp_multiplicityFinsupp_eq D, ofFinsupp_multiplicityFinsupp_eq E] at h
  rw [h, multiplicityFinsupp_ofFinsupp]

/-- The symmetric-power equivalence sends fixed-degree divisor addition to `Sym.append`. -/
@[simp]
lemma equivSym_add (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    equivSym (add D E) = (equivSym D).append (equivSym E) := by
  classical
  apply (Sym.equivNatSum X (d + e)).injective
  ext x
  simp [equivSym_apply]

/-- Adding the divisors associated to symmetric-power points is the divisor associated to
their appended unordered collection. -/
@[simp]
lemma add_ofSym (s : Sym X d) (t : Sym X e) :
    add (ofSym s) (ofSym t) = ofSym (s.append t) := by
  classical
  apply equivSym.injective
  simp

/-- The divisor associated to an appended symmetric-power point is the sum of the associated
fixed-degree divisors. -/
@[simp]
lemma coe_ofSym_append (s : Sym X d) (t : Sym X e) :
    WeilDivisor.ofFinsupp
        (letI := Classical.decEq X; ((Sym.equivNatSum X (d + e)) (s.append t)).1) =
      (ofSym s : WeilDivisor X) + (ofSym t : WeilDivisor X) := by
  rw [← coe_ofSym, ← coe_add, add_ofSym]

/-- Pushforward commutes with addition of fixed-degree effective divisors. -/
@[simp]
lemma pushforward_add (f : X → Y) (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (add D E).pushforward f = add (D.pushforward f) (E.pushforward f) := by
  ext
  simp [WeilDivisor.pushforward_add]

/-- On symmetric powers, pushforward compatibility for fixed-degree divisor addition is the
usual compatibility of `Sym.map` with `Sym.append`. -/
lemma equivSym_pushforward_add (f : X → Y) (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    equivSym ((add D E).pushforward f) =
      (Sym.map f (equivSym D)).append (Sym.map f (equivSym E)) := by
  rw [equivSym_pushforward, equivSym_add, Sym.map_append]

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
