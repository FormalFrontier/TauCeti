/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.PNat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Supernatural numbers

A supernatural number, also called a Steinitz number, is a formal product
`\prod_p p ^ n_p`, where `p` ranges over the rational primes and every exponent `n_p` is an
extended natural number.  This file realizes supernatural numbers as exponent functions and
equips them with the arithmetic used for orders and indices of profinite groups.

Multiplication adds exponents, divisibility is pointwise comparison, and gcd and lcm are the
lattice infimum and supremum.  Positive natural numbers embed by their prime factorizations.
The finite supernatural numbers are characterized as those with finite support and no infinite
exponent.

## Main definitions

* `Supernatural`: supernatural numbers as prime-indexed extended-natural exponent functions.
* `Supernatural.ofFun`: the supernatural number with prescribed exponent at each prime.
* `Supernatural.ofNat`: the supernatural number attached to a positive natural number.
* `Supernatural.primePower`: the supernatural prime power `p ^ n`, including `p ^ infinity`.
* `Supernatural.primaryPart`: the `p`-primary part of a supernatural number.
* `Supernatural.primeToPart`: the prime-to-`p` part of a supernatural number.
* `Supernatural.IsNatural`: the predicate that a supernatural number comes from `ofNat`.

## References

This is the `Supernatural` milestone of Layer 1, "supernatural order and index", of the
human-authored roadmap `TauCetiRoadmap/ProfiniteProPGroups/README.md`, which asks for
divisibility as pointwise `≤`, multiplication as pointwise `+`, the lattice operations, the
embedding of `ℕ+` by prime factorization, the "is a natural number" predicate and the
`p`-primary and prime-to-`p` parts, together with an API checklist of the multiplicativity,
injectivity, gcd/lcm and finite-support statements proved below.  The type itself is pinned in
that roadmap's `Suggested.lean` as `Supernatural := Nat.Primes → ℕ∞`.

The definitions and terminology follow Ribes--Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

/-- A supernatural number is a formal product of rational primes with exponents in `\mathbb{N}_∞`.

This is a separate type, rather than an abbreviation for a function type, because multiplication
of supernatural numbers is pointwise addition of exponents, not the pointwise multiplication a
function type carries.  As for Mathlib's `Matrix`, the body of the synonym is exposed, since the
operations are pointwise operations of the underlying function type and can only be defined, and
their pointwise characterizations only stated, with the synonym transparent.  The operations and
instances themselves are opaque and are used through the pointwise lemmas below; `ofFun` is the
named constructor building a supernatural number from its exponents. -/
@[expose]
def Supernatural := Nat.Primes → ℕ∞

namespace Supernatural

instance : CoeFun Supernatural fun _ ↦ Nat.Primes → ℕ∞ := ⟨id⟩

/-- Two supernatural numbers are equal when all of their prime exponents are equal. -/
@[ext]
theorem ext {m n : Supernatural} (h : ∀ p, m p = n p) : m = n :=
  funext h

/-- The supernatural number with prescribed exponent at each prime.

This is the named constructor for downstream definitions such as `profiniteOrder`, playing the
role that `Matrix.of` plays for `Matrix`. -/
def ofFun (f : Nat.Primes → ℕ∞) : Supernatural :=
  f

@[simp]
theorem ofFun_apply (f : Nat.Primes → ℕ∞) (p : Nat.Primes) : ofFun f p = f p :=
  (rfl)

noncomputable instance : CompleteLattice Supernatural :=
  inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

instance : One Supernatural := ⟨fun _ ↦ 0⟩

instance : Mul Supernatural := ⟨fun m n p ↦ m p + n p⟩

instance : CommMonoid Supernatural where
  mul_assoc m n k := by ext p; exact add_assoc (m p) (n p) (k p)
  one_mul m := by ext p; exact zero_add (m p)
  mul_one m := by ext p; exact add_zero (m p)
  mul_comm m n := by ext p; exact add_comm (m p) (n p)

/-- Every exponent of the multiplicative unit is zero. -/
@[simp]
theorem one_apply (p : Nat.Primes) : (1 : Supernatural) p = 0 :=
  rfl

@[simp]
theorem mul_apply (m n : Supernatural) (p : Nat.Primes) : (m * n) p = m p + n p :=
  rfl

/-- Raising to a natural power multiplies every exponent by that power. -/
@[simp]
theorem pow_apply (m : Supernatural) (n : ℕ) (p : Nat.Primes) : (m ^ n) p = n • m p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply, ih, add_nsmul, one_nsmul]

@[simp]
theorem inf_apply (m n : Supernatural) (p : Nat.Primes) : (m ⊓ n) p = m p ⊓ n p :=
  rfl

@[simp]
theorem sup_apply (m n : Supernatural) (p : Nat.Primes) : (m ⊔ n) p = m p ⊔ n p :=
  rfl

/-- Every exponent of the greatest supernatural number is infinite. -/
@[simp]
theorem top_apply (p : Nat.Primes) : (⊤ : Supernatural) p = ⊤ :=
  rfl

/-- Every exponent of the least supernatural number is zero. -/
@[simp]
theorem bot_apply (p : Nat.Primes) : (⊥ : Supernatural) p = 0 :=
  rfl

/-- Suprema of supernatural numbers are computed exponentwise. -/
@[simp]
theorem iSup_apply {ι : Sort*} (m : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, m i) p = ⨆ i, m i p :=
  _root_.iSup_apply

/-- Infima of supernatural numbers are computed exponentwise. -/
@[simp]
theorem iInf_apply {ι : Sort*} (m : ι → Supernatural) (p : Nat.Primes) :
    (⨅ i, m i) p = ⨅ i, m i p :=
  _root_.iInf_apply

/-- The multiplicative unit is also the least supernatural number. -/
@[simp]
theorem one_eq_bot : (1 : Supernatural) = ⊥ :=
  rfl

/-- Divisibility of supernatural numbers is comparison of every prime exponent. -/
@[simp]
theorem dvd_iff_le {m n : Supernatural} : m ∣ n ↔ m ≤ n := by
  constructor
  · rintro ⟨k, rfl⟩ p
    exact le_add_right (le_refl (m p))
  · intro h
    refine ⟨fun p ↦ n p - m p, ?_⟩
    ext p
    exact (add_tsub_cancel_of_le (h p)).symm

/-- One supernatural number is at most another exactly when each exponent is at most the
corresponding exponent of the other. -/
theorem le_iff {m n : Supernatural} : m ≤ n ↔ ∀ p, m p ≤ n p :=
  Pi.le_def

/-- A supernatural number divides another exactly when each exponent is at most the
corresponding exponent of the other. -/
theorem dvd_iff {m n : Supernatural} : m ∣ n ↔ ∀ p, m p ≤ n p :=
  dvd_iff_le.trans le_iff

/-- The exponent of a supernatural number at a given prime. -/
def exponent (p : Nat.Primes) : Supernatural →o ℕ∞ :=
  Pi.evalOrderHom p

@[simp]
theorem exponent_apply (p : Nat.Primes) (m : Supernatural) : exponent p m = m p :=
  (rfl)

/-- The supernatural prime power `p ^ n`; all exponents away from `p` are zero. -/
def primePower (p : Nat.Primes) (n : ℕ∞) : Supernatural :=
  Pi.single p n

@[simp]
theorem primePower_apply_self (p : Nat.Primes) (n : ℕ∞) : primePower p n p = n :=
  Pi.single_eq_same (M := fun _ : Nat.Primes ↦ ℕ∞) p n

@[simp]
theorem primePower_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : ℕ∞) :
    primePower p n q = 0 :=
  Pi.single_eq_of_ne (M := fun _ : Nat.Primes ↦ ℕ∞) h n

@[simp]
theorem primePower_zero (p : Nat.Primes) : primePower p 0 = 1 :=
  Pi.single_zero p

/-- A prime power with a sum of exponents is the product of the two prime powers. -/
@[simp]
theorem primePower_add (p : Nat.Primes) (m n : ℕ∞) :
    primePower p (m + n) = primePower p m * primePower p n := by
  apply ext
  intro q
  rw [mul_apply]
  exact congrFun (Pi.single_add (f := fun _ : Nat.Primes ↦ ℕ∞) p m n) q

/-- A rational prime, regarded as the supernatural number having exponent one at that prime. -/
instance : Coe Nat.Primes Supernatural :=
  ⟨fun p ↦ primePower p 1⟩

/-- A prime is at most a supernatural number exactly when its exponent there is nonzero.

This is the simp-normal form of `coe_prime_dvd_iff`, since `dvd_iff_le` rewrites divisibility
of supernatural numbers to comparison. -/
@[simp]
theorem coe_prime_le_iff (p : Nat.Primes) (n : Supernatural) :
    (p : Supernatural) ≤ n ↔ n p ≠ 0 := by
  rw [le_iff]
  constructor
  · intro h
    exact Order.one_le_iff_ne_zero.mp (by simpa using h p)
  · intro h q
    by_cases hq : q = p
    · subst q
      simpa using Order.one_le_iff_ne_zero.mpr h
    · simp [hq]

/-- A prime divides a supernatural number exactly when its exponent there is nonzero. -/
theorem coe_prime_dvd_iff (p : Nat.Primes) (n : Supernatural) :
    (p : Supernatural) ∣ n ↔ n p ≠ 0 :=
  dvd_iff_le.trans (coe_prime_le_iff p n)

/-- The `p`-primary part of a supernatural number. -/
def primaryPart (p : Nat.Primes) (n : Supernatural) : Supernatural :=
  primePower p (n p)

@[simp]
theorem primaryPart_apply_self (p : Nat.Primes) (n : Supernatural) : primaryPart p n p = n p :=
  primePower_apply_self _ _

@[simp]
theorem primaryPart_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : Supernatural) :
    primaryPart p n q = 0 :=
  primePower_apply_of_ne h _

/-- The prime-to-`p` part of a supernatural number, obtained by deleting its `p`-exponent. -/
def primeToPart (p : Nat.Primes) (n : Supernatural) : Supernatural :=
  Function.update n p 0

@[simp]
theorem primeToPart_apply_self (p : Nat.Primes) (n : Supernatural) : primeToPart p n p = 0 :=
  Function.update_self p 0 n

@[simp]
theorem primeToPart_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : Supernatural) :
    primeToPart p n q = n q :=
  Function.update_of_ne h 0 n

/-- A supernatural number is the product of its `p`-primary and prime-to-`p` parts. -/
theorem primaryPart_mul_primeToPart (p : Nat.Primes) (n : Supernatural) :
    primaryPart p n * primeToPart p n = n := by
  ext q
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

/-- The embedding of positive natural numbers into supernatural numbers by prime
factorization. -/
def ofNat (n : ℕ+) : Supernatural :=
  fun p ↦ (padicValNat p n : ℕ∞)

@[simp]
theorem ofNat_apply (n : ℕ+) (p : Nat.Primes) : ofNat n p = (padicValNat p n : ℕ∞) :=
  (rfl)

@[simp]
theorem ofNat_one : ofNat 1 = 1 := by
  ext p
  simp [ofNat]

/-- The prime factorization embedding turns multiplication of positive natural numbers into
multiplication of supernatural numbers, that is, into addition of exponents. -/
@[simp]
theorem ofNat_mul (m n : ℕ+) : ofNat (m * n) = ofNat m * ofNat n := by
  ext p
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  rw [mul_apply, ofNat_apply, ofNat_apply, ofNat_apply, PNat.mul_coe,
    padicValNat.mul m.ne_zero n.ne_zero, Nat.cast_add]

/-- Prime factorization embeds positive natural numbers injectively into supernatural numbers. -/
theorem ofNat_injective : Function.Injective ofNat := by
  intro m n h
  apply PNat.eq
  rw [Nat.eq_iff_prime_padicValNat_eq m n m.ne_zero n.ne_zero]
  intro p hp
  have hv := congrFun h ⟨p, hp⟩
  rw [ofNat_apply m ⟨p, hp⟩, ofNat_apply n ⟨p, hp⟩] at hv
  exact_mod_cast hv

/-- The embedding of positive natural numbers as a multiplicative homomorphism. -/
def ofNatMonoidHom : ℕ+ →* Supernatural where
  toFun := ofNat
  map_one' := ofNat_one
  map_mul' := ofNat_mul

@[simp]
theorem ofNatMonoidHom_apply (n : ℕ+) : ofNatMonoidHom n = ofNat n :=
  (rfl)

/-- Divisibility of positive natural numbers agrees with comparison of their supernatural
images.

This is the simp-normal form of `ofNat_dvd_ofNat_iff`, since `dvd_iff_le` rewrites divisibility
of supernatural numbers to comparison. -/
@[simp]
theorem ofNat_le_ofNat_iff {m n : ℕ+} : ofNat m ≤ ofNat n ↔ m ∣ n := by
  rw [le_iff]
  constructor
  · intro h
    rw [PNat.dvd_iff, ← Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero]
    intro p
    by_cases hp : p.Prime
    · have hv := h ⟨p, hp⟩
      rw [ofNat_apply m ⟨p, hp⟩, ofNat_apply n ⟨p, hp⟩, ENat.natCast_le_natCast] at hv
      simpa [Nat.factorization_def _ hp] using hv
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · intro h p
    rw [PNat.dvd_iff, ← Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero] at h
    have hp := h (p : ℕ)
    rw [Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop] at hp
    rw [ofNat_apply, ofNat_apply, ENat.natCast_le_natCast]
    exact hp

/-- Divisibility of positive natural numbers agrees with divisibility of their supernatural
images. -/
theorem ofNat_dvd_ofNat_iff {m n : ℕ+} : ofNat m ∣ ofNat n ↔ m ∣ n :=
  dvd_iff_le.trans ofNat_le_ofNat_iff

/-- The positive-natural embedding takes gcd to the supernatural gcd. -/
@[simp]
theorem ofNat_gcd (m n : ℕ+) : ofNat (PNat.gcd m n) = ofNat m ⊓ ofNat n := by
  ext p
  have h := DFunLike.congr_fun (Nat.factorization_gcd m.ne_zero n.ne_zero) (p : ℕ)
  rw [Finsupp.inf_apply, Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop,
    Nat.factorization_def _ p.prop] at h
  simp only [ofNat_apply, inf_apply]
  calc
    (padicValNat (p : ℕ) (PNat.gcd m n) : ℕ∞) =
        (min (padicValNat (p : ℕ) m) (padicValNat (p : ℕ) n) : ℕ) := congr_arg _ h
    _ = min (padicValNat (p : ℕ) m : ℕ∞) (padicValNat (p : ℕ) n) :=
      Monotone.map_min fun _ _ hle ↦ ENat.natCast_le_natCast.mpr hle

/-- The positive-natural embedding takes lcm to the supernatural lcm. -/
@[simp]
theorem ofNat_lcm (m n : ℕ+) : ofNat (PNat.lcm m n) = ofNat m ⊔ ofNat n := by
  ext p
  have h := DFunLike.congr_fun (Nat.factorization_lcm m.ne_zero n.ne_zero) (p : ℕ)
  rw [Finsupp.sup_apply, Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop,
    Nat.factorization_def _ p.prop] at h
  simp only [ofNat_apply, sup_apply]
  calc
    (padicValNat (p : ℕ) (PNat.lcm m n) : ℕ∞) =
        (max (padicValNat (p : ℕ) m) (padicValNat (p : ℕ) n) : ℕ) := congr_arg _ h
    _ = max (padicValNat (p : ℕ) m : ℕ∞) (padicValNat (p : ℕ) n) :=
      Monotone.map_max fun _ _ hle ↦ ENat.natCast_le_natCast.mpr hle

/-- A supernatural number is natural when it lies in the image of `ofNat`. -/
def IsNatural (n : Supernatural) : Prop :=
  ∃ m : ℕ+, ofNat m = n

/-- A supernatural number is natural exactly when it is the image under `ofNat` of a positive
natural number.  This is `IsNatural` by definition, and is the form downstream files use, since
the body of `IsNatural` is not exposed. -/
theorem isNatural_def {n : Supernatural} : IsNatural n ↔ ∃ m : ℕ+, ofNat m = n :=
  Iff.rfl

/-- Every positive natural number gives a natural supernatural number. -/
@[simp]
theorem isNatural_ofNat (n : ℕ+) : IsNatural (ofNat n) :=
  ⟨n, rfl⟩

/-- The support of a supernatural number is the set of primes having nonzero exponent. -/
def support (n : Supernatural) : Set Nat.Primes :=
  Function.support n

@[simp]
theorem mem_support {n : Supernatural} {p : Nat.Primes} : p ∈ support n ↔ n p ≠ 0 :=
  Iff.rfl

private theorem finite_support_ofNat (n : ℕ+) : (support (ofNat n)).Finite := by
  refine ((n : ℕ).primeFactors.finite_toSet.preimage Subtype.val_injective.injOn).subset ?_
  intro p hp
  dsimp [support, Function.support, ofNat] at hp
  simp only [Set.mem_preimage, Finset.mem_coe]
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, Nat.factorization_def _ p.prop]
  intro h
  apply hp
  simp [h]

private theorem finite_values_ofNat (n : ℕ+) (p : Nat.Primes) : ofNat n p ≠ ⊤ := by
  simp [ofNat]

/-- A supernatural number comes from a positive natural number exactly when it has finite
support and every exponent is finite. -/
theorem isNatural_iff {n : Supernatural} :
    IsNatural n ↔ (support n).Finite ∧ ∀ p, n p ≠ ⊤ := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨finite_support_ofNat m, finite_values_ofNat m⟩
  · rintro ⟨hsupport, hfinite⟩
    have htoNatSupport :
        (Function.support fun p : Nat.Primes ↦ ENat.toNat (n p)).Finite :=
      hsupport.subset fun p hp ↦ by
        rw [mem_support]
        intro hzero
        rw [Function.mem_support] at hp
        apply hp
        simp [hzero]
    let f : Nat.Primes →₀ ℕ :=
      Finsupp.ofSupportFinite (fun p ↦ ENat.toNat (n p)) htoNatSupport
    let g : ℕ →₀ ℕ := f.mapDomain ((↑) : Nat.Primes → ℕ)
    have hgprime : ∀ q ∈ g.support, q.Prime := by
      intro q hq
      have hsupp : g.support = f.support.map ⟨Subtype.val, Subtype.val_injective⟩ := by
        simpa [g] using
          Finsupp.support_mapDomain_embedding ⟨Subtype.val, Subtype.val_injective⟩ f
      rw [hsupp] at hq
      obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hq
      exact p.prop
    refine ⟨Nat.factorizationEquiv.symm ⟨g, hgprime⟩, ?_⟩
    ext p
    have hfactorization :
        ((Nat.factorizationEquiv.symm ⟨g, hgprime⟩ : ℕ+) : ℕ).factorization = g :=
      congrArg Subtype.val (Nat.factorizationEquiv.apply_symm_apply ⟨g, hgprime⟩)
    have hvaluation :
        padicValNat p ((Nat.factorizationEquiv.symm ⟨g, hgprime⟩ : ℕ+) : ℕ) = ENat.toNat (n p) := by
      rw [← Nat.factorization_def _ p.prop, hfactorization]
      exact Finsupp.mapDomain_apply Subtype.val_injective f p
    rw [ofNat_apply, hvaluation]
    exact ENat.natCast_toNat (hfinite p)

/-- A prime power with infinite exponent is not a natural supernatural number. -/
@[simp]
theorem not_isNatural_primePower_top (p : Nat.Primes) : ¬IsNatural (primePower p ⊤) := by
  rw [isNatural_iff]
  push Not
  exact fun _ ↦ ⟨p, by simp⟩

end Supernatural

end TauCeti
