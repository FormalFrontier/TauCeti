import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Prime

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

The definitions and terminology follow Ribes--Zalesskii, *Profinite Groups*, Section 2.3.

## Main definitions

* `Supernatural`: supernatural numbers as prime-indexed extended-natural exponent functions.
* `Supernatural.ofNat`: the supernatural number attached to a positive natural number.
* `Supernatural.primePower`: the supernatural prime power `p ^ n`, including `p ^ infinity`.
* `Supernatural.primaryPart`: the `p`-primary part of a supernatural number.
* `Supernatural.primeToPart`: the prime-to-`p` part of a supernatural number.
* `Supernatural.IsNatural`: the predicate that a supernatural number comes from `ofNat`.
-/

namespace TauCeti

/-- A supernatural number is a formal product of rational primes with exponents in `\mathbb{N}_∞`.

This is a separate type, rather than an abbreviation for a function type, because multiplication
of supernatural numbers is pointwise addition of exponents. -/
def Supernatural := Nat.Primes → ℕ∞

namespace Supernatural

instance : CoeFun Supernatural fun _ ↦ Nat.Primes → ℕ∞ := ⟨id⟩

/-- Two supernatural numbers are equal when all of their prime exponents are equal. -/
@[ext]
theorem ext {m n : Supernatural} (h : ∀ p, m p = n p) : m = n :=
  funext h

noncomputable instance : CompleteLattice Supernatural :=
  inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

instance : One Supernatural := ⟨fun _ ↦ 0⟩

instance : Mul Supernatural := ⟨fun m n p ↦ m p + n p⟩

instance : CommMonoid Supernatural where
  mul_assoc m n k := by ext p; exact add_assoc (m p) (n p) (k p)
  one_mul m := by ext p; exact zero_add (m p)
  mul_one m := by ext p; exact add_zero (m p)
  mul_comm m n := by ext p; exact add_comm (m p) (n p)

@[simp]
theorem one_apply (p : Nat.Primes) : (1 : Supernatural) p = 0 :=
  rfl

@[simp]
theorem mul_apply (m n : Supernatural) (p : Nat.Primes) : (m * n) p = m p + n p :=
  rfl

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

/-- The multiplicative unit is also the least supernatural number. -/
@[simp]
theorem one_eq_bot : (1 : Supernatural) = ⊥ :=
  rfl

/-- Divisibility of supernatural numbers is comparison of every prime exponent. -/
theorem dvd_iff_le {m n : Supernatural} : m ∣ n ↔ m ≤ n := by
  constructor
  · rintro ⟨k, rfl⟩ p
    exact le_add_right (le_refl (m p))
  · intro h
    refine ⟨fun p ↦ n p - m p, ?_⟩
    ext p
    exact (add_tsub_cancel_of_le (h p)).symm

/-- A supernatural number divides another exactly when each exponent is at most the
corresponding exponent of the other. -/
theorem dvd_iff {m n : Supernatural} : m ∣ n ↔ ∀ p, m p ≤ n p :=
  dvd_iff_le.trans Pi.le_def

/-- The exponent of a supernatural number at a given prime. -/
def exponent (p : Nat.Primes) : Supernatural →o ℕ∞ where
  toFun m := m p
  monotone' _ _ h := h p

@[simp]
theorem exponent_apply (p : Nat.Primes) (m : Supernatural) : exponent p m = m p :=
  rfl

/-- The supernatural prime power `p ^ n`; all exponents away from `p` are zero. -/
def primePower (p : Nat.Primes) (n : ℕ∞) : Supernatural :=
  fun q ↦ if q = p then n else 0

@[simp]
theorem primePower_apply_self (p : Nat.Primes) (n : ℕ∞) : primePower p n p = n := by
  simp [primePower]

@[simp]
theorem primePower_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : ℕ∞) :
    primePower p n q = 0 := by
  simp [primePower, h]

@[simp]
theorem primePower_zero (p : Nat.Primes) : primePower p 0 = 1 := by
  ext q
  by_cases h : q = p <;> simp [primePower, h]

@[simp]
theorem primePower_add (p : Nat.Primes) (m n : ℕ∞) :
    primePower p (m + n) = primePower p m * primePower p n := by
  ext q
  by_cases h : q = p <;> simp [primePower, h]

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
  fun q ↦ if q = p then 0 else n q

@[simp]
theorem primeToPart_apply_self (p : Nat.Primes) (n : Supernatural) : primeToPart p n p = 0 := by
  simp [primeToPart]

@[simp]
theorem primeToPart_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : Supernatural) :
    primeToPart p n q = n q := by
  simp [primeToPart, h]

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
  rfl

@[simp]
theorem ofNat_one : ofNat 1 = 1 := by
  ext p
  simp [ofNat]

@[simp]
theorem ofNat_mul (m n : ℕ+) : ofNat (m * n) = ofNat m * ofNat n := by
  ext p
  have h := DFunLike.congr_fun (Nat.factorization_mul m.ne_zero n.ne_zero) (p : ℕ)
  rw [Finsupp.add_apply, Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop,
    Nat.factorization_def _ p.prop] at h
  change (padicValNat (p : ℕ) ((m : ℕ) * n) : ℕ∞) =
    (padicValNat (p : ℕ) m : ℕ∞) + padicValNat (p : ℕ) n
  exact_mod_cast h

/-- Prime factorization embeds positive natural numbers injectively into supernatural numbers. -/
theorem ofNat_injective : Function.Injective ofNat := by
  intro m n h
  apply PNat.eq
  rw [Nat.eq_iff_prime_padicValNat_eq m n m.ne_zero n.ne_zero]
  intro p hp
  let q : Nat.Primes := ⟨p, hp⟩
  exact ENat.natCast_inj.mp (show (padicValNat p m : ℕ∞) = padicValNat p n from congr_fun h q)

/-- The embedding of positive natural numbers as a multiplicative homomorphism. -/
def ofNatMonoidHom : ℕ+ →* Supernatural where
  toFun := ofNat
  map_one' := ofNat_one
  map_mul' := ofNat_mul

@[simp]
theorem ofNatMonoidHom_apply (n : ℕ+) : ofNatMonoidHom n = ofNat n :=
  rfl

/-- Divisibility of positive natural numbers agrees with divisibility of their supernatural
images. -/
theorem ofNat_dvd_ofNat_iff {m n : ℕ+} : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff]
  constructor
  · intro h
    rw [PNat.dvd_iff, ← Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero]
    intro p
    by_cases hp : p.Prime
    · have hv := h ⟨p, hp⟩
      change (padicValNat p m : ℕ∞) ≤ padicValNat p n at hv
      simpa [Nat.factorization_def _ hp] using ENat.natCast_le_natCast.mp hv
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · intro h p
    rw [PNat.dvd_iff, ← Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero] at h
    have hp := h (p : ℕ)
    rw [Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop] at hp
    change (padicValNat p m : ℕ∞) ≤ padicValNat p n
    exact_mod_cast hp

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

/-- Every positive natural number gives a natural supernatural number. -/
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
  simp only [Set.mem_preimage, Finset.mem_coe]
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, Nat.factorization_def _ p.prop]
  change (padicValNat (p : ℕ) n : ℕ∞) ≠ 0 at hp
  exact fun h ↦ hp (congr_arg ((↑) : ℕ → ℕ∞) h)

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
      hsupport.subset fun p hp hzero ↦ hp (by simp [hzero])
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
    let a : ℕ := g.prod (· ^ ·)
    have ha : a ≠ 0 := by
      apply Finsupp.prod_ne_zero_iff.mpr
      intro q hq
      exact pow_ne_zero _ (hgprime q hq).ne_zero
    let m : ℕ+ := ⟨a, Nat.pos_of_ne_zero ha⟩
    refine ⟨m, ?_⟩
    ext p
    have hfactorization : a.factorization = g :=
      Nat.prod_pow_factorization_eq_self hgprime
    have hvaluation : padicValNat p a = ENat.toNat (n p) := by
      rw [← Nat.factorization_def a p.prop, hfactorization]
      exact Finsupp.mapDomain_apply Subtype.val_injective f p
    rw [ofNat_apply]
    exact (congr_arg ((↑) : ℕ → ℕ∞) hvaluation).trans (ENat.natCast_toNat (hfinite p))

/-- A prime power with infinite exponent is not a natural supernatural number. -/
theorem not_isNatural_primePower_top (p : Nat.Primes) : ¬IsNatural (primePower p ⊤) := by
  rw [isNatural_iff]
  push Not
  exact fun _ ↦ ⟨p, by simp⟩

end Supernatural

end TauCeti
