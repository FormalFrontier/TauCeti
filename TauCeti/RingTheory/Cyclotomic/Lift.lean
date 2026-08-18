/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.Data.ZMod.ValMinAbs
public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Lifting an exact cyclotomic integer out of its residues at the conjugate roots

`TauCeti.Cyclotomic.reduce p r` evaluates an exact cyclotomic integer at a residue `r`, and when
`r` is a primitive `e`-th root of unity modulo `p` that evaluation is a ring homomorphism
`ℤ[ζ_e] → ZMod p` (`TauCeti.Cyclotomic.reduceRingHom`).  A single such residue loses far too much
to be inverted: it is one linear condition on the `e.totient` coordinates.  What can be inverted is
the whole tuple of residues at *all* the primitive `e`-th roots modulo `p`, that is, the residues
of all the Galois conjugates `σ_k x`, `σ_k : ζ ↦ ζ ^ k` for `k` coprime to `e`.  This file inverts
it.

Fix a primitive `e`-th root `α : ZMod p`.  The conjugate roots are the powers `α ^ k` for the
`e.totient` exponents `k < e` coprime to `e` (`TauCeti.Cyclotomic.primitiveExponents`), and they
are pairwise distinct, so the matrix `(α ^ k) ^ j` of the resulting evaluation map is a
**Vandermonde matrix with distinct nodes** and hence invertible over the field `ZMod p`.  Two
consequences follow.

* **Reconstruction.** Inverting the Vandermonde matrix and taking the balanced representative
  `ZMod.valMinAbs` of each resulting residue is an actual computation
  (`TauCeti.Cyclotomic.lift`), and it returns the element it came from as soon as that element's
  coordinates have absolute value less than `p / 2` (`TauCeti.Cyclotomic.lift_conjugateResidues`).
* **Uniqueness.** Two elements with coordinates in that window and the same residue tuple are
  therefore both returned by the lift from it, hence equal
  (`TauCeti.Cyclotomic.eq_of_conjugateResidues_eq`).

This is the lift of the Burnside--Dixon--Schneider algorithm, whose modular phase produces the
central character table as residues modulo a good Dixon prime and whose output is exact.  Every
statement below is *conditional* on the coordinate bound: the bound is a hypothesis here, never a
conclusion.  What a good Dixon prime contributes is the other two ingredients: the condition
`Monoid.exponent G ∣ p - 1` provides the primitive root `α`, and Dixon's size bound `2⌊√|G|⌋ < p`
converts a coordinate bound of `⌊√|G|⌋` into the residue window.  That the values the algorithm
reconstructs do have coordinates that small is *not* claimed anywhere here: it is unverified, it is
proved nowhere in this repository, and the roadmap records the precise constant in Dixon's `2√|G|`
as low-confidence pending a re-check against Dixon 1967.  A caller has to supply that bound as a
hypothesis.  Nothing about groups appears here, only the arithmetic.

The lift is *not* a bare map `ZMod p → ℤ[ζ_e]`: a single residue underdetermines an algebraic
integer, and because a good Dixon prime satisfies `p ≡ 1 (mod e)` the Frobenius acts trivially on
`ζ_e` modulo `p`, so no Frobenius orbit is available to make up the deficit.  The data that does
determine the element is the tuple of residues at all the conjugate roots, which is what
`TauCeti.Cyclotomic.conjugateResidues` records.

## Main definitions

* `TauCeti.Cyclotomic.primitiveExponents`: the exponents below `e` coprime to `e`, indexing the
  Galois group `(ZMod e)ˣ` of `ℚ(ζ_e)` by the power maps `σ_k : ζ ↦ ζ ^ k`.
* `TauCeti.Cyclotomic.conjugateRoot`: the primitive `e`-th root `α ^ k` modulo `p`, at which the
  `k`-th Galois conjugate is read.
* `TauCeti.Cyclotomic.conjugateResidues`: the residue tuple of an exact cyclotomic integer,
  a ring homomorphism into `Fin e.totient → ZMod p` by
  `TauCeti.Cyclotomic.conjugateResiduesRingHom`.
* `TauCeti.Cyclotomic.lift`: the exact cyclotomic integer reconstructed from a residue tuple.

## Main results

* `TauCeti.Cyclotomic.lift_conjugateResidues` and
  `TauCeti.Cyclotomic.lift_eq_of_conjugateResidues_eq`: **correctness of the lift**, it returns any
  element whose coordinates lie in the residue window from that element's residue tuple.
* `TauCeti.Cyclotomic.eq_of_conjugateResidues_eq`: **uniqueness**, two exact cyclotomic integers
  with coordinates inside the residue window and the same residue tuple are equal.
* `TauCeti.Cyclotomic.conjugateResidues_lift`: the lift is a section of the residue tuple, with no
  hypothesis on the tuple at all.

## Implementation notes

The residue tuple is indexed by `Fin e.totient` through the explicit increasing enumeration
`TauCeti.Cyclotomic.primitiveExponents` of the exponents coprime to `e`, rather than by the Galois
group `(ZMod e)ˣ` itself.  The two index sets have the same size, and
`TauCeti.Cyclotomic.mem_primitiveExponents_iff` identifies the enumerated exponents; the concrete
index is what lets the Vandermonde matrix be a square matrix over `Fin e.totient` matching the
coordinate vector, and what keeps `TauCeti.Cyclotomic.lift` a computation rather than a choice.

Inversion is by Cramer's rule, `det⁻¹ • Matrix.cramer`, rather than by `Matrix.inv`, whose
`Ring.inverse` is noncomputable.  `TauCeti.Cyclotomic.lift` is therefore a genuine `def` that the
compiler runs; it is not reducible by the *kernel*, because `ZMod.inv` is `Nat.gcdA`, whose
well-founded recursion does not unfold there.  That is a property of the inverse of `ZMod p`, not
of the lift, and it is why the examples at the end of this file reach a concrete value of the lift
through `TauCeti.Cyclotomic.lift_conjugateResidues` rather than by `decide`.

No definition in this file is `@[expose]`: downstream code is meant to use the lemmas rather than
the representations, that is `TauCeti.Cyclotomic.mem_primitiveExponents_iff` and
`TauCeti.Cyclotomic.primitiveExponent_eq_getElem` for the exponents,
`TauCeti.Cyclotomic.conjugateRoot_def` for the conjugate roots,
`TauCeti.Cyclotomic.conjugateResidues_apply` and `TauCeti.Cyclotomic.conjugateResiduesRingHom` for
the residue tuple, and `TauCeti.Cyclotomic.coeff_lift` with the correctness, uniqueness and section
theorems for the lift.  `TauCeti.Cyclotomic.conjugateVandermonde` and
`TauCeti.Cyclotomic.liftResidues`, the linear algebra the lift runs on, stay public declarations
none the less, because `TauCeti.Cyclotomic.coeff_lift` — the coordinate formula, which is public
interface — is stated in terms of `TauCeti.Cyclotomic.liftResidues`.  Each of the two is described
by a lemma rather than by its body: `TauCeti.Cyclotomic.conjugateVandermonde_apply` gives the
matrix entries, and `TauCeti.Cyclotomic.conjugateVandermonde_mulVec_liftResidues` says that the
recovered coordinate vector solves the Vandermonde system, which determines it since that system
is invertible.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "The structured cyclotomic lift",
  whose `liftCyclotomic` and `liftCyclotomic_spec` are `TauCeti.Cyclotomic.lift` and
  `TauCeti.Cyclotomic.lift_eq_of_conjugateResidues_eq` here.
-/

public section

open Matrix Polynomial

namespace TauCeti

namespace Cyclotomic

variable {e p : ℕ}

/-! ## The exponents of the Galois conjugates -/

/-- The exponents `k < e` coprime to `e`, in increasing order.  These index the Galois group of
`ℚ(ζ_e)` over `ℚ` by the power maps `σ_k : ζ ↦ ζ ^ k`, and there are `e.totient` of them. -/
def primitiveExponents (e : ℕ) : List ℕ :=
  (List.range e).filter fun k => e.Coprime k

/-- The enumerated exponents are exactly the residues below `e` coprime to it. -/
@[simp]
theorem mem_primitiveExponents_iff {e k : ℕ} :
    k ∈ primitiveExponents e ↔ k < e ∧ e.Coprime k := by
  simp [primitiveExponents]

/-- The exponents are enumerated without repetition, since `List.range` is. -/
theorem nodup_primitiveExponents (e : ℕ) : (primitiveExponents e).Nodup :=
  (List.nodup_range).filter _

/-- There are `e.totient` exponents coprime to `e`: filtering `List.range e` for coprimality is
literally the definition of `Nat.totient`. -/
@[simp]
theorem length_primitiveExponents (e : ℕ) : (primitiveExponents e).length = e.totient := by
  rw [primitiveExponents]
  rfl

/-- The `j`-th exponent coprime to `e`. -/
def primitiveExponent (e : ℕ) (j : Fin e.totient) : ℕ :=
  (primitiveExponents e).getD j 0

/-- The `j`-th exponent coprime to `e`, read as a list index rather than through the default
value of `List.getD`. -/
theorem primitiveExponent_eq_getElem (e : ℕ) (j : Fin e.totient) :
    primitiveExponent e j = (primitiveExponents e)[(j : ℕ)]'(by simp [j.isLt]) :=
  List.getD_eq_getElem _ _ _

/-- Every `TauCeti.Cyclotomic.primitiveExponent` is one of the enumerated exponents. -/
theorem primitiveExponent_mem (e : ℕ) (j : Fin e.totient) :
    primitiveExponent e j ∈ primitiveExponents e := by
  rw [primitiveExponent_eq_getElem]
  exact List.getElem_mem _

/-- The exponents coprime to `e` are taken from below `e`, so distinct indices give powers of `α`
that a primitive `e`-th root separates. -/
theorem primitiveExponent_lt (e : ℕ) (j : Fin e.totient) : primitiveExponent e j < e :=
  (mem_primitiveExponents_iff.1 (primitiveExponent_mem e j)).1

/-- The enumerated exponents are coprime to `e`, so the powers of `ζ` by them are again primitive
`e`-th roots of unity. -/
theorem coprime_primitiveExponent (e : ℕ) (j : Fin e.totient) :
    e.Coprime (primitiveExponent e j) :=
  (mem_primitiveExponents_iff.1 (primitiveExponent_mem e j)).2

/-- Distinct indices name distinct exponents, because the enumeration has no repetitions. -/
theorem primitiveExponent_injective (e : ℕ) : Function.Injective (primitiveExponent e) := by
  intro i j h
  rw [primitiveExponent_eq_getElem, primitiveExponent_eq_getElem,
    (nodup_primitiveExponents e).getElem_inj_iff] at h
  exact Fin.ext h

/-! ## The conjugate roots and the residue tuple -/

/-- The `j`-th conjugate root modulo `p`: the power `α ^ k` of `α` by the `j`-th exponent coprime
to `e`.  Evaluating at it reads off the residue of the `j`-th Galois conjugate. -/
def conjugateRoot (e : ℕ) {p : ℕ} (α : ZMod p) (j : Fin e.totient) : ZMod p :=
  α ^ primitiveExponent e j

/-- The `j`-th conjugate root is the power of `α` by the `j`-th exponent coprime to `e`. -/
@[simp]
theorem conjugateRoot_def (e : ℕ) (α : ZMod p) (j : Fin e.totient) :
    conjugateRoot e α j = α ^ primitiveExponent e j := by
  rw [conjugateRoot]

/-- Every conjugate root is itself a primitive `e`-th root of unity, which is why evaluating at it
is a ring homomorphism out of the exact cyclotomic integers. -/
theorem isPrimitiveRoot_conjugateRoot {α : ZMod p} (hα : IsPrimitiveRoot α e)
    (j : Fin e.totient) : IsPrimitiveRoot (conjugateRoot e α j) e :=
  hα.pow_of_coprime _ (coprime_primitiveExponent e j).symm

/-- **The conjugate roots are pairwise distinct.**  This is what makes the Vandermonde matrix of
the evaluation map invertible, and hence the residue tuple invertible. -/
theorem conjugateRoot_injective {α : ZMod p} (hα : IsPrimitiveRoot α e) :
    Function.Injective (conjugateRoot e α) := fun i j h =>
  primitiveExponent_injective e
    (hα.pow_inj (primitiveExponent_lt e i) (primitiveExponent_lt e j) h)

/-- The residues of `x` at the `e.totient` conjugate roots: the images of the Galois conjugates
`σ_k x` in `ZMod p`, the data the modular phase of a character-table computation produces. -/
def conjugateResidues {e p : ℕ} (α : ZMod p) (x : Cyclotomic e) :
    Fin e.totient → ZMod p :=
  fun j => reduce p (conjugateRoot e α j) x

/-- A single coordinate of the residue tuple is the reduction at the matching conjugate root. -/
@[simp]
theorem conjugateResidues_apply {α : ZMod p} (x : Cyclotomic e) (j : Fin e.totient) :
    conjugateResidues α x j = reduce p (conjugateRoot e α j) x := by
  rw [conjugateResidues]

/-- **The residue tuple is a ring homomorphism.**  Each component is reduction at a conjugate
root, which is again a primitive `e`-th root of unity, so the tuple is a ring homomorphism into
the product ring `Fin e.totient → ZMod p`.  The `map_*` lemmas below are the componentwise form
of this. -/
noncomputable def conjugateResiduesRingHom [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) : Cyclotomic e →+* (Fin e.totient → ZMod p) :=
  RingHom.pi fun j => reduceRingHom p (conjugateRoot e α j) (isPrimitiveRoot_conjugateRoot hα j)

/-- The bundled residue tuple is the residue tuple. -/
@[simp]
theorem conjugateResiduesRingHom_apply [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (x : Cyclotomic e) :
    conjugateResiduesRingHom hα x = conjugateResidues α x :=
  funext fun _ => reduceRingHom_apply _ _ _ _

/-- The residue tuple of `0` is `0`.  Unlike the other componentwise rules this needs no
primitive root: every coordinate of `0` vanishes, so every residue does. -/
@[simp]
theorem conjugateResidues_zero {α : ZMod p} : conjugateResidues α (0 : Cyclotomic e) = 0 := by
  funext j
  rw [conjugateResidues_apply, reduce_eq_sum]
  simp

/-- The residue tuple of `1` is `1`. -/
@[simp]
theorem conjugateResidues_one [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) : conjugateResidues α (1 : Cyclotomic e) = 1 := by
  rw [← conjugateResiduesRingHom_apply hα, map_one]

/-- Residue tuples add. -/
@[simp]
theorem conjugateResidues_add [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (x y : Cyclotomic e) :
    conjugateResidues α (x + y) = conjugateResidues α x + conjugateResidues α y := by
  rw [← conjugateResiduesRingHom_apply hα, map_add, conjugateResiduesRingHom_apply,
    conjugateResiduesRingHom_apply]

/-- Residue tuples negate. -/
@[simp]
theorem conjugateResidues_neg [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (x : Cyclotomic e) :
    conjugateResidues α (-x) = -conjugateResidues α x := by
  rw [← conjugateResiduesRingHom_apply hα, map_neg, conjugateResiduesRingHom_apply]

/-- Residue tuples multiply. -/
@[simp]
theorem conjugateResidues_mul [Fact p.Prime] [NeZero e] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (x y : Cyclotomic e) :
    conjugateResidues α (x * y) = conjugateResidues α x * conjugateResidues α y := by
  rw [← conjugateResiduesRingHom_apply hα, map_mul, conjugateResiduesRingHom_apply,
    conjugateResiduesRingHom_apply]

/-! ## Evaluation as a Vandermonde system -/

/-- The Vandermonde matrix of the conjugate roots: the matrix of the map taking the coordinate
vector of an exact cyclotomic integer to its residue tuple. -/
def conjugateVandermonde (e : ℕ) {p : ℕ} (α : ZMod p) :
    Matrix (Fin e.totient) (Fin e.totient) (ZMod p) :=
  Matrix.vandermonde (conjugateRoot e α)

/-- The entries of the Vandermonde matrix are the powers of the conjugate roots: its `i`-th row
reads the coordinate vector against the powers of the `i`-th conjugate root. -/
@[simp]
theorem conjugateVandermonde_apply (e : ℕ) (α : ZMod p) (i j : Fin e.totient) :
    conjugateVandermonde e α i j = conjugateRoot e α i ^ (j : ℕ) := by
  rw [conjugateVandermonde, Matrix.vandermonde_apply]

/-- **The Vandermonde matrix of the conjugate roots is invertible**, because those roots are
pairwise distinct. -/
theorem det_conjugateVandermonde_ne_zero [Fact p.Prime] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) : (conjugateVandermonde e α).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.2 (conjugateRoot_injective hα)

/-- The residue tuple is the Vandermonde matrix applied to the reduced coordinate vector. -/
theorem conjugateVandermonde_mulVec (α : ZMod p) (x : Cyclotomic e) :
    conjugateVandermonde e α *ᵥ (fun j => ((x.coeff j : ℤ) : ZMod p)) = conjugateResidues α x := by
  funext i
  rw [conjugateResidues_apply, reduce_eq_sum, Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply, conjugateVandermonde, Matrix.vandermonde_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ## The lift -/

/-- The reduced coordinate vector recovered from a residue tuple, by **Cramer's rule** for the
Vandermonde matrix of the conjugate roots. -/
def liftResidues (e : ℕ) {p : ℕ} (α : ZMod p) (r : Fin e.totient → ZMod p) :
    Fin e.totient → ZMod p :=
  ((conjugateVandermonde e α).det)⁻¹ • Matrix.cramer (conjugateVandermonde e α) r

/-- **The recovered coordinate vector solves the Vandermonde system it was recovered from.**  This
characterizes `TauCeti.Cyclotomic.liftResidues`, the matrix of the system being invertible, and is
what Cramer's rule is used for. -/
theorem conjugateVandermonde_mulVec_liftResidues [Fact p.Prime] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (r : Fin e.totient → ZMod p) :
    conjugateVandermonde e α *ᵥ liftResidues e α r = r := by
  rw [liftResidues, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    inv_smul_smul₀ (det_conjugateVandermonde_ne_zero hα)]

/-- **The lift.**  The exact cyclotomic integer whose coordinates are the balanced representatives
of the coordinate residues recovered from `r`.  This is a computation on the coefficient vector:
the determinants Cramer's rule takes, the inverse in `ZMod p` and `ZMod.valMinAbs` all are. -/
def lift (e : ℕ) {p : ℕ} (α : ZMod p) (r : Fin e.totient → ZMod p) : Cyclotomic e :=
  ⟨(List.ofFn fun j => (liftResidues e α r j).valMinAbs).reverse, by simp⟩

/-- The coefficient list of the lift, in the descending order `TauCeti.Cyclotomic.coeffs` uses. -/
theorem coeffs_lift (e : ℕ) (α : ZMod p) (r : Fin e.totient → ZMod p) :
    (lift e α r).coeffs = (List.ofFn fun j => (liftResidues e α r j).valMinAbs).reverse := by
  rw [lift]
  rfl

/-- The coordinates of the lift are the balanced representatives of the recovered residues. -/
@[simp]
theorem coeff_lift (e : ℕ) (α : ZMod p) (r : Fin e.totient → ZMod p) (j : Fin e.totient) :
    (lift e α r).coeff j = (liftResidues e α r j).valMinAbs := by
  rw [coeff, coeffs_lift, List.reverse_reverse, List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]

/-- Inverting the Vandermonde system returns the reduced coordinates it was built from. -/
@[simp]
theorem liftResidues_conjugateResidues [Fact p.Prime] {α : ZMod p} (hα : IsPrimitiveRoot α e)
    (x : Cyclotomic e) (j : Fin e.totient) :
    liftResidues e α (conjugateResidues α x) j = ((x.coeff j : ℤ) : ZMod p) := by
  have h : Matrix.cramer (conjugateVandermonde e α) (conjugateResidues α x)
      = (conjugateVandermonde e α).det • fun j : Fin e.totient => ((x.coeff j : ℤ) : ZMod p) := by
    rw [← conjugateVandermonde_mulVec, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [liftResidues, h, inv_smul_smul₀ (det_conjugateVandermonde_ne_zero hα)]

/-- **The lift is correct.**  An exact cyclotomic integer whose coordinates lie in the residue
window is returned by the lift from its own residue tuple. -/
@[simp]
theorem lift_conjugateResidues [Fact p.Prime] {α : ZMod p} (hα : IsPrimitiveRoot α e)
    {x : Cyclotomic e} (hx : ∀ j : Fin e.totient, 2 * (x.coeff j).natAbs < p) :
    lift e α (conjugateResidues α x) = x := by
  refine ext fun j => ?_
  rw [coeff_lift, liftResidues_conjugateResidues hα,
    TauCeti.ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt (hx j)]

/-- **The specification of the lift.**  Whenever a residue tuple comes from an exact cyclotomic
integer whose coordinates lie in the residue window, the lift returns that integer; by
`TauCeti.Cyclotomic.eq_of_conjugateResidues_eq` there is at most one such integer, so this
determines the answer. -/
theorem lift_eq_of_conjugateResidues_eq [Fact p.Prime] {α : ZMod p} (hα : IsPrimitiveRoot α e)
    {r : Fin e.totient → ZMod p} {x : Cyclotomic e}
    (hx : ∀ j : Fin e.totient, 2 * (x.coeff j).natAbs < p)
    (hr : conjugateResidues α x = r) : lift e α r = x := by
  subst hr
  exact lift_conjugateResidues hα hx

/-- **An exact cyclotomic integer whose coordinates lie in the residue window is determined by its
residue tuple.**  Both elements are returned by the lift from the tuple they share, so this is
uniqueness read off the correctness of the lift; the mathematical content is the invertibility of
the Vandermonde matrix of the conjugate roots together with the residue window. -/
theorem eq_of_conjugateResidues_eq [Fact p.Prime] {α : ZMod p} (hα : IsPrimitiveRoot α e)
    {x y : Cyclotomic e} (hx : ∀ j : Fin e.totient, 2 * (x.coeff j).natAbs < p)
    (hy : ∀ j : Fin e.totient, 2 * (y.coeff j).natAbs < p)
    (h : conjugateResidues α x = conjugateResidues α y) : x = y := by
  rw [← lift_conjugateResidues hα hx, h, lift_conjugateResidues hα hy]

/-- **The lift is a section of the residue tuple.**  Unlike its correctness, this needs no bound:
whatever residue tuple it is given, the element it returns has exactly those residues.  It is the
statement that a residue tuple is always realized, and only the size of the coordinates is at
stake in the correctness above. -/
@[simp]
theorem conjugateResidues_lift [Fact p.Prime] {α : ZMod p} (hα : IsPrimitiveRoot α e)
    (r : Fin e.totient → ZMod p) : conjugateResidues α (lift e α r) = r := by
  have hc : (fun j : Fin e.totient => (((lift e α r).coeff j : ℤ) : ZMod p))
      = liftResidues e α r := by
    funext j
    rw [coeff_lift]
    exact ZMod.coe_valMinAbs _
  rw [← conjugateVandermonde_mulVec, hc, conjugateVandermonde_mulVec_liftResidues hα]

/-! ## Worked examples

In `Cyclotomic 4` the exponents coprime to `4` are `1` and `3`, so the two conjugate roots modulo
`5` are `2 ^ 1 = 2` and `2 ^ 3 = 3`, at which `ζ + 1` has residues `3` and `4`. -/

example : primitiveExponents 4 = [1, 3] := by decide

example : List.ofFn (conjugateResidues (2 : ZMod 5) (zeta 4 + 1)) = [3, 4] := by decide

/-! The lift itself is not reducible by the kernel, but it can still be run against a concrete
element through its correctness theorem, which is where the hypotheses become concrete: for the
two small conductors the roadmap stages before the general one, `e = 4` (the Gaussian integers)
and `e = 3` (the Eisenstein integers), both the primitivity of the root and the coordinate bound
are settled by `decide`. -/

example : lift 4 (2 : ZMod 5) (conjugateResidues (2 : ZMod 5) (zeta 4 + 1)) = zeta 4 + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact lift_conjugateResidues
    (.mk_of_lt 2 (by decide) (by decide) fun l hl0 hl4 => by interval_cases l <;> decide)
    (by decide)

example : lift 3 (2 : ZMod 7) (conjugateResidues (2 : ZMod 7) (zeta 3 + 2)) = zeta 3 + 2 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact lift_conjugateResidues
    (.mk_of_lt 2 (by decide) (by decide) fun l hl0 hl3 => by interval_cases l <;> decide)
    (by decide)

end Cyclotomic

end TauCeti
