/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# Riemann–Roch spaces

The **Riemann–Roch space** of a divisor `D` of an algebraic function field `F / k` is the
`k`-subspace

`L(D) = {f : F | div f + D ≥ 0}`

of functions whose poles are bounded by `D`, and `ℓ(D) = dim_k L(D)` is its dimension.  This
file constructs `L(D)`, proves the two computations that pin it down at the bottom of the
divisor order, and proves that it is always finite-dimensional with the sharp bound
`ℓ(D) ≤ deg D⁺ + 1` over an exact constant field.  It is Stichtenoth, *Algebraic Function
Fields and Codes*, 2nd ed., Definition 1.4.4 through Definition 1.4.10.

## Main definitions

* `TauCeti.riemannRochSpace`: the Riemann–Roch space `L(D) : Submodule k F` (Definition 1.4.4).
  Its membership condition is the multiplicative `v_P f ≤ exp (D P)`, which is junk-free at
  `f = 0` — no separate `∪ {0}` clause is needed, unlike in the additive `ord_P` form.
* `TauCeti.Divisor.dim`: the dimension `ℓ(D) = dim_k L(D)` (Definition 1.4.10).

## Main results

* `TauCeti.riemannRochSpace_zero`: `L(0)` is the field of constants `algebraicClosure k F` — over
  an exact constant field, `L(0) = k` (`TauCeti.riemannRochSpace_zero_of_isIntegrallyClosedIn`,
  Lemma 1.4.7(a)).
* `TauCeti.riemannRochSpace_eq_bot_of_lt_zero`: `L(D) = 0` for `D < 0` (Lemma 1.4.7(b)).
* `TauCeti.finrank_riemannRochSpace_add_ofPoint_le`: adding one place to a divisor raises `ℓ`
  by at most the degree of that place (Lemma 1.4.8, the one-place-at-a-time estimate).
* `TauCeti.finrank_quotient_riemannRochSpace_le_degree_sub`: for `D ≤ E` the quotient
  `L(E)/L(D)` has dimension at most `deg E - deg D`, equivalently
  `TauCeti.Divisor.dim_le_dim_add_degree_sub`: `ℓ(E) ≤ ℓ(D) + (deg E - deg D)` (Lemma 1.4.8).
* `TauCeti.finiteDimensional_riemannRochSpace` and
  `TauCeti.Divisor.dim_le_degree_posPart_add_one`: `L(D)` is finite-dimensional, with
  `ℓ(D) ≤ deg D⁺ + [algebraicClosure k F : k]` and hence `ℓ(D) ≤ deg D⁺ + 1` over an exact
  constant field (Proposition 1.4.9).

Finite-dimensionality and the estimates leading to it are proved with no hypothesis on the
constant field; only the sharp `+ 1` needs `IsIntegrallyClosedIn k F`.  For a non-exact constant
field the bound genuinely degrades: over `ℝ ⊂ ℂ(x)` already `ℓ(0) = 2`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The **Riemann–Roch space** `L(D)` of a divisor `D` of `F / k` (Stichtenoth,
Definition 1.4.4): the `k`-subspace of functions whose poles are bounded by `D`, that is
`div f + D ≥ 0`.

The membership condition is stated multiplicatively as `v_P f ≤ exp (D P)`.  This is junk-free
at `f = 0`, where the valuation is `0` and the condition holds at every place, so no separate
`∪ {0}` clause is needed; the additive form is
`TauCeti.mem_riemannRochSpace_iff_neg_le_ord`. -/
noncomputable def riemannRochSpace (D : Divisor k F) : Submodule k F where
  carrier := {f : F | ∀ P : Place k F, P.valuation f ≤ WithZero.exp (D.coeff P)}
  add_mem' {a b} ha hb P := (P.valuation.map_add a b).trans (max_le (ha P) (hb P))
  zero_mem' P := by simp
  smul_mem' c f hf P := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [Algebra.smul_def, map_mul, P.isTrivialOn.eq_one c hc, one_mul]
      exact hf P

/-- `ℓ(D) = dim_k L(D)` (Stichtenoth, Definition 1.4.10).  Its finiteness, which guards the
junk value of `Module.finrank`, is `TauCeti.finiteDimensional_riemannRochSpace`. -/
noncomputable def Divisor.dim (D : Divisor k F) : ℕ :=
  Module.finrank k (riemannRochSpace D)

/-- `ℓ(D)` unfolded to the dimension of `L(D)`. -/
theorem Divisor.dim_def (D : Divisor k F) :
    Divisor.dim D = Module.finrank k (riemannRochSpace D) := (rfl)

/-- Membership in `L(D)`, unfolded: the poles of `f` are bounded by `D` at every place. -/
@[simp]
theorem mem_riemannRochSpace_iff {D : Divisor k F} {f : F} :
    f ∈ riemannRochSpace D ↔ ∀ P : Place k F, P.valuation f ≤ WithZero.exp (D.coeff P) :=
  (Iff.rfl)

/-- The additive form of membership in `L(D)`: away from the junk value `ord_P 0 = 0`, the
functions of `L(D)` are those with `ord_P f ≥ -D P` at every place. -/
theorem mem_riemannRochSpace_iff_neg_le_ord {D : Divisor k F} {f : F} (hf : f ≠ 0) :
    f ∈ riemannRochSpace D ↔ ∀ P : Place k F, -D.coeff P ≤ P.ord f := by
  rw [mem_riemannRochSpace_iff]
  refine forall_congr' fun P ↦ ?_
  rw [P.valuation_eq_exp_neg_ord hf, WithZero.exp_le_exp]
  omega

/-- Enlarging a divisor enlarges its Riemann–Roch space (Stichtenoth, Lemma 1.4.8, first
part). -/
theorem riemannRochSpace_mono {D E : Divisor k F} (h : D ≤ E) :
    riemannRochSpace D ≤ riemannRochSpace E := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  exact fun P ↦ (hf P).trans (WithZero.exp_le_exp.mpr (WeilDivisor.coeff_le_coeff h P))

/-- The bundled form of `TauCeti.riemannRochSpace_mono`. -/
theorem riemannRochSpace_monotone :
    Monotone (riemannRochSpace : Divisor k F → Submodule k F) :=
  fun _ _ ↦ riemannRochSpace_mono

/-! ### The two ends of the divisor order -/

/-- **Stichtenoth, Lemma 1.4.7(a)**, without a hypothesis on the constant field: the functions
with no poles at all are exactly the constants `algebraicClosure k F`. -/
theorem mem_riemannRochSpace_zero_iff (hF : IsFunctionField k F) {f : F} :
    f ∈ riemannRochSpace (0 : Divisor k F) ↔ f ∈ algebraicClosure k F := by
  rw [mem_riemannRochSpace_iff, Place.mem_algebraicClosure_iff_forall_mem_integers hF]
  simp [Place.mem_integers_iff]

/-- **Stichtenoth, Lemma 1.4.7(a)**, as an equality of `k`-subspaces of `F`:
`L(0) = algebraicClosure k F`. -/
theorem riemannRochSpace_zero (hF : IsFunctionField k F) :
    riemannRochSpace (0 : Divisor k F) =
      Subalgebra.toSubmodule (algebraicClosure k F).toSubalgebra := by
  ext f
  rw [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
  exact mem_riemannRochSpace_zero_iff hF

/-- **Stichtenoth, Lemma 1.4.7(a)**: over an exact constant field, `L(0) = k`. -/
theorem riemannRochSpace_zero_of_isIntegrallyClosedIn (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    riemannRochSpace (0 : Divisor k F) = LinearMap.range (Algebra.linearMap k F) := by
  rw [riemannRochSpace_zero hF, algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mpr hex]
  ext f
  simp [Algebra.mem_bot, eq_comm]

/-- **Stichtenoth, Lemma 1.4.7(b)**: a divisor that is negative — everywhere at most zero, and
somewhere strictly negative — has no functions at all.  A nonzero `f ∈ L(D)` would have no pole,
hence be a constant, hence have `div f = 0`, contradicting `D < 0`. -/
theorem riemannRochSpace_eq_bot_of_lt_zero (hF : IsFunctionField k F) {D : Divisor k F}
    (hD : D < 0) : riemannRochSpace D = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun f hf ↦ ?_
  by_contra hf0
  have hmem : f ∈ algebraicClosure k F :=
    (mem_riemannRochSpace_zero_iff hF).mp (riemannRochSpace_mono hD.le hf)
  have hzero : ∀ P : Place k F, P.ord f = 0 := fun P ↦
    P.ord_eq_zero_of_isAlgebraic (mem_algebraicClosure_iff.mp hmem)
  refine hD.ne (le_antisymm hD.le (WeilDivisor.le_iff.mpr fun P ↦ ?_))
  have h1 := (mem_riemannRochSpace_iff_neg_le_ord hf0).mp hf P
  rw [hzero P] at h1
  exact neg_nonpos.mp h1

/-! ### The one-place estimate -/

section OnePlace

variable {D : Divisor k F} {P : Place k F} {t : F}

private lemma le_add_ofPoint (D : Divisor k F) (P : Place k F) :
    D ≤ D + WeilDivisor.ofPoint P :=
  le_add_of_nonneg_right
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P))

private lemma coe_algebraMap_integers (P : Place k F) (c : k) :
    ((algebraMap k P.integers c : P.integers) : F) = algebraMap k F c := by
  rw [IsScalarTower.algebraMap_apply k P.integers F, ValuationSubring.algebraMap_apply]

private lemma mul_mem_integers (ht : P.ord t = D.coeff P + 1) (ht0 : t ≠ 0) {x : F}
    (hx : x ∈ riemannRochSpace (D + WeilDivisor.ofPoint P)) : t * x ∈ P.integers := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [P.mem_integers_iff_ord_nonneg, P.ord_mul ht0 hx0, ht]
    have h := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp hx P
    rw [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self] at h
    omega

/-- The evaluation map of Stichtenoth's proof of Lemma 1.4.8: for `t` of order `D P + 1` at `P`,
the map `x ↦ (t · x)(P)` sends `L(D + P)` to the residue field of `P`, and its kernel is
`L(D)`. -/
private noncomputable def residueEval (D : Divisor k F) (P : Place k F) {t : F}
    (ht : P.ord t = D.coeff P + 1) (ht0 : t ≠ 0) :
    riemannRochSpace (D + WeilDivisor.ofPoint P) →ₗ[k] P.ResidueField where
  toFun x := IsScalarTower.toAlgHom k P.integers P.ResidueField
    ⟨t * (x : F), mul_mem_integers ht ht0 x.2⟩
  map_add' x y := by
    rw [← map_add]
    exact congrArg _ (Subtype.ext (by push_cast; ring))
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    exact congrArg _
      (Subtype.ext (by push_cast [Algebra.smul_def, coe_algebraMap_integers]; ring))

private lemma residueEval_apply (ht : P.ord t = D.coeff P + 1) (ht0 : t ≠ 0)
    (x : riemannRochSpace (D + WeilDivisor.ofPoint P)) :
    residueEval D P ht ht0 x =
      IsLocalRing.residue P.integers ⟨t * (x : F), mul_mem_integers ht ht0 x.2⟩ := (rfl)

private lemma mem_riemannRochSpace_iff_residueEval_eq_zero (ht : P.ord t = D.coeff P + 1)
    (ht0 : t ≠ 0) (x : riemannRochSpace (D + WeilDivisor.ofPoint P)) :
    (x : F) ∈ riemannRochSpace D ↔ residueEval D P ht ht0 x = 0 := by
  rcases eq_or_ne (x : F) 0 with hx0 | hx0
  · have hx : x = 0 := Subtype.ext hx0
    simp [hx]
  · have hres : residueEval D P ht ht0 x = 0 ↔ 0 < P.ord (t * (x : F)) := by
      rw [residueEval_apply]
      exact P.residue_eq_zero_iff_ord_pos (f := ⟨t * (x : F), mul_mem_integers ht ht0 x.2⟩)
        (mul_ne_zero ht0 hx0)
    rw [hres, P.ord_mul ht0 hx0, ht, mem_riemannRochSpace_iff_neg_le_ord hx0]
    constructor
    · intro h
      have := h P
      omega
    · intro h Q
      rcases eq_or_ne Q P with rfl | hQ
      · omega
      · have hQ' := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp x.2 Q
        rwa [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_of_ne hQ, add_zero] at hQ'

/-- The kernel of `TauCeti.residueEval` is `L(D)`, sitting inside `L(D + P)` as the comap of the
inclusion `TauCeti.riemannRochSpace_mono`.  This is the structural heart of Stichtenoth's proof of
Lemma 1.4.8. -/
private lemma ker_residueEval (ht : P.ord t = D.coeff P + 1) (ht0 : t ≠ 0) :
    LinearMap.ker (residueEval D P ht ht0) =
      Submodule.comap (riemannRochSpace (D + WeilDivisor.ofPoint P)).subtype
        (riemannRochSpace D) := by
  ext x
  exact (mem_riemannRochSpace_iff_residueEval_eq_zero ht ht0 x).symm

/-- Stichtenoth's proof of Lemma 1.4.8 in its one-place form, carrying both conclusions the two
public statements below project out of: `L(D + P)` stays finite-dimensional, and its dimension
exceeds that of `L(D)` by at most `deg P`.  The evaluation map `x ↦ (t · x)(P)` embeds the
quotient `L(D + P) / L(D)` in the residue field of `P`, for `t` of order `D P + 1` there. -/
private lemma finiteDimensional_and_finrank_add_ofPoint_le (hF : IsFunctionField k F)
    (D : Divisor k F) (P : Place k F) (h : FiniteDimensional k (riemannRochSpace D)) :
    FiniteDimensional k (riemannRochSpace (D + WeilDivisor.ofPoint P)) ∧
      Module.finrank k (riemannRochSpace (D + WeilDivisor.ofPoint P)) ≤
        Module.finrank k (riemannRochSpace D) + P.degree := by
  have : FiniteDimensional k P.ResidueField := Place.finiteDimensional_residueField P hF
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ P.ord t = D.coeff P + 1 := by
    obtain ⟨t, ht⟩ := P.ord_surjective (D.coeff P + 1)
    rcases eq_or_ne t 0 with rfl | ht0
    · exact ⟨1, one_ne_zero, by rw [P.ord_one, ← ht, P.ord_zero]⟩
    · exact ⟨t, ht0, ht⟩
  have hle : riemannRochSpace D ≤ riemannRochSpace (D + WeilDivisor.ofPoint P) :=
    riemannRochSpace_mono (le_add_ofPoint D P)
  have hkerfin : FiniteDimensional k (LinearMap.ker (residueEval D P ht ht0)) := by
    rw [ker_residueEval]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  have hkerrank : Module.finrank k (LinearMap.ker (residueEval D P ht ht0)) =
      Module.finrank k (riemannRochSpace D) := by
    rw [ker_residueEval]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hquotfin : FiniteDimensional k
      (riemannRochSpace (D + WeilDivisor.ofPoint P) ⧸ LinearMap.ker (residueEval D P ht ht0)) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (residueEval D P ht ht0)).symm
  have hfin : FiniteDimensional k (riemannRochSpace (D + WeilDivisor.ofPoint P)) :=
    Module.Finite.of_submodule_quotient (LinearMap.ker (residueEval D P ht ht0))
  refine ⟨hfin, ?_⟩
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.ker (residueEval D P ht ht0))
  have hrange : Module.finrank k
      (riemannRochSpace (D + WeilDivisor.ofPoint P) ⧸ LinearMap.ker (residueEval D P ht ht0)) ≤
        P.degree := by
    rw [(LinearMap.quotKerEquivRange (residueEval D P ht ht0)).finrank_eq, Place.degree_eq_finrank]
    exact Submodule.finrank_le _
  omega

/-- Adding one place to a divisor keeps its Riemann–Roch space finite-dimensional. -/
theorem finiteDimensional_riemannRochSpace_add_ofPoint (hF : IsFunctionField k F)
    (D : Divisor k F) (P : Place k F) (h : FiniteDimensional k (riemannRochSpace D)) :
    FiniteDimensional k (riemannRochSpace (D + WeilDivisor.ofPoint P)) :=
  (finiteDimensional_and_finrank_add_ofPoint_le hF D P h).1

/-- **Stichtenoth, Lemma 1.4.8**, in its one-place form: passing from `D` to `D + P` raises the
dimension of the Riemann–Roch space by at most `deg P`.  The proof embeds the quotient
`L(D + P) / L(D)` in the residue field of `P` by evaluating `t · f` at `P`, for `t` a function
of order `D P + 1` there. -/
theorem finrank_riemannRochSpace_add_ofPoint_le (hF : IsFunctionField k F) (D : Divisor k F)
    (P : Place k F) (h : FiniteDimensional k (riemannRochSpace D)) :
    Module.finrank k (riemannRochSpace (D + WeilDivisor.ofPoint P)) ≤
      Module.finrank k (riemannRochSpace D) + P.degree :=
  (finiteDimensional_and_finrank_add_ofPoint_le hF D P h).2

end OnePlace

/-! ### Finite-dimensionality -/

/-- `ℓ(0) = [algebraicClosure k F : k]`: the functions without poles are the constants. -/
theorem Divisor.dim_zero (hF : IsFunctionField k F) :
    Divisor.dim (0 : Divisor k F) = Module.finrank k (algebraicClosure k F) := by
  rw [Divisor.dim_def, riemannRochSpace_zero hF, Subalgebra.finrank_toSubmodule]
  rfl

/-- `L(0) = algebraicClosure k F` is finite-dimensional: the constants form a finite extension of
`k` (Stichtenoth, Corollary 1.1.16). -/
theorem finiteDimensional_riemannRochSpace_zero (hF : IsFunctionField k F) :
    FiniteDimensional k (riemannRochSpace (0 : Divisor k F)) := by
  have := hF.finiteDimensional_algebraicClosure
  rw [riemannRochSpace_zero hF]
  exact inferInstanceAs (FiniteDimensional k (algebraicClosure k F))

/-- The engine of Stichtenoth's Lemma 1.4.8 and Proposition 1.4.9: an induction that walks from
`D` up to `E` one place at a time, the number of steps being controlled by the difference of the
degrees because every place has degree at least one. -/
private lemma finiteDimensional_and_finrank_le_of_le (hF : IsFunctionField k F) :
    ∀ (m : ℕ) (D E : Divisor k F), D ≤ E → (Divisor.degree E - Divisor.degree D).toNat ≤ m →
      FiniteDimensional k (riemannRochSpace D) →
        FiniteDimensional k (riemannRochSpace E) ∧
          (Module.finrank k (riemannRochSpace E) : ℤ) ≤
            Module.finrank k (riemannRochSpace D) +
              (Divisor.degree E - Divisor.degree D) := by
  intro m
  induction m with
  | zero =>
    intro D E hDE hm hfin
    have hd : Divisor.degree D ≤ Divisor.degree E := Divisor.degree_le_of_le hDE
    have hDE' : D = E := Divisor.eq_of_le_of_degree_eq hF hDE (by omega)
    subst hDE'
    exact ⟨hfin, by omega⟩
  | succ m ih =>
    intro D E hDE hm hfin
    have hd : Divisor.degree D ≤ Divisor.degree E := Divisor.degree_le_of_le hDE
    rcases eq_or_ne D E with rfl | hne
    · exact ⟨hfin, by omega⟩
    obtain ⟨P, hP⟩ : ∃ P : Place k F, D.coeff P < E.coeff P := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hne (WeilDivisor.ext fun P ↦ le_antisymm (WeilDivisor.coeff_le_coeff hDE P) (hcon P))
    have hPdeg : 1 ≤ (P.degree : ℤ) := by
      exact_mod_cast P.one_le_degree_of_isFunctionField hF
    have hstep : D + WeilDivisor.ofPoint P ≤ E := WeilDivisor.le_iff.mpr fun Q ↦ by
      rcases eq_or_ne Q P with rfl | hQ
      · rw [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_self]
        omega
      · rw [WeilDivisor.coeff_add, WeilDivisor.coeff_ofPoint_of_ne hQ, add_zero]
        exact WeilDivisor.coeff_le_coeff hDE Q
    have hdeg : Divisor.degree (D + WeilDivisor.ofPoint P) =
        Divisor.degree D + (P.degree : ℤ) := by
      rw [Divisor.degree_add, Divisor.degree_ofPoint]
    have hfin' := finiteDimensional_riemannRochSpace_add_ofPoint hF D P hfin
    have hrank := finrank_riemannRochSpace_add_ofPoint_le hF D P hfin
    obtain ⟨hfinE, hleE⟩ := ih (D + WeilDivisor.ofPoint P) E hstep (by omega) hfin'
    exact ⟨hfinE, by omega⟩

/-- **Stichtenoth, Proposition 1.4.9**: the Riemann–Roch space of any divisor is
finite-dimensional over the constants.  No hypothesis on the constant field is needed here: the
constants `algebraicClosure k F` form a finite extension of `k` and
`L(0) = algebraicClosure k F`, and the estimate walking up from `0` to `D⁺` is hypothesis-free. -/
theorem finiteDimensional_riemannRochSpace (hF : IsFunctionField k F) (D : Divisor k F) :
    FiniteDimensional k (riemannRochSpace D) := by
  have := (finiteDimensional_and_finrank_le_of_le hF
    (Divisor.degree D⁺ - Divisor.degree (0 : Divisor k F)).toNat 0 D⁺
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_posPart D)) le_rfl
    (finiteDimensional_riemannRochSpace_zero hF)).1
  exact Submodule.finiteDimensional_of_le (riemannRochSpace_mono (le_posPart D))

/-- The Riemann–Roch dimension is zero exactly when the Riemann–Roch space is zero. -/
theorem Divisor.dim_eq_zero_iff_riemannRochSpace_eq_bot (hF : IsFunctionField k F)
    (D : Divisor k F) : Divisor.dim D = 0 ↔ riemannRochSpace D = ⊥ := by
  let _ := finiteDimensional_riemannRochSpace hF D
  rw [Divisor.dim_def, Submodule.finrank_eq_zero]

/-- The Riemann–Roch dimension is positive exactly when the Riemann–Roch space is nonzero. -/
theorem Divisor.one_le_dim_iff_riemannRochSpace_ne_bot (hF : IsFunctionField k F)
    (D : Divisor k F) : 1 ≤ Divisor.dim D ↔ riemannRochSpace D ≠ ⊥ := by
  let _ := finiteDimensional_riemannRochSpace hF D
  rw [Divisor.dim_def, Submodule.one_le_finrank_iff]

/-- `ℓ` is monotone in the divisor (Stichtenoth, Lemma 1.4.8, first part). -/
theorem Divisor.dim_mono (hF : IsFunctionField k F) {D E : Divisor k F} (h : D ≤ E) :
    Divisor.dim D ≤ Divisor.dim E := by
  have := finiteDimensional_riemannRochSpace hF E
  exact Submodule.finrank_mono (riemannRochSpace_mono h)

/-- **Stichtenoth, Lemma 1.4.8**: enlarging a divisor raises `ℓ` by at most the increase in
degree.  Stichtenoth states this as `dim (L(E)/L(D)) ≤ deg E - deg D`; the two forms agree
because `L(D)` is finite-dimensional. -/
theorem Divisor.dim_le_dim_add_degree_sub (hF : IsFunctionField k F) {D E : Divisor k F}
    (h : D ≤ E) :
    (Divisor.dim E : ℤ) ≤ Divisor.dim D + (Divisor.degree E - Divisor.degree D) :=
  (finiteDimensional_and_finrank_le_of_le hF (Divisor.degree E - Divisor.degree D).toNat D E h
    le_rfl (finiteDimensional_riemannRochSpace hF D)).2

/-- **Stichtenoth, Lemma 1.4.8** in the quotient form Stichtenoth states it in: for `D ≤ E` the
quotient `L(E) / L(D)` has dimension at most `deg E - deg D`.  Inside `L(E)` the subspace `L(D)`
is the comap along the subtype map of the inclusion `TauCeti.riemannRochSpace_mono`; the
arithmetic form of the same bound is `TauCeti.Divisor.dim_le_dim_add_degree_sub`. -/
theorem finrank_quotient_riemannRochSpace_le_degree_sub (hF : IsFunctionField k F)
    {D E : Divisor k F} (h : D ≤ E) :
    (Module.finrank k (riemannRochSpace E ⧸
        Submodule.comap (riemannRochSpace E).subtype (riemannRochSpace D)) : ℤ) ≤
      Divisor.degree E - Divisor.degree D := by
  have := finiteDimensional_riemannRochSpace hF E
  have hsub : Module.finrank k
      (Submodule.comap (riemannRochSpace E).subtype (riemannRochSpace D)) = Divisor.dim D :=
    (Submodule.comapSubtypeEquivOfLe (riemannRochSpace_mono h)).finrank_eq.trans
      (Divisor.dim_def D).symm
  have hquot := Submodule.finrank_quotient_add_finrank
    (Submodule.comap (riemannRochSpace E).subtype (riemannRochSpace D))
  have hE : Module.finrank k (riemannRochSpace E) = Divisor.dim E := (Divisor.dim_def E).symm
  have hle := Divisor.dim_le_dim_add_degree_sub hF h
  omega

/-- **Stichtenoth, Proposition 1.4.9**, with the bound for a general constant field:
`ℓ(D) ≤ deg D⁺ + [algebraicClosure k F : k]`. -/
theorem Divisor.dim_le_degree_posPart_add_finrank (hF : IsFunctionField k F) (D : Divisor k F) :
    (Divisor.dim D : ℤ) ≤
      Divisor.degree D⁺ + Module.finrank k (algebraicClosure k F) := by
  have hmono : Divisor.dim D ≤ Divisor.dim D⁺ := Divisor.dim_mono hF (le_posPart D)
  have h := Divisor.dim_le_dim_add_degree_sub hF
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_posPart D))
  rw [Divisor.dim_zero hF, Divisor.degree_zero] at h
  omega

/-- **Stichtenoth, Proposition 1.4.9**: over an exact constant field the Riemann–Roch space of
`D` has dimension at most `deg D⁺ + 1`.  In particular `ℓ(D) ≤ deg D + 1` for effective `D`. -/
theorem Divisor.dim_le_degree_posPart_add_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (D : Divisor k F) :
    (Divisor.dim D : ℤ) ≤ Divisor.degree D⁺ + 1 := by
  have h := Divisor.dim_le_degree_posPart_add_finrank hF D
  rwa [isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex] at h

/-- Over an exact constant field `ℓ(0) = 1`: the only functions without poles are the
constants. -/
theorem Divisor.dim_zero_of_isIntegrallyClosedIn (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) : Divisor.dim (0 : Divisor k F) = 1 := by
  rw [Divisor.dim_zero hF]
  exact isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex

/-- `ℓ(D) = 0` for a negative divisor (Stichtenoth, Lemma 1.4.7(b)). -/
theorem Divisor.dim_eq_zero_of_lt_zero (hF : IsFunctionField k F) {D : Divisor k F} (hD : D < 0) :
    Divisor.dim D = 0 := by
  exact (Divisor.dim_eq_zero_iff_riemannRochSpace_eq_bot hF D).mpr
    (riemannRochSpace_eq_bot_of_lt_zero hF hD)

end TauCeti
