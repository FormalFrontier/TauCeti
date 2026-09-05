/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The zero locus of a nonzero multivariate polynomial is Lebesgue-null

A nonzero polynomial in finitely many real variables vanishes on a Lebesgue-null set. The proof
peels off one variable: after separating a variable with `MvPolynomial.finSuccEquiv`, some
coefficient polynomial is nonzero, so by induction almost every choice of the remaining
variables leaves a nonzero one-variable polynomial, whose finitely many roots are null; Fubini
for the product measure combines the two.

## Main declarations

* `TauCeti.MvPolynomial.volume_setOfPred_eval_eq_zero` — the zero locus of a nonzero
  `MvPolynomial ι ℝ` is `volume`-null in `ι → ℝ`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure** (the polynomial-zero-locus infrastructure
  for the singularity of degenerate Wishart laws).
-/

public section

noncomputable section

open MeasureTheory

namespace MvPolynomial

/-- Polynomial evaluation is continuous, so its zero locus is closed, hence measurable. -/
private theorem measurableSet_setOfPred_eval_eq_zero {ι : Type*} [Countable ι]
    (P : MvPolynomial ι ℝ) : MeasurableSet {x : ι → ℝ | MvPolynomial.eval x P = 0} :=
  (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet

end MvPolynomial

namespace TauCeti

namespace MvPolynomial

/-- The zero locus of a nonzero real polynomial in `n` variables is Lebesgue-null. -/
private theorem volume_setOfPred_eval_eq_zero_fin :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP
    obtain ⟨a, rfl⟩ := MvPolynomial.C_surjective (Fin 0) P
    have ha : a ≠ 0 := fun h => hP (by rw [h, map_zero])
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x (MvPolynomial.C a) = 0} = ∅ := by
      ext x; simp [ha]
    rw [hempty, measure_empty]
  | succ n ih =>
    intro P hP
    set Q := MvPolynomial.finSuccEquiv ℝ n P with hQdef
    have hQ : Q ≠ 0 := by rw [hQdef]; simpa using hP
    have hk : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hQ
    have he : MeasurePreserving
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm) volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    rw [← he.measure_preimage_equiv {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0}]
    set T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
      {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0} with hTdef
    have hT : MeasurableSet T :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable
        (_root_.MvPolynomial.measurableSet_setOfPred_eval_eq_zero P)
    have hslice : ∀ s : Fin n → ℝ, ((fun y : ℝ => (y, s)) ⁻¹' T) =
        {y : ℝ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) Q) = 0} := by
      intro s
      ext y
      simp only [hTdef, Set.mem_preimage, Set.mem_ofPred_eq]
      rw [show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (y, s)
            : Fin (n + 1) → ℝ) = Fin.cons y s by simp [Fin.consEquiv],
        MvPolynomial.eval_eq_eval_mv_eval' s y P, hQdef]
    have hae : (fun s : Fin n → ℝ => volume ((fun y : ℝ => (y, s)) ⁻¹' T)) =ᵐ[volume] 0 := by
      filter_upwards [compl_mem_ae_iff.2 (ih (Q.coeff Q.natDegree) hk)] with s hs
      have hs' : MvPolynomial.eval s (Q.coeff Q.natDegree) ≠ 0 := hs
      have hne : Polynomial.map (MvPolynomial.eval s) Q ≠ 0 := fun h =>
        hs' (by simpa [Polynomial.coeff_map] using congrArg (Polynomial.coeff · Q.natDegree) h)
      rw [hslice s]
      exact (Polynomial.finite_setOfPred_isRoot hne).measure_zero _
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hT, lintegral_congr_ae hae]
    simp

/-- The zero locus of a nonzero multivariate real polynomial is Lebesgue-null. -/
theorem volume_setOfPred_eval_eq_zero {ι : Type*} [Fintype ι] {P : MvPolynomial ι ℝ} (hP : P ≠ 0) :
    volume {x : ι → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  have hφ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm) volume volume :=
    volume_measurePreserving_piCongrLeft _ _
  rw [← hφ.measure_preimage_equiv {x : ι → ℝ | MvPolynomial.eval x P = 0}]
  have hpre : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm) ⁻¹'
      {x : ι → ℝ | MvPolynomial.eval x P = 0}) =
      {z : Fin (Fintype.card ι) → ℝ |
        MvPolynomial.eval z (MvPolynomial.rename (Fintype.equivFin ι) P) = 0} := by
    ext z
    have happ : (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm) z
        = fun i => z (Fintype.equivFin ι i) := by
      funext i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp [happ, MvPolynomial.eval_rename, Function.comp_def]
  rw [hpre]
  exact volume_setOfPred_eval_eq_zero_fin _ _ fun h =>
    hP (MvPolynomial.rename_injective _ (Fintype.equivFin ι).injective (by rw [h, map_zero]))

end MvPolynomial

end TauCeti
