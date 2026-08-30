/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Composition of scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block.
-/

public section

open scoped BigOperators

namespace FormalMultilinearSeries

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E]

omit [TopologicalSpace E] [IsTopologicalRing E] in
private theorem prod_ofFn_smul {n : ℕ} (a : Fin n → 𝕜) (b : Fin n → E) :
    (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
    simp only [List.prod_cons, ih]
    exact smul_mul_smul_comm _ _ _ _

omit [Ring E] [TopologicalSpace E] [IsTopologicalRing E] in
private theorem ofFn_embedding_eq_block {n : ℕ} (p : Composition n) (v : Fin n → E)
    (i : Fin p.length) :
    List.ofFn (fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)) =
      ((List.ofFn v).splitWrtComposition p).get
        ⟨i, by simp⟩ := by
  let p' : Composition (List.ofFn v).length := p.cast (by simp)
  have hsplit : (List.ofFn v).splitWrtComposition p' =
      (List.ofFn v).splitWrtComposition p := by rfl
  let ip : Fin ((List.ofFn v).splitWrtComposition p').length :=
    ⟨i, by
      simpa only [List.length_splitWrtComposition, p', Composition.cast] using i.isLt⟩
  have hblock := List.get_of_eq hsplit ip
  have hm := @List.getElem_of_eq _ _ _
      (List.map_length_splitWrtComposition (List.ofFn v) p') i.val (by
        simpa only [List.length_map, List.length_splitWrtComposition, p',
          Composition.cast] using i.isLt)
  have hlen :
      (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).length =
        (((List.ofFn v).splitWrtComposition p').get ip).length := by
    calc
      (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).length =
          p.blocksFun i := by simp
      _ = (((List.ofFn v).splitWrtComposition p').get ip).length := by
        simpa [p', Composition.blocksFun, ip] using hm.symm
  apply List.ext_getElem
  · calc
      _ = (((List.ofFn v).splitWrtComposition p').get ip).length := hlen
      _ = _ := congrArg List.length hblock
  · intro j hj₁ hj₂
    have hvalue := @List.getElem_of_eq _ _ _ hblock j (hlen ▸ hj₁)
    rw [List.getElem_ofFn]
    rw [← hvalue]
    simp only [List.get_eq_getElem]
    have hslice := List.getElem_splitWrtComposition (List.ofFn v) p' ip.val ip.isLt
    have hsliceValue := @List.getElem_of_eq _ _ _ hslice j (hlen ▸ hj₁)
    rw [hsliceValue]
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn]
    apply congrArg v
    apply Fin.ext
    rfl

omit [TopologicalSpace E] [IsTopologicalRing E] in
private theorem prod_blocks {n : ℕ} (p : Composition n) (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod).prod =
      (List.ofFn v).prod := by
  have h :
      List.ofFn (fun i : Fin p.length ↦
          (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod) =
        ((List.ofFn v).splitWrtComposition p).map List.prod := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_map]
      exact congrArg List.prod (ofFn_embedding_eq_block p v ⟨i, by simpa using hi₁⟩)
  rw [h, ← List.prod_flatten]
  let p' : Composition (List.ofFn v).length := p.cast (by simp)
  have hsplit : (List.ofFn v).splitWrtComposition p' =
      (List.ofFn v).splitWrtComposition p := by rfl
  rw [← hsplit, List.flatten_splitWrtComposition]

private theorem prod_applyComposition_ofScalars {n : ℕ} (d : ℕ → 𝕜) (p : Composition n)
    (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (ofScalars E d).applyComposition p v i).prod =
      (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
  simp only [applyComposition, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [prod_ofFn_smul]
  congr 1
  exact prod_blocks p v

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [prod_applyComposition_ofScalars]
  simp only [smul_smul]

end FormalMultilinearSeries
