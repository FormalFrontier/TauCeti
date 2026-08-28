/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Basic
public import TauCeti.Topology.PiCurry
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-!
# Analytic coordinate changes for families of simple roots

An elementary-symmetric chart on a symmetric power of a surface separates a tuple into the
points lying in finitely many disjoint coordinate patches. If the multiplicity in patch `i` is
`m i`, its coordinates form a block `Fin (m i) → 𝕜`; a bijection
`(Σ i, Fin (m i)) ≃ Fin n` regroups those blocks into the model space `Fin n → 𝕜`.

`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm` proves that changing the surface
coordinate is analytic on one block when its roots are distinct. This file applies that result to
a finite family of blocks and then conjugates the family by the possibly different source and
target regroupings. The assembled statement is
`TauCeti.Sym.analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm`.

Thus the blockwise coordinate-change expression used by elementary-symmetric charts is analytic
at tuples that are multiplicity-free inside every block. The case where points collide remains
separate: there the inverse root parametrization is not analytic, and the transition map must
instead be studied directly as a symmetric holomorphic function.

This is the multiplicity-free assembly step in Lane F4.1 of the analytic Heegaard Floer roadmap,
whose first target is the smooth complex structure on `Sym^g(Σ)` from elementary symmetric
functions. The organization follows Ozsváth--Szabó,
[arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Section 2.1.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜]
variable {ι : Type*} [Finite ι] {m : ι → ℕ} {n : ℕ}

attribute [local instance] Fintype.ofFinite

omit [IsAlgClosed 𝕜] in
/-- Regrouping a finite family of tuples is analytic. This is kept private because the public
result below exposes exactly the conjugated coordinate change needed by symmetric-power charts. -/
private theorem analyticAt_piSigmaConstHomeomorph
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : ∀ i, Fin (m i) → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e) c := by
  refine AnalyticAt.pi fun j => ?_
  have hblock : AnalyticAt 𝕜 (fun p : (∀ i, Fin (m i) → 𝕜) => p (e.symm j).1) c :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i => Fin (m i) → 𝕜)
      (e.symm j).1).analyticAt c
  have hcoord : AnalyticAt 𝕜 (fun p : Fin (m (e.symm j).1) → 𝕜 => p (e.symm j).2)
      (c (e.symm j).1) :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (m (e.symm j).1) => 𝕜)
      (e.symm j).2).analyticAt _
  convert hcoord.comp hblock using 1
  ext x
  exact piSigmaConstHomeomorph_apply 𝕜 e x j

omit [IsAlgClosed 𝕜] in
/-- The inverse regrouping from one tuple to a finite family of tuples is analytic. -/
private theorem analyticAt_piSigmaConstHomeomorph_symm
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : Fin n → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e).symm c := by
  refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
  convert (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)
    (e ⟨i, j⟩)).analyticAt c using 1
  ext x
  exact piSigmaConstHomeomorph_symm_apply 𝕜 e x i j

/-- **Coordinate changes on a finite family of multiplicity-free root blocks are analytic.**

For each `i`, the coefficient tuple `c₀ i` represents the pairwise distinct roots `z i`. Applying
`φ i` to those roots and returning to elementary-symmetric coordinates is analytic jointly in
the family of coefficient blocks, provided `φ i` is analytic at every represented root. -/
private theorem analyticAt_pi_coeffEquiv_map_coeffEquiv_symm
    {φ : ι → 𝕜 → 𝕜} {c₀ z : ∀ i, Fin (m i) → 𝕜}
    (hz : ∀ i, Function.Injective (z i))
    (hc₀ : ∀ i, (coeffEquiv 𝕜 (m i)).symm (c₀ i) = ofFn (z i))
    (hφ : ∀ i j, AnalyticAt 𝕜 (φ i) (z i j)) :
    AnalyticAt 𝕜
      (fun c i => coeffEquiv 𝕜 (m i)
        (_root_.Sym.map (φ i) ((coeffEquiv 𝕜 (m i)).symm (c i)))) c₀ := by
  refine AnalyticAt.pi fun i => ?_
  exact AnalyticAt.comp (f := fun c : (∀ i, Fin (m i) → 𝕜) => c i)
    (analyticAt_coeffEquiv_map_coeffEquiv_symm (hz i) (hc₀ i) (hφ i))
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun i => Fin (m i) → 𝕜) i).analyticAt c₀)

/-- **A blockwise elementary-symmetric coordinate change is analytic after regrouping.**

The bijections `e` and `e'` are the independent choices used to identify the source and target
families of coefficient blocks with `Fin n → 𝕜`. The transition first undoes `e`, changes the
underlying coordinate separately on each root block, and then regroups along `e'`. It is analytic
at every tuple whose roots are pairwise distinct inside each block. -/
theorem analyticAt_piSigmaConstHomeomorph_coeffEquiv_map_coeffEquiv_symm
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    {φ : ι → 𝕜 → 𝕜} {c₀ z : ∀ i, Fin (m i) → 𝕜}
    (hz : ∀ i, Function.Injective (z i))
    (hc₀ : ∀ i, (coeffEquiv 𝕜 (m i)).symm (c₀ i) = ofFn (z i))
    (hφ : ∀ i j, AnalyticAt 𝕜 (φ i) (z i j)) :
    AnalyticAt 𝕜
      (fun c => piSigmaConstHomeomorph 𝕜 e' (fun i =>
        coeffEquiv 𝕜 (m i) (_root_.Sym.map (φ i)
          ((coeffEquiv 𝕜 (m i)).symm ((piSigmaConstHomeomorph 𝕜 e).symm c i)))))
      (piSigmaConstHomeomorph 𝕜 e c₀) := by
  have hin := analyticAt_piSigmaConstHomeomorph_symm (𝕜 := 𝕜) e
    (piSigmaConstHomeomorph 𝕜 e c₀)
  have hblocks := analyticAt_pi_coeffEquiv_map_coeffEquiv_symm hz hc₀ hφ
  have hblocks' : AnalyticAt 𝕜
      (fun c => fun i => coeffEquiv 𝕜 (m i) (_root_.Sym.map (φ i)
        ((coeffEquiv 𝕜 (m i)).symm (c i))))
      ((piSigmaConstHomeomorph 𝕜 e).symm (piSigmaConstHomeomorph 𝕜 e c₀)) := by
    rw [Homeomorph.symm_apply_apply]
    exact hblocks
  have hmiddle := AnalyticAt.comp
    (f := (piSigmaConstHomeomorph 𝕜 e).symm) hblocks' hin
  have hmiddle' : AnalyticAt 𝕜
      (fun c => fun i => coeffEquiv 𝕜 (m i) (_root_.Sym.map (φ i)
        ((coeffEquiv 𝕜 (m i)).symm ((piSigmaConstHomeomorph 𝕜 e).symm c i))))
      (piSigmaConstHomeomorph 𝕜 e c₀) := by
    convert hmiddle using 1
    all_goals rfl
  convert AnalyticAt.comp
    (f := fun c => fun i => coeffEquiv 𝕜 (m i) (_root_.Sym.map (φ i)
      ((coeffEquiv 𝕜 (m i)).symm ((piSigmaConstHomeomorph 𝕜 e).symm c i))))
    (analyticAt_piSigmaConstHomeomorph (𝕜 := 𝕜) e' _) hmiddle' using 1
  all_goals rfl

end Sym

end TauCeti
