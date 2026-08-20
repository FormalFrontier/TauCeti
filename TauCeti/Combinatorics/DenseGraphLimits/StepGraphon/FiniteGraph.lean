/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# A finite graph as a graphon

`finiteGraphGraphon G` is the graphon `W_G` of a finite graph `G` on `Fin m`: the step graphon on
the `m` equal cells of `(I, volume)` taking the value `1` on the rectangle `cell i × cell j` when
`i ~ j` in `G`, and `0` otherwise.

Its defining property is **finite-graph compatibility**: the graphon homomorphism density of a
finite pattern `F` in `W_G` is the finite homomorphism density of `F` in `G`,

`t(F, W_G) = hom(F, G) / m ^ |V(F)|`,

which is `homDensity_finiteGraphGraphon`. That is what makes the graphon theory an extension of the
finite theory rather than a parallel one: every finite graph sits in the graphon world with its
densities unchanged, and the sampling and mixture layers read a sampled finite graph back as a
point of the graphon space along this map.

## Why the definition goes through `ℕ`

`finiteGraphGraphon` has to be total in `m`, and there is no map `I → Fin 0`. The value is
therefore read off `G.map Fin.valEmbedding`, the transport of `G` to a graph on `ℕ` in which every
vertex outside `[0, m)` is isolated, evaluated at the `ℕ`-valued cell index `unitInterval.cellIdx`.
At `m = 0` that graph has no edges and `finiteGraphGraphon G` is the zero graphon — which is why
`homDensity_finiteGraphGraphon` carries `0 < m`: for an empty host and a pattern with no edges the
graphon density is `1` while the finite density is `0 / 0 = 0`.

Symmetry of the value is then the symmetry of an adjacency relation, with no case analysis on `m`,
and measurability is a composition through the countable discrete space `ℕ × ℕ`.

## Main definitions

* `TauCeti.DenseGraphLimits.finiteGraphGraphon` — the graphon of a finite graph.

## Main results

* `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_not_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply` — the value on a rectangle of cells;
* `TauCeti.DenseGraphLimits.homDensity_finiteGraphGraphon` — finite-graph compatibility;
* `TauCeti.DenseGraphLimits.homDensity_top_finiteGraphGraphon_top` and
  `TauCeti.DenseGraphLimits.homDensity_top_finiteGraphGraphon_cycleGraph` — the computed-value
  backstops `t(K₂, W_{K₄}) = 3/4` and `t(K₃, W_{C₅}) = 0`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 acceptance ("a finite graph as a
  step graphon") and Layer 7 / *Worked examples* ("finite-graph compatibility
  `t(F, W_G) = hom(F,G)/|V(G)|^{|V(F)|}`"), together with the computed-value backstops
  `t(K₂, W_{K₄}) = 3/4` and `t(K₃, W_{C₅}) = 0`. The signatures `finiteGraphGraphon` and
  `homDensity_finiteGraphGraphon` follow `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti.unitInterval

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {m : ℕ}

open scoped Classical in
/-- The **graphon of a finite graph** `G` on `Fin m`: the step graphon on the `m` equal cells of
`(I, volume)` whose value on `cell i × cell j` is `1` if `i ~ j` in `G` and `0` otherwise.

The adjacency is read off `G.map Fin.valEmbedding`, the transport of `G` to `ℕ`, so that the
definition is total in `m`; see the module docstring. Use `finiteGraphGraphon_apply_of_adj` and
`finiteGraphGraphon_apply_of_not_adj` to evaluate on a rectangle of cells. -/
def finiteGraphGraphon (G : SimpleGraph (Fin m)) : Graphon I (volume : Measure I) where
  toFun x y := if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0
  symm' x y := by
    by_cases h : (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y)
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  meas' := by
    change Measurable fun p : I × I =>
      if (G.map Fin.valEmbedding).Adj (cellIdx m p.1) (cellIdx m p.2) then (1 : ℝ) else 0
    exact (measurable_of_countable fun q : ℕ × ℕ =>
        if (G.map Fin.valEmbedding).Adj q.1 q.2 then (1 : ℝ) else 0).comp
      ((measurable_cellIdx.comp measurable_fst).prodMk (measurable_cellIdx.comp measurable_snd))
  bdd' := ⟨1, fun x y => by split_ifs <;> simp⟩
  mem01' x y := by split_ifs <;> simp

variable {G : SimpleGraph (Fin m)} {x y : I} {i j : Fin m}

open scoped Classical in
/-- The defining value of `finiteGraphGraphon`, at the level of the `ℕ`-valued cell indices.

This is the honest unfolding, transport to `ℕ` included; the rectangle lemmas below are the form
callers should use. -/
theorem finiteGraphGraphon_apply_cellIdx (G : SimpleGraph (Fin m)) (x y : I) :
    finiteGraphGraphon G x y =
      if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0 := (rfl)

/-- On a rectangle `cell i × cell j` spanned by an edge of `G`, the graphon takes the value `1`. -/
theorem finiteGraphGraphon_apply_of_adj (hij : G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 1 := by
  rw [finiteGraphGraphon_apply_cellIdx, ite_eq_left]
  rw [hx, hy]
  exact SimpleGraph.map_adj_apply.2 hij

/-- On a rectangle `cell i × cell j` spanned by a non-edge of `G`, the graphon takes the value
`0`. -/
theorem finiteGraphGraphon_apply_of_not_adj (hij : ¬ G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 0 := by
  rw [finiteGraphGraphon_apply_cellIdx, ite_eq_right]
  rw [hx, hy]
  exact fun h => hij (SimpleGraph.map_adj_apply.1 h)

/-- Evaluating the graphon of a finite graph on a rectangle of cells, in `if`-form. -/
theorem finiteGraphGraphon_apply [DecidableRel G.Adj] (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = if G.Adj i j then 1 else 0 := by
  by_cases hij : G.Adj i j
  · rw [ite_eq_left hij, finiteGraphGraphon_apply_of_adj hij hx hy]
  · rw [ite_eq_right hij, finiteGraphGraphon_apply_of_not_adj hij hx hy]

variable {V : Type*} [Fintype V]

/-- **Finite-graph compatibility.** The graphon homomorphism density of `F` in the graphon of a
finite graph `G` on `Fin m` is the finite homomorphism density of `F` in `G`:

`t(F, W_G) = hom(F, G) / m ^ |V(F)|`.

Positivity of `m` is needed: at `m = 0` and a pattern with no edges the left-hand side is `1`,
while the right-hand side is `0 / 0 = 0`.

The proof is a change of variables and nothing else. The integrand is constant on each product of
cells, and equals `1` exactly when the corresponding map `V → Fin m` preserves adjacency, so
`unitInterval.integral_pi_comp_cellIdx` turns the integral into the average of that indicator over
all `m ^ |V(F)|` vertex maps — which is the finite density. -/
theorem homDensity_finiteGraphGraphon (F : SimpleGraph V) [DecidableRel F.Adj] (hm : 0 < m)
    (G : SimpleGraph (Fin m)) :
    homDensity F (finiteGraphGraphon G) = homDensityFin F G := by
  classical
  -- the integrand is the adjacency-preservation indicator of the tuple of cell indices
  have hstep : ∀ x : V → I, ∏ e ∈ F.edgeFinset, edgeFactor (finiteGraphGraphon G) x e
      = if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b))
          then (1 : ℝ) else 0 := by
    intro x
    by_cases h : ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b))
    · rw [ite_eq_left h]
      refine Finset.prod_eq_one fun e he => ?_
      revert he
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        rw [edgeFactor_mk]
        refine finiteGraphGraphon_apply_of_adj (i := ⟨cellIdx m (x a), cellIdx_lt hm _⟩)
          (j := ⟨cellIdx m (x b), cellIdx_lt hm _⟩) ?_ rfl rfl
        exact SimpleGraph.map_adj_apply.1 (h a b (by simpa using he))
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨a, b, hab, hnot⟩ := h
      refine Finset.prod_eq_zero (i := s(a, b)) (by simpa using hab) ?_
      rw [edgeFactor_mk]
      refine finiteGraphGraphon_apply_of_not_adj (i := ⟨cellIdx m (x a), cellIdx_lt hm _⟩)
        (j := ⟨cellIdx m (x b), cellIdx_lt hm _⟩) ?_ rfl rfl
      exact fun hadj => hnot (SimpleGraph.map_adj_apply.2 hadj)
  -- the resulting finite sum counts the homomorphisms
  have hsum : (∑ ψ : V → Fin m, if ∀ a b, F.Adj a b →
        (G.map Fin.valEmbedding).Adj ((ψ a : ℕ)) ((ψ b : ℕ)) then (1 : ℝ) else 0)
      = (Nat.card (F →g G) : ℝ) := by
    have hcongr : ∀ ψ : V → Fin m,
        (if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj ((ψ a : ℕ)) ((ψ b : ℕ))
          then (1 : ℝ) else 0)
          = if ∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b) then 1 else 0 := fun ψ =>
      if_congr (forall_congr' fun a => forall_congr' fun b =>
        imp_congr_right fun _ => SimpleGraph.map_adj_apply) rfl rfl
    rw [Finset.sum_congr rfl fun ψ _ => hcongr ψ, Finset.sum_boole, card_hom_eq_card_subtype,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpi := integral_pi_comp_cellIdx (V := V) hm
    (fun ν : V → ℕ => if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj (ν a) (ν b)
      then (1 : ℝ) else 0)
  rw [homDensity_def, integral_congr_ae (Filter.Eventually.of_forall hstep), hpi, hsum,
    homDensityFin_def, Fintype.card_fin]

/-! ### Computed-value backstops -/

/-- **The edge density of `K₄`.** `t(K₂, W_{K₄}) = 3/4`: of the `16` ordered pairs of vertices of
the complete graph on four vertices, the `12` with distinct entries are adjacent.

A numeric floor under the definitions that the headline compatibility theorem does not give: it
pins the normalization of both densities and the equal size of the cells at once. -/
theorem homDensity_top_finiteGraphGraphon_top :
    homDensity (⊤ : SimpleGraph (Fin 2)) (finiteGraphGraphon (⊤ : SimpleGraph (Fin 4)))
      = 3 / 4 := by
  have hcount : Nat.card ((⊤ : SimpleGraph (Fin 2)) →g (⊤ : SimpleGraph (Fin 4))) = 12 := by
    rw [card_hom_eq_card_subtype, Nat.card_eq_fintype_card]
    decide
  rw [homDensity_finiteGraphGraphon _ (by norm_num), homDensityFin_def, hcount]
  norm_num

/-- **`C₅` is triangle-free.** `t(K₃, W_{C₅}) = 0`: no map `Fin 3 → Fin 5` sends all three edges of
a triangle to edges of the five-cycle, so the density vanishes exactly rather than approximately. -/
theorem homDensity_top_finiteGraphGraphon_cycleGraph :
    homDensity (⊤ : SimpleGraph (Fin 3)) (finiteGraphGraphon (SimpleGraph.cycleGraph 5)) = 0 := by
  have hcount : Nat.card ((⊤ : SimpleGraph (Fin 3)) →g SimpleGraph.cycleGraph 5) = 0 := by
    rw [card_hom_eq_card_subtype, Nat.card_eq_fintype_card]
    decide
  rw [homDensity_finiteGraphGraphon _ (by norm_num), homDensityFin_def, hcount]
  norm_num

end DenseGraphLimits

end TauCeti
