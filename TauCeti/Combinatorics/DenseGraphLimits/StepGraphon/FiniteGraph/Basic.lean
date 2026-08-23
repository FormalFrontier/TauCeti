/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.MeasureTheory.Constructions.UnitInterval

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
`homDensity_finiteGraphGraphon` carries `0 < m`: for a *nonempty* vertex type and a pattern with no
edges the graphon density is `1`, while there is no map `V → Fin 0`, so the finite density is
`0 / 0 ^ |V(F)| = 0 / 0 = 0`. (For an empty vertex type both sides are `1` even at `m = 0`.)

Symmetry of the value is then the symmetry of an adjacency relation, with no case analysis on `m`,
and measurability is a composition through the countable discrete space `ℕ × ℕ`.

## Main definitions

* `TauCeti.DenseGraphLimits.finiteGraphGraphon` — the graphon of a finite graph.

## Main results

* `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply` — the defining value, at the level of the
  `ℕ`-valued cell indices;
* `TauCeti.DenseGraphLimits.finiteGraphGraphon_eq_const_zero` — the value for the empty host;
* `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_fin`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_not_adj`,
  `TauCeti.DenseGraphLimits.finiteGraphGraphon_apply_of_cellIdx_eq` — the value in terms of the
  adjacency of `G` itself, on `Fin m`;
* `TauCeti.DenseGraphLimits.homDensity_finiteGraphGraphon` — finite-graph compatibility.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 acceptance ("a finite graph as a
  step graphon") and Layer 7 / *Worked examples* ("finite-graph compatibility
  `t(F, W_G) = hom(F,G)/|V(G)|^{|V(F)|}`). The signatures `finiteGraphGraphon` and
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
definition is total in `m`; see the module docstring. Use `finiteGraphGraphon_apply_fin` and the
rectangle lemmas `finiteGraphGraphon_apply_of_adj`, `finiteGraphGraphon_apply_of_not_adj` to
evaluate in terms of the adjacency of `G` on `Fin m`. -/
def finiteGraphGraphon (G : SimpleGraph (Fin m)) : Graphon I (volume : Measure I) where
  toFun x y := if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0
  symm' x y := by
    by_cases h : (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y)
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  meas' :=
    (measurable_of_countable fun q : ℕ × ℕ =>
        if (G.map Fin.valEmbedding).Adj q.1 q.2 then (1 : ℝ) else 0).comp
      ((measurable_cellIdx.comp measurable_fst).prodMk (measurable_cellIdx.comp measurable_snd))
  bdd' := ⟨1, fun x y => by split_ifs <;> simp⟩
  mem01' x y := by split_ifs <;> simp

variable {G : SimpleGraph (Fin m)} {x y : I} {i j : Fin m}

open scoped Classical in
/-- The defining value of `finiteGraphGraphon`, at the level of the `ℕ`-valued cell indices and the
transported graph `G.map Fin.valEmbedding`.

The lemmas below state the same value in terms of the adjacency of `G` on `Fin m`, which is the
form callers should use. -/
theorem finiteGraphGraphon_apply (G : SimpleGraph (Fin m)) (x y : I) :
    finiteGraphGraphon G x y =
      if (G.map Fin.valEmbedding).Adj (cellIdx m x) (cellIdx m y) then 1 else 0 := (rfl)

/-- The graphon of the unique graph on the empty vertex type is the constant-zero graphon. -/
@[simp]
theorem finiteGraphGraphon_eq_const_zero (G : SimpleGraph (Fin 0)) :
    finiteGraphGraphon G = Graphon.const volume 0 := by
  ext x y
  rw [finiteGraphGraphon_apply, Graphon.const_apply, ite_eq_right]
  · rfl
  · rw [SimpleGraph.map_adj]
    rintro ⟨i, j, _⟩
    exact Fin.elim0 i

private theorem map_valEmbedding_adj_iff (G : SimpleGraph (Fin m)) (i j : Fin m) :
    (G.map Fin.valEmbedding).Adj (i : ℕ) (j : ℕ) ↔ G.Adj i j := by
  simpa only [Fin.valEmbedding_apply] using
    (SimpleGraph.map_adj_apply (G := G) (f := Fin.valEmbedding) (a := i) (b := j))

/-- On a rectangle `cell i × cell j` spanned by an edge of `G`, the graphon takes the value `1`. -/
theorem finiteGraphGraphon_apply_of_adj (hij : G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 1 := by
  rw [finiteGraphGraphon_apply, ite_eq_left]
  rw [hx, hy]
  exact (map_valEmbedding_adj_iff G i j).2 hij

/-- On a rectangle `cell i × cell j` spanned by a non-edge of `G`, the graphon takes the value
`0`. -/
theorem finiteGraphGraphon_apply_of_not_adj (hij : ¬ G.Adj i j) (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = 0 := by
  rw [finiteGraphGraphon_apply, ite_eq_right]
  rw [hx, hy]
  exact fun h => hij ((map_valEmbedding_adj_iff G i j).1 h)

/-- Evaluating the graphon of a finite graph on a rectangle of cells, in `if`-form. -/
theorem finiteGraphGraphon_apply_of_cellIdx_eq [DecidableRel G.Adj] (hx : cellIdx m x = i)
    (hy : cellIdx m y = j) : finiteGraphGraphon G x y = if G.Adj i j then 1 else 0 := by
  by_cases hij : G.Adj i j
  · rw [ite_eq_left hij, finiteGraphGraphon_apply_of_adj hij hx hy]
  · rw [ite_eq_right hij, finiteGraphGraphon_apply_of_not_adj hij hx hy]

/-- The value of `finiteGraphGraphon` at an arbitrary pair of points, in terms of the adjacency of
`G` between the cells containing them. -/
@[simp]
theorem finiteGraphGraphon_apply_fin (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hm : 0 < m) (x y : I) : finiteGraphGraphon G x y =
      if G.Adj ⟨cellIdx m x, cellIdx_lt hm x⟩ ⟨cellIdx m y, cellIdx_lt hm y⟩ then 1 else 0 :=
  finiteGraphGraphon_apply_of_cellIdx_eq rfl rfl

variable {V : Type*} [Fintype V]

/-- **Finite-graph compatibility.** The graphon homomorphism density of `F` in the graphon of a
finite graph `G` on `Fin m` is the finite homomorphism density of `F` in `G`:

`t(F, W_G) = hom(F, G) / m ^ |V(F)|`.

Positivity of `m` is needed when `V` is nonempty: at `m = 0` and a pattern with no edges the
left-hand side is `1`, while the right-hand side is `0 / 0 = 0`. -/
@[simp]
theorem homDensity_finiteGraphGraphon (F : SimpleGraph V) [DecidableRel F.Adj] (hm : 0 < m)
    (G : SimpleGraph (Fin m)) :
    homDensity F (finiteGraphGraphon G) = homDensityFin F G := by
  classical
  -- the integrand is the adjacency-preservation indicator of the tuple of cell indices
  have hstep : ∀ x : V → I, ∏ e ∈ F.edgeFinset, edgeFactor (finiteGraphGraphon G) x e
      = if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b))
          then (1 : ℝ) else 0 := by
    intro x
    let p : Sym2 V → Prop := Sym2.lift
      ⟨fun a b => (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b)),
        fun a b => propext (SimpleGraph.adj_comm (G.map Fin.valEmbedding) _ _)⟩
    have hfac : ∀ e : Sym2 V,
        edgeFactor (finiteGraphGraphon G) x e = if p e then 1 else 0 := by
      intro e
      induction e using Sym2.ind with
      | _ a b =>
        rw [edgeFactor_mk, finiteGraphGraphon_apply]
        exact if_congr (by simp only [p, Sym2.lift_mk]) rfl rfl
    have hp_iff : (∀ e ∈ F.edgeFinset, p e) ↔
        ∀ a b, F.Adj a b →
          (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b)) := by
      constructor
      · intro h a b hab
        simpa only [p, Sym2.lift_mk] using h s(a, b) (by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hab)
      · intro h e he
        induction e using Sym2.ind with
        | _ a b =>
          simpa only [p, Sym2.lift_mk] using h a b (by
            simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he)
    rw [Finset.prod_congr rfl fun e _ => hfac e, Finset.prod_boole]
    by_cases h : ∀ a b, F.Adj a b →
        (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b))
    · rw [ite_eq_left h, ite_eq_left (hp_iff.2 h)]
    · rw [ite_eq_right h, ite_eq_right fun hp => h (hp_iff.1 hp)]
  -- the resulting finite sum counts the homomorphisms
  have hsum : (∑ ψ : V → Fin m, if ∀ a b, F.Adj a b →
        (G.map Fin.valEmbedding).Adj ((ψ a : ℕ)) ((ψ b : ℕ)) then (1 : ℝ) else 0)
      = (Nat.card (F →g G) : ℝ) := by
    have hcongr : ∀ ψ : V → Fin m,
        (if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj ((ψ a : ℕ)) ((ψ b : ℕ))
          then (1 : ℝ) else 0)
          = if ∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b) then 1 else 0 := fun ψ =>
      if_congr (forall_congr' fun a => forall_congr' fun b =>
        imp_congr_right fun _ => map_valEmbedding_adj_iff G (ψ a) (ψ b)) rfl rfl
    rw [Finset.sum_congr rfl fun ψ _ => hcongr ψ, Finset.sum_boole,
      card_hom_eq_card_adjPreservingMaps,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpi : (∫ x : V → I,
        (if ∀ a b, F.Adj a b →
          (G.map Fin.valEmbedding).Adj (cellIdx m (x a)) (cellIdx m (x b)) then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : V => (volume : Measure I)))
      = (∑ ψ : V → Fin m, if ∀ a b, F.Adj a b →
          (G.map Fin.valEmbedding).Adj (ψ a : ℕ) (ψ b : ℕ) then (1 : ℝ) else 0)
          / (m : ℝ) ^ Fintype.card V := by
    simpa [smul_eq_mul, div_eq_inv_mul] using
      (integral_pi_comp_cellIdx_eq_inv_smul_sum (V := V) hm
        (fun ν : V → ℕ => if ∀ a b, F.Adj a b → (G.map Fin.valEmbedding).Adj (ν a) (ν b)
          then (1 : ℝ) else 0))
  rw [homDensity_def, integral_congr_ae (Filter.Eventually.of_forall hstep), hpi, hsum,
    homDensityFin_def, Fintype.card_fin]

end DenseGraphLimits

end TauCeti
