/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.PathHomotopyDiscreteness
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.Basic

/-!
# Based paths

This file introduces the compact-open based-path space `BasedPath x₀` and the path-component
machinery of `endpoint ⁻¹' U` used in the universal-cover construction. It is adapted from
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292) by Kim Morrison.
-/

open scoped unitInterval
open Topology TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The compact-open based-path space out of `x₀`. -/
@[expose] public def BasedPath (x₀ : X) :=
  { γ : C(I, X) // γ 0 = x₀ }

namespace BasedPath

variable {x₀ : X}

public instance : TopologicalSpace (BasedPath x₀) :=
  inferInstanceAs (TopologicalSpace { γ : C(I, X) // γ 0 = x₀ })

/-- The endpoint of a based path. -/
@[expose] public def endpoint (γ : BasedPath x₀) : X := γ.1 1

/-- The endpoint map from based paths to their terminal point is continuous. -/
public theorem continuous_endpoint : Continuous (endpoint (x₀ := x₀)) :=
  (continuous_eval_const (1 : I)).comp continuous_induced_dom

/-- View a based path as a path to its endpoint. -/
@[expose] public def toPath (γ : BasedPath x₀) : Path x₀ (endpoint γ) where
  toContinuousMap := γ.1
  source' := γ.2
  target' := rfl

/-- Definitional unfolding of `endpoint`. Not a global simp lemma: it overlaps with
`endpoint_refl` (and other `endpoint_…` lemmas) on the simp normal form, so we instead include it
explicitly in `simp [endpoint_def, …]` at each site that wants to bridge between the named
`endpoint γ = u` API and the underlying `γ.1 1` evaluation. -/
public theorem endpoint_def (γ : BasedPath x₀) : endpoint γ = γ.1 1 := rfl
@[simp] public theorem toPath_apply (γ : BasedPath x₀) (t : I) : toPath γ t = γ.1 t := rfl
public theorem toPath_source (γ : BasedPath x₀) : toPath γ 0 = x₀ := γ.2
public theorem toPath_target (γ : BasedPath x₀) : toPath γ 1 = endpoint γ := rfl

@[ext] public theorem ext {γ γ' : BasedPath x₀} (h : ∀ t, γ.1 t = γ'.1 t) : γ = γ' := by
  cases γ with
  | mk γ hγ =>
    cases γ' with
    | mk γ' hγ' =>
      simp only at h
      have hfun : γ = γ' := by
        ext t
        exact h t
      subst hfun
      simp

/-- The canonical inclusion `Path x₀ y → BasedPath x₀`: package an ordinary path out of `x₀` as a
based path, forgetting `y` at the type level. The endpoint is recovered as
`endpoint (ofPath γ) = y` via `endpoint_ofPath`. The map `toPath` is a partial inverse:
`ofPath γ.toPath = γ` (`ofPath_toPath_self`), and conversely `(ofPath γ).toPath` is `γ` with its
right endpoint cast to `endpoint (ofPath γ)` (`toPath_ofPath`). -/
@[expose] public def ofPath {y : X} (γ : Path x₀ y) : BasedPath x₀ :=
  ⟨γ.toContinuousMap, γ.source⟩

@[simp] public theorem toPath_ofPath {y : X} (γ : Path x₀ y) :
    (ofPath γ).toPath = γ.cast rfl γ.target := by
  ext t
  rfl

@[simp] public theorem endpoint_ofPath {y : X} (γ : Path x₀ y) : endpoint (ofPath γ) = y :=
  γ.target

/-- The round-trip `ofPath ∘ toPath` is the identity on `BasedPath x₀`. -/
@[simp] public theorem ofPath_toPath_self (γ : BasedPath x₀) : ofPath γ.toPath = γ := rfl

/-- `ofPath` is invariant under reindexing the right endpoint via `Path.cast`. -/
@[simp] public theorem ofPath_cast {y y' : X} (γ : Path x₀ y) (h : y' = y) :
    ofPath (γ.cast rfl h) = ofPath γ := rfl

/-- The constant based path at `x₀`. -/
@[expose] public def refl (x₀ : X) : BasedPath x₀ :=
  ofPath (Path.refl x₀)

@[simp] public theorem endpoint_refl (x₀ : X) : endpoint (refl x₀) = x₀ :=
  endpoint_ofPath _

@[simp] public theorem toPath_refl (x₀ : X) :
    (refl x₀).toPath = Path.refl x₀ := by
  apply Path.ext; funext t; rfl

@[simp] public theorem ofPath_refl (x₀ : X) :
    ofPath (Path.refl x₀) = refl x₀ := rfl

/-- Append a path `δ` at the endpoint of a based path `γ`, defined as
`ofPath (γ.toPath.trans δ)`: the half `s ∈ [0, ½]` traverses `γ` at double speed and the half
`s ∈ [½, 1]` traverses `δ` at double speed (`Path.trans_apply`). The new endpoint is the endpoint
of `δ` (`endpoint_append`). This is the move used by `joinedIn_preimage_of_append` to slide a
based path within a path component of `endpoint ⁻¹' U`. -/
-- `append` is exposed so the exported endpoint and `toPath` normal-form lemmas can typecheck
-- across the module boundary; their result types identify endpoints by unfolding this wrapper.
@[expose] public noncomputable def append {y : X} (γ : BasedPath x₀)
    (δ : Path (endpoint γ) y) : BasedPath x₀ :=
  ofPath (γ.toPath.trans δ)

@[simp] public theorem toPath_append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
    (append γ δ).toPath = (γ.toPath.trans δ).cast rfl (γ.toPath.trans δ).target := by
  simp [append, toPath_ofPath]

@[simp] public theorem endpoint_append {y : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) y) :
    endpoint (append γ δ) = y := endpoint_ofPath _

/-- The tail of a based path past time `a`, viewed as a `Path (γ.toPath.extend a) u` where
`u = endpoint γ`. Concretely it is `γ.toPath.truncateOfLE` between `a` and `1`, cast on the right
to land at `u`; the only hypothesis required is `a ≤ 1` (for `a < 0` the source is clamped
through `Path.extend`). This is the "compressed tail" piece used by `deformTerminal` to splice
a new endpoint path onto `γ` while preserving its image on `[0, a]`. -/
private noncomputable def terminalTail {u : X} (γ : BasedPath x₀)
    (hu : endpoint γ = u) (a : ℝ) (ha1 : a ≤ 1) :
    Path (γ.toPath.extend a) u :=
  (γ.toPath.truncateOfLE (t₀ := a) (t₁ := 1) ha1).cast rfl
    (by simpa using! hu.symm)

/-- Replace the terminal interval of a based path by first traversing a compressed tail of the
original path and then a new endpoint path. -/
private noncomputable def deformTerminal {u v : X} (γ : BasedPath x₀)
    (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) : BasedPath x₀ := by
  let tail : Path (γ.toPath.extend a) u := terminalTail γ hu a (by linarith)
  let f : ℝ → X := fun t ↦
    if hta : t ≤ a then γ.toPath.extend t else
      if htb : t ≤ b then tail.extend ((t - a) / (b - a)) else δ.extend ((t - b) / (1 - b))
  have hf_cont : Continuous f := by
    refine Continuous.if_le γ.toPath.continuous_extend ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le
        (tail.continuous_extend.comp (by fun_prop))
        (δ.continuous_extend.comp (by fun_prop))
        continuous_id continuous_const ?_
      · intro t htb
        have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne.symm
        subst t
        simp [tail, hba]
    · intro t hta
      subst t
      simp [tail, hab.le]
  refine ⟨ContinuousMap.mk
    (fun t : I ↦ f t)
    (hf_cont.comp continuous_subtype_val), ?_⟩
  simpa [f, ha, endpoint_def] using! γ.toPath.source

private theorem deformTerminal_apply_of_le {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (ht : (t : ℝ) ≤ a) :
    (deformTerminal γ hu δ ha hab hb).1 t = γ.toPath.extend t := by
  simp [deformTerminal, endpoint_def, ht]

private theorem deformTerminal_apply_of_lt_of_le {u v : X} (γ : BasedPath x₀)
    (hu : endpoint γ = u) (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (hta : a < (t : ℝ)) (htb : (t : ℝ) ≤ b) :
    (deformTerminal γ hu δ ha hab hb).1 t =
      (terminalTail γ hu a (by linarith)).extend (((t : ℝ) - a) / (b - a)) := by
  simp [deformTerminal, endpoint_def, not_le_of_gt hta, htb]

private theorem deformTerminal_apply_of_lt {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (t : I) (ht : b < (t : ℝ)) :
    (deformTerminal γ hu δ ha hab hb).1 t = δ.extend (((t : ℝ) - b) / (1 - b)) := by
  simp [deformTerminal, endpoint_def, not_le_of_gt (lt_trans hab ht), not_le_of_gt ht]

/-- The endpoint of `deformTerminal γ hu δ ha hab hb` is the endpoint of `δ`. -/
private theorem endpoint_deformTerminal {u v : X} (γ : BasedPath x₀) (hu : endpoint γ = u)
    (δ : Path u v) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    endpoint (deformTerminal γ hu δ ha hab hb) = v := by
  simp only [endpoint_def]
  rw [deformTerminal_apply_of_lt γ hu δ ha hab hb 1 hb]
  have hbne : (1 : ℝ) - b ≠ 0 := sub_ne_zero.mpr hb.ne'
  have hone : (((1 : I) : ℝ) - b) / (1 - b) = 1 := by
    have : ((1 : I) : ℝ) = 1 := rfl
    rw [this]; field_simp
  rw [hone]
  simp [δ.extend_one]

/-- Appending a fixed terminal path's initial-segment family to a fixed based path is jointly
continuous in the family parameter. This packages the boilerplate for using
`Path.trans_continuous_family` to lift `append γ ∘ Path.initialSegmentFamily δ` to a continuous
map `I → BasedPath x₀`. -/
public theorem continuous_append_initialSegmentFamily {x₀ z : X}
    (γ : BasedPath x₀) (δ : Path (endpoint γ) z) :
    Continuous fun t : I ↦ γ.append (Path.initialSegmentFamily δ t) := by
  apply Continuous.subtype_mk
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  simpa using!
    Path.trans_continuous_family (fun _ : I ↦ γ.toPath)
      (Path.continuous_uncurry_iff.mpr continuous_const) (Path.initialSegmentFamily δ)
      (Path.continuous_initialSegmentFamily_uncurry δ)

/-- Extract an open path-connected endpoint neighborhood and a terminal interval avoiding the
subbasic compact sets that do not contain `1`. -/
theorem exists_endpointNeighborhood_of_basicNeighborhood [LocallyPathConnectedSpace X]
    {x₀ : X} (γ : BasedPath x₀) (Tgood Tbad : Finset (Set I × Set X))
    (hTgood_open_mem : ∀ KU ∈ Tgood, IsOpen KU.2 ∧ endpoint γ ∈ KU.2)
    (hTbad_closed : ∀ KU ∈ Tbad, IsClosed KU.1)
    (hTbad_not_mem : ∀ KU ∈ Tbad, (1 : I) ∉ KU.1) :
    ∃ (W : Set X) (a₀ : I) (a b : ℝ),
      IsOpen W ∧ endpoint γ ∈ W ∧ IsPathConnected W ∧
      (∀ KU ∈ Tgood, W ⊆ KU.2) ∧
      Set.Ioc a₀ 1 ⊆ γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ ∧
      ((a₀ : I) : ℝ) < a ∧ 0 ≤ a ∧ a ≤ 1 ∧ a < b ∧ b < 1 := by
  let O : Set X := ⋂ KU ∈ Tgood, KU.2
  have hOopen : IsOpen O :=
    isOpen_biInter_finset fun KU hKU ↦ (hTgood_open_mem KU hKU).1
  have huO : endpoint γ ∈ O := by
    simp only [O, Set.mem_iInter]
    exact fun KU hKU ↦ (hTgood_open_mem KU hKU).2
  rcases (isOpen_isPathConnected_basis (x := endpoint γ)).mem_iff.mp
      (hOopen.mem_nhds huO) with ⟨W, ⟨hWopen, huW, hWpath⟩, hWO⟩
  let N : Set I := γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ
  have hNnhds : N ∈ 𝓝 (1 : I) := by
    refine Filter.inter_mem
      ((hWopen.preimage γ.toPath.continuous).mem_nhds (by simpa using! huW)) ?_
    refine (isOpen_biInter_finset ?_).mem_nhds ?_
    · exact fun KU hKU ↦ (hTbad_closed KU hKU).isOpen_compl
    · simp only [Set.mem_iInter]
      intro KU hKU
      exact hTbad_not_mem KU hKU
  rcases exists_Ioc_subset_of_mem_nhds' hNnhds (show (0 : I) < 1 by simp) with ⟨a₀, ha₀, hIoc⟩
  let a : ℝ := (((a₀ : I) : ℝ) + 1) / 2
  let b : ℝ := (a + 1) / 2
  have ha₀_nonneg : 0 ≤ ((a₀ : I) : ℝ) := a₀.2.1
  have ha₀_lt_one : ((a₀ : I) : ℝ) < 1 := ha₀.2
  have ha₀_lt_a : ((a₀ : I) : ℝ) < a := by dsimp [a]; nlinarith
  have ha0 : 0 ≤ a := by dsimp [a]; nlinarith
  have ha1 : a ≤ 1 := by dsimp [a]; nlinarith
  have hab : a < b := by dsimp [a, b]; nlinarith
  have hb1 : b < 1 := by dsimp [a, b]; nlinarith
  refine ⟨W, a₀, a, b, hWopen, huW, hWpath, ?_, hIoc, ha₀_lt_a, ha0, ha1, hab, hb1⟩
  intro KU hKU z hz
  have hz' : ∀ KU ∈ Tgood, z ∈ KU.2 := by simpa [O] using! hWO hz
  exact hz' KU hKU

/-- The range of the compressed terminal tail `terminalTail γ rfl a ha1` is contained in `W`,
given that the terminal interval `Set.Ioc a₀ 1` maps into `W` under `γ.toPath` (`hpreim`), that
`a₀ < a` (`ha₀_lt_a`) and that `a ≤ 1` (`ha1`). The tail retraces `γ` over `[a, 1]`, and every
such time already lies in `Set.Ioc a₀ 1`, so its image lies in `W`. -/
private theorem terminalTail_range_subset (γ : BasedPath x₀) {W : Set X} {a₀ : I} {a : ℝ}
    (hpreim : Set.Ioc a₀ 1 ⊆ γ.toPath ⁻¹' W)
    (ha₀_lt_a : ((a₀ : I) : ℝ) < a) (ha1 : a ≤ 1) :
    Set.range (terminalTail γ rfl a ha1) ⊆ W := by
  apply Path.truncateOfLE_range_subset (h := ha1)
  intro s hs
  have ha0 : (0 : ℝ) ≤ a := (a₀.2.1.trans_lt ha₀_lt_a).le
  have hs01 : s ∈ (Set.Icc 0 1 : Set ℝ) := ⟨le_trans ha0 hs.1, hs.2⟩
  simp only [Set.mem_preimage]
  rw [Path.extend_apply _ hs01]
  refine hpreim ?_
  refine ⟨?_, ?_⟩
  · -- No interval-order lemma matches this mixed subtype/real goal directly.
    change ((a₀ : I) : ℝ) < s
    exact lt_of_lt_of_le ha₀_lt_a hs.1
  · -- No interval-order lemma matches this mixed subtype/real goal directly.
    change s ≤ 1
    exact hs.2

/-- For a time `t` with `a < t`, the deformed based path `deformTerminal γ rfl δ ha0 hab hb1`
takes a value in `U` at `t`, provided `W ⊆ U` (`hWU`), the terminal tail's range lies in `W`
(`htail`), and `δ`'s range lies in `W` (`hδW`). The bounds are `0 ≤ a` (`ha0`), `a < b` (`hab`),
`b < 1` (`hb1`), and `a ≤ 1` (`ha1`, which names the tail's defining bound). On `a < t ≤ b` the
value lies on the tail, and on `b < t` it lies on `δ`; either way it is in `W ⊆ U`. -/
private theorem deformTerminal_apply_mem_of_lt {v : X} (γ : BasedPath x₀)
    (δ : Path (endpoint γ) v) {W U : Set X} {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1)
    (ha1 : a ≤ 1) (hWU : W ⊆ U) (htail : Set.range (terminalTail γ rfl a ha1) ⊆ W)
    (hδW : Set.range δ ⊆ W) (t : I) (hat : a < (t : ℝ)) :
    (deformTerminal γ rfl δ ha0 hab hb1).1 t ∈ U := by
  by_cases htb : (t : ℝ) ≤ b
  · have hparam : (((t : ℝ) - a) / (b - a)) ∈ (Set.Icc 0 1 : Set ℝ) :=
      unitInterval.div_mem (sub_nonneg.mpr hat.le) (sub_pos.mpr hab).le (sub_le_sub_right htb a)
    rw [deformTerminal_apply_of_lt_of_le γ rfl δ ha0 hab hb1 t hat htb,
      Path.extend_apply _ hparam]
    exact hWU (htail ⟨⟨((t : ℝ) - a) / (b - a), hparam⟩, rfl⟩)
  · have hbt : b < (t : ℝ) := lt_of_not_ge htb
    have hparam : (((t : ℝ) - b) / (1 - b)) ∈ (Set.Icc 0 1 : Set ℝ) :=
      unitInterval.div_mem (sub_nonneg.mpr hbt.le) (sub_pos.mpr hb1).le (sub_le_sub_right t.2.2 b)
    rw [deformTerminal_apply_of_lt γ rfl δ ha0 hab hb1 t hbt, Path.extend_apply _ hparam]
    exact hWU (hδW ⟨⟨((t : ℝ) - b) / (1 - b), hparam⟩, rfl⟩)

omit [TopologicalSpace X] in
/-- A time `t` in the set `K` of a `Tbad` pair `(K, U)` (`hKUbad`, `ht`) satisfies
`(t : ℝ) ≤ a`, provided the terminal interval `Set.Ioc a₀ 1` avoids every `Tbad` set
(`hbad_avoid`) and `a₀ < a` (`ha₀_lt_a`). Were `(t : ℝ) > a`, then `a₀ < a < t ≤ 1` would place
`t` in `Set.Ioc a₀ 1`, contradicting that `t` lies in the avoided set `K`. -/
private theorem coe_le_of_mem_Tbad {Tbad : Finset (Set I × Set X)} {a₀ : I} {a : ℝ}
    (hbad_avoid : Set.Ioc a₀ 1 ⊆ ⋂ KU ∈ Tbad, KU.1ᶜ) (ha₀_lt_a : ((a₀ : I) : ℝ) < a)
    {K : Set I} {U : Set X} (hKUbad : (K, U) ∈ Tbad) {t : I} (ht : t ∈ K) : (t : ℝ) ≤ a := by
  have ht_not_Ioc : t ∉ Set.Ioc a₀ 1 := fun htIoc ↦ by
    have htN' : ∀ KU ∈ Tbad, t ∉ KU.1 := by simpa using! hbad_avoid htIoc
    exact htN' (K, U) hKUbad ht
  by_contra hgt
  have hat₀ : ((a₀ : I) : ℝ) < t := lt_trans ha₀_lt_a (lt_of_not_ge hgt)
  exact ht_not_Ioc ⟨hat₀, t.2.2⟩

/-- The deformed based path `deformTerminal γ rfl δ ha0 hab hb1` maps the set `K` of a
pair `(K, U) ∈ S` (`hKU`) into `U`. Here `hγKU` says `γ.1` already maps `K` into `U`;
`hT_of_S` includes `S` into `T`;
`hTgood_iff` and `hTbad_iff` split `T` according to whether `1 ∈ K`; `hW_good` says `W` refines
every `Tgood` target; `hIoc` places `Set.Ioc a₀ 1` inside `γ.toPath ⁻¹' W` and away from the
`Tbad` sets; `ha₀_lt_a`, `ha0`, `ha1`, `hab`, `hb1` are the bounds `a₀ < a`, `0 ≤ a`, `a ≤ 1`,
`a < b`, `b < 1`; and `hδW` says `δ` stays in `W`. For `t ≤ a` the deformed path agrees with `γ`,
and for `a < t` the pair is forced to be `Tgood`, so the value lies in `W ⊆ U`. -/
private theorem mapsTo_deformTerminal {v : X} (γ : BasedPath x₀) (δ : Path (endpoint γ) v)
    {S : Set (Set I × Set X)} {T Tgood Tbad : Finset (Set I × Set X)}
    (hT_of_S : ∀ KU, KU ∈ S → KU ∈ T)
    (hTgood_iff : ∀ KU, KU ∈ Tgood ↔ KU ∈ T ∧ (1 : I) ∈ KU.1)
    (hTbad_iff : ∀ KU, KU ∈ Tbad ↔ KU ∈ T ∧ (1 : I) ∉ KU.1)
    {W : Set X} (hW_good : ∀ KU ∈ Tgood, W ⊆ KU.2) {a₀ : I} {a b : ℝ}
    (hIoc : Set.Ioc a₀ 1 ⊆ γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ)
    (ha₀_lt_a : ((a₀ : I) : ℝ) < a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (hb1 : b < 1)
    (hδW : Set.range δ ⊆ W) {K : Set I} {U : Set X} (hKU : (K, U) ∈ S)
    (hγKU : Set.MapsTo γ.1 K U) :
    Set.MapsTo (deformTerminal γ rfl δ ha0 hab hb1).1 K U := by
  classical
  have htail : Set.range (terminalTail γ rfl a ha1) ⊆ W :=
    terminalTail_range_subset γ (hIoc.trans Set.inter_subset_left) ha₀_lt_a ha1
  intro t ht
  have hKUT : (K, U) ∈ T := hT_of_S (K, U) hKU
  by_cases hta : (t : ℝ) ≤ a
  · rw [deformTerminal_apply_of_le γ rfl δ ha0 hab hb1 t hta, Path.extend_apply _ t.2]
    exact hγKU ht
  · have hat : a < (t : ℝ) := lt_of_not_ge hta
    have h1K : (1 : I) ∈ K := by
      by_contra h1K
      exact absurd
        (coe_le_of_mem_Tbad (hIoc.trans Set.inter_subset_right) ha₀_lt_a
          ((hTbad_iff (K, U)).2 ⟨hKUT, h1K⟩) ht) (not_le.mpr hat)
    exact deformTerminal_apply_mem_of_lt γ δ ha0 hab hb1 ha1
      (hW_good (K, U) ((hTgood_iff (K, U)).2 ⟨hKUT, h1K⟩)) htail hδW t hat

/-- Any point in the chosen path-connected endpoint neighborhood is realized by a deformed based
path that still lies in the original compact-open basic neighborhood. -/
theorem exists_deformTerminal_mem_basicNeighborhood
    {x₀ : X} (γ : BasedPath x₀) {V : Set (C(I, X))} {S : Set (Set I × Set X)}
    {T Tgood Tbad : Finset (Set I × Set X)}
    (hSdata : ∀ K U, (K, U) ∈ S → IsCompact K ∧ IsOpen U ∧ Set.MapsTo γ.1 K U)
    (hT_of_S : ∀ KU, KU ∈ S → KU ∈ T)
    (hSV : {g : C(I, X) | ∀ K U, (K, U) ∈ S → Set.MapsTo g K U} ⊆ V)
    (hTgood_iff : ∀ KU, KU ∈ Tgood ↔ KU ∈ T ∧ (1 : I) ∈ KU.1)
    (hTbad_iff : ∀ KU, KU ∈ Tbad ↔ KU ∈ T ∧ (1 : I) ∉ KU.1)
    {W : Set X} (huW : endpoint γ ∈ W) (hWpath : IsPathConnected W)
    (hW_good : ∀ KU ∈ Tgood, W ⊆ KU.2)
    {a₀ : I} {a b : ℝ}
    (hIoc : Set.Ioc a₀ 1 ⊆ γ.toPath ⁻¹' W ∩ ⋂ KU ∈ Tbad, KU.1ᶜ)
    (ha₀_lt_a : ((a₀ : I) : ℝ) < a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hab : a < b) (hb1 : b < 1) :
    ∀ v ∈ W, ∃ η : BasedPath x₀, η.1 ∈ V ∧ endpoint η = v := by
  intro v hvW
  obtain ⟨δ, hδ⟩ := hWpath.joinedIn _ huW _ hvW
  refine ⟨deformTerminal γ rfl δ ha0 hab hb1, ?_,
    endpoint_deformTerminal γ rfl δ ha0 hab hb1⟩
  exact hSV fun K U hKU ↦ mapsTo_deformTerminal γ δ hT_of_S hTgood_iff hTbad_iff
    hW_good hIoc ha₀_lt_a ha0 ha1 hab hb1 (Set.range_subset_iff.mpr hδ) hKU (hSdata K U hKU).2.2

/-- The endpoint map `BasedPath x₀ → X` is an open map when `X` is locally path-connected. -/
public theorem isOpenMap_endpoint [LocallyPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (endpoint (x₀ := x₀)) := by
  classical
  refine IsOpenMap.of_nhds_le ?_
  intro γ
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_map'] at hs
  have hsub := mem_nhds_subtype (s := {γ : C(I, X) | γ 0 = x₀}) γ
    ({η : BasedPath x₀ | endpoint η ∈ s})
  rcases hsub.mp hs with ⟨V, hVγ, hVs⟩
  rcases ContinuousMap.mem_nhds_iff.1 hVγ with ⟨S, hSfin, hSdata, hSV⟩
  let T : Finset (Set I × Set X) := hSfin.toFinset
  let Tgood : Finset (Set I × Set X) := T.filter fun KU ↦ (1 : I) ∈ KU.1
  let Tbad : Finset (Set I × Set X) := T.filter fun KU ↦ (1 : I) ∉ KU.1
  have hS_of_T : ∀ KU, KU ∈ T → KU ∈ S := fun _ ↦ hSfin.mem_toFinset.mp
  have hT_of_S : ∀ KU, KU ∈ S → KU ∈ T := fun _ ↦ hSfin.mem_toFinset.mpr
  have hgood : ∀ KU ∈ Tgood, KU ∈ S ∧ (1 : I) ∈ KU.1 := fun KU hKU ↦
    let ⟨hT, h1⟩ := Finset.mem_filter.mp hKU
    ⟨hS_of_T KU hT, h1⟩
  have hbad : ∀ KU ∈ Tbad, KU ∈ S ∧ (1 : I) ∉ KU.1 := fun KU hKU ↦
    let ⟨hT, h1⟩ := Finset.mem_filter.mp hKU
    ⟨hS_of_T KU hT, h1⟩
  obtain ⟨W, a₀, a, b, hWopen, huW, hWpath, hW_good, hIoc, ha₀_lt_a, ha0, ha1, hab, hb1⟩ :=
    exists_endpointNeighborhood_of_basicNeighborhood γ Tgood Tbad
      (fun KU hKU ↦ ⟨(hSdata KU.1 KU.2 (hgood KU hKU).1).2.1,
        (hSdata KU.1 KU.2 (hgood KU hKU).1).2.2 (hgood KU hKU).2⟩)
      (fun KU hKU ↦ (hSdata KU.1 KU.2 (hbad KU hKU).1).1.isClosed)
      (fun KU hKU ↦ (hbad KU hKU).2)
  refine mem_nhds_iff.mpr ⟨W, ?_, hWopen, huW⟩
  intro v hvW
  obtain ⟨η, hηV, hend⟩ :=
    exists_deformTerminal_mem_basicNeighborhood γ hSdata hT_of_S hSV
      (fun KU ↦ by simp [Tgood])
      (fun KU ↦ by simp [Tbad])
      huW hWpath hW_good hIoc ha₀_lt_a ha0 ha1 hab hb1 v hvW
  have hηs : endpoint η ∈ s := hVs hηV
  rw [hend] at hηs
  exact hηs

variable {x₀ : X}

/-- Endpoint-preserving homotopic paths to a point `y ∈ U` give joined based paths inside the
endpoint preimage of `U`. -/
public theorem joinedIn_endpoint_preimage_of_homotopic (x₀ : X) {y : X} {U : Set X}
    (hy : y ∈ U) {p q : Path x₀ y} (h : Path.Homotopic p q) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) (ofPath q) := by
  rcases h with ⟨H⟩
  let γ : Path (ofPath p) (ofPath q) :=
    { toFun := fun t ↦ ofPath (H.eval t)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_induced_dom.comp <| (Path.continuous_uncurry_iff.mp <| by
          -- `Path.continuous_uncurry_iff` leaves the homotopy as its coercion; name that
          -- defeq form so `H.continuous` applies.
          change Continuous fun ts : I × I ↦ H ts
          exact H.continuous)
      source' := by
        ext s
        simp
      target' := by
        ext s
        simp }
  refine ⟨γ, fun t ↦ ?_⟩
  -- `γ` is a let-bound path, so expose its definitional value before using endpoint API.
  change endpoint (ofPath (H.eval t)) ∈ U
  rw [endpoint_ofPath]
  exact hy

/-- Appending a path that stays inside `U` moves a based path within the same path component of
the endpoint preimage of `U`. -/
public theorem joinedIn_preimage_of_append {U : Set X} {z : X} (γ : BasedPath x₀)
    (δ : Path (endpoint γ) z) (hδU : Set.range δ ⊆ U) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) γ (append γ δ) := by
  have hγU : endpoint γ ∈ U := by
    simpa [δ.source] using hδU ⟨0, rfl⟩
  let γrefl : Path (endpoint γ) (endpoint γ) := Path.refl (endpoint γ)
  have h_start :
      JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) γ (append γ γrefl) := by
    simpa [γrefl] using!
      (joinedIn_endpoint_preimage_of_homotopic (x₀ := x₀) (U := U) hγU
        (p := γ.toPath.trans (Path.refl (endpoint γ))) (q := γ.toPath)
        (Path.Homotopic.trans_refl γ.toPath)).symm
  have h_move :
      JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) (append γ γrefl) (append γ δ) := by
    let η : Path (append γ γrefl) (append γ δ) := {
      toFun := fun t ↦ append γ (Path.initialSegmentFamily δ t)
      continuous_toFun := continuous_append_initialSegmentFamily γ δ
      source' := by
        rw [Path.initialSegmentFamily_zero]
        ext s
        -- The endpoint casts come from `Path.initialSegmentFamily_zero`; expose the appended
        -- path values so `Path.cast_coe` can remove them pointwise.
        change (γ.toPath.trans ((Path.refl (endpoint γ)).cast _ _)) s =
          (γ.toPath.trans γrefl) s
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs <;> simp only [γrefl, Path.cast_coe]
      target' := by
        rw [Path.initialSegmentFamily_one]
        ext s
        -- As above, the final segment differs only by endpoint casts introduced by the
        -- initial-segment normal form.
        change (γ.toPath.trans (δ.cast _ _)) s = (γ.toPath.trans δ) s
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs <;> simp only [Path.cast_coe] }
    refine ⟨η, fun t ↦ ?_⟩
    -- `η` is a let-bound path, so expose its definitional value before using endpoint API.
    change endpoint (append γ (Path.initialSegmentFamily δ t)) ∈ U
    rw [BasedPath.endpoint_append]
    exact hδU ⟨t, rfl⟩
  exact h_start.trans h_move

theorem exists_refined_terminal_vertex
    [LocallyPathConnectedSpace X]
    {x₀ : X} {n' : ℕ} {U : Set X} (hU_open : IsOpen U)
    (α : BasedPath x₀) (hα : endpoint α ∈ U)
    (part : IntervalPartition (n' + 1)) (T : TubeData X (n' + 1))
    (hα_tube : PathInTube α.toPath part T) :
    ∃ V_last' : Set X,
      IsOpen V_last' ∧ IsPathConnected V_last' ∧ endpoint α ∈ V_last' ∧
      V_last' ⊆ T.V (Fin.last (n' + 1)) ∧ V_last' ⊆ U := by
  have hα_at_last : α.toPath (part.t (Fin.last (n' + 1))) = endpoint α := by
    rw [part.t_last]
    exact α.toPath.target
  let V_last := T.V (Fin.last (n' + 1))
  have hα_V_last : endpoint α ∈ V_last := hα_at_last ▸ hα_tube.passes_through_V _
  let W : Set X := V_last ∩ U
  have hW_open : IsOpen W := (T.V_open _).inter hU_open
  have hα_W : endpoint α ∈ W := ⟨hα_V_last, hα⟩
  refine ⟨pathComponentIn W (endpoint α), hW_open.pathComponentIn _,
    isPathConnected_pathComponentIn hα_W, mem_pathComponentIn_self hα_W, ?_, ?_⟩
  · exact pathComponentIn_subset.trans Set.inter_subset_left
  · exact pathComponentIn_subset.trans Set.inter_subset_right

theorem isOpen_refined_tubeNeighborhood
    {x₀ : X} {n' : ℕ} (part : IntervalPartition (n' + 1))
    {U : Fin (n' + 1) → Set X} {V : Fin (n' + 2) → Set X}
    (hU_open : ∀ i, IsOpen (U i)) (hV_open : ∀ j, IsOpen (V j)) :
    IsOpen {β : BasedPath x₀ |
      (∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i) ∧
      (∀ j, β.1 (part.t j) ∈ V j)} := by
  have h_split : {β : BasedPath x₀ |
        (∀ (i : Fin (n' + 1)) (s : I),
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i) ∧
        (∀ j, β.1 (part.t j) ∈ V j)} =
      {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i} ∩
      {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V j} := by ext β; simp
  rw [h_split]
  refine IsOpen.inter ?_ ?_
  · have h_U_iInter : {β : BasedPath x₀ | ∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i} =
        ⋂ i : Fin (n' + 1), {β : BasedPath x₀ | ∀ s : I,
            (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i} := by
      ext β; simp
    rw [h_U_iInter]
    refine isOpen_iInter_of_finite fun i ↦ ?_
    have h_U_preimage : {β : BasedPath x₀ | ∀ s : I,
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ U i} =
        (fun β : BasedPath x₀ ↦ (β.1 : C(I, X))) ⁻¹'
          {f : C(I, X) | Set.MapsTo f
            (Set.Icc (part.t i.castSucc) (part.t i.succ) : Set I) (U i)} := by
      ext β; simp [Set.MapsTo, Set.mem_Icc]
    rw [h_U_preimage]
    exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc (hU_open i)).preimage
      continuous_subtype_val
  · have h_V_iInter : {β : BasedPath x₀ | ∀ j, β.1 (part.t j) ∈ V j} =
        ⋂ j : Fin (n' + 2), {β : BasedPath x₀ | β.1 (part.t j) ∈ V j} := by ext β; simp
    rw [h_V_iInter]
    exact isOpen_iInter_of_finite fun j ↦
      (hV_open j).preimage ((continuous_eval_const (part.t j)).comp continuous_subtype_val)

/-- **Refining the terminal vertex set of a tube.** If the last vertex set of `T` is replaced by a
smaller `V_last'` that is itself open, path-connected and contains `endpoint α`, the resulting
family is again open and path-connected, is contained in `T.V` pointwise, and `α` still passes
through it at every partition point. -/
private theorem exists_refined_vertex_family {n' : ℕ} {part : IntervalPartition (n' + 1)}
    {T : TubeData X (n' + 1)} {α : BasedPath x₀}
    (hα_passes : ∀ j, α.toPath (part.t j) ∈ T.V j)
    {V_last' : Set X} (hV'_open : IsOpen V_last') (hV'_pathConn : IsPathConnected V_last')
    (hα_V' : endpoint α ∈ V_last') (hV'_sub_V : V_last' ⊆ T.V (Fin.last (n' + 1))) :
    ∃ V' : Fin (n' + 2) → Set X,
      (∀ j, IsOpen (V' j)) ∧ (∀ j, IsPathConnected (V' j)) ∧ (∀ j, V' j ⊆ T.V j) ∧
        V' (Fin.last (n' + 1)) = V_last' ∧ ∀ j, α.toPath (part.t j) ∈ V' j := by
  have hα_at_last : α.toPath (part.t (Fin.last (n' + 1))) = endpoint α := by
    rw [part.t_last]; exact α.toPath.target
  refine ⟨Fin.snoc (fun j : Fin (n' + 1) ↦ T.V j.castSucc) V_last', ?_, ?_, ?_,
    Fin.snoc_last .., ?_⟩
  · exact fun j ↦ by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hV'_open
      | cast k => rw [Fin.snoc_castSucc]; exact T.V_open _
  · exact fun j ↦ by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hV'_pathConn
      | cast k => rw [Fin.snoc_castSucc]; exact T.V_pathConn _
  · exact fun j ↦ by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hV'_sub_V
      | cast k => rw [Fin.snoc_castSucc]
  · exact fun j ↦ by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, hα_at_last]; exact hα_V'
      | cast k => rw [Fin.snoc_castSucc]; exact hα_passes _

/-- **A path through the refined tube is joined to `α`.** If `β` runs through the same tube as `α`
with refined vertex sets `V'` whose terminal member is contained in `U`, then `β` is joined to `α`
inside `endpoint ⁻¹' U`. -/
private theorem joinedIn_endpoint_preimage_of_pathInTube {n' : ℕ} {U : Set X}
    {V' : Fin (n' + 2) → Set X} {part : IntervalPartition (n' + 1)}
    {T : TubeData X (n' + 1)} (hV'_open : ∀ j, IsOpen (V' j))
    (hV'_pathConn : ∀ j, IsPathConnected (V' j)) (hV'_sub_TV : ∀ j, V' j ⊆ T.V j)
    (hV'_last_sub_U : V' (Fin.last (n' + 1)) ⊆ U) {α β : BasedPath x₀}
    (hα_stays : ∀ (i : Fin (n' + 1)) (s : I),
      (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → α.toPath s ∈ T.U i)
    (hα_passes : ∀ j, α.toPath (part.t j) ∈ V' j)
    (hβ_stays : ∀ (i : Fin (n' + 1)) (s : I),
      (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i)
    (hβ_passes : ∀ j, β.1 (part.t j) ∈ V' j) :
    JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β := by
  let T' : TubeData X (n' + 1) := {
    U := T.U
    V := V'
    U_open := T.U_open
    U_slsc := T.U_slsc
    V_open := hV'_open
    V_pathConn := hV'_pathConn
    V_left_subset := fun i ↦ (hV'_sub_TV i.castSucc).trans (T.V_left_subset i)
    V_right_subset := fun i ↦ (hV'_sub_TV i.succ).trans (T.V_right_subset i)
  }
  have hβ_end_U : endpoint β ∈ U :=
    hV'_last_sub_U (by simpa [part.t_last] using! hβ_passes (Fin.last (n' + 1)))
  obtain ⟨ρ_final, hρ_final_range_V, h_paste⟩ :=
    Path.tube_subset_homotopy_class_source α.toPath part T' ⟨hα_stays, hα_passes⟩
      β.toPath ⟨hβ_stays, hβ_passes⟩
  refine (joinedIn_preimage_of_append α ρ_final
    (hρ_final_range_V.trans hV'_last_sub_U)).trans ?_
  obtain ⟨γ, hγ⟩ :=
    (joinedIn_endpoint_preimage_of_homotopic (x₀ := x₀) (U := ({endpoint β} : Set X))
      (Set.mem_singleton _) h_paste).mono
      (Set.preimage_mono (Set.singleton_subset_iff.mpr hβ_end_U))
  exact ⟨γ.cast rfl (by ext t; rfl), hγ⟩

/-- Variable-endpoint tube/component theorem.

In a locally path-connected space, if semilocal simple connectivity holds along `α.toPath` and
`α : BasedPath x₀` has endpoint in an open set `U`, then `α` has an open neighborhood `N` in
`BasedPath x₀` such that every element of `N` has endpoint in `U` and lies in the same path
component of `endpoint ⁻¹' U` as `α`. -/
public theorem exists_open_nhds_pathComponent_preimage
    [LocallyPathConnectedSpace X] {U : Set X} (hU_open : IsOpen U)
    (α : BasedPath x₀) (hslsc : SemilocallySimplyConnectedOn (Set.range α.toPath))
    (hα : endpoint α ∈ U) :
    ∃ N : Set (BasedPath x₀), IsOpen N ∧ α ∈ N ∧
      N ⊆ endpoint (x₀ := x₀) ⁻¹' U ∧
      ∀ β ∈ N, JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β := by
  classical
  obtain ⟨n, part, T, hα_tube⟩ :=
    α.toPath.exists_pathHomotopyTrivial_tube hslsc
  -- Rule out `n = 0`; the rest of the proof assumes `n = n' + 1`.
  match n, part, T, hα_tube with
  | 0, part, _, _ => exact isEmptyElim part
  | n' + 1, part, T, hα_tube =>
  obtain ⟨V_last', hV'_open, hV'_pathConn, hα_V', hV'_sub_V, hV'_sub_U⟩ :=
    exists_refined_terminal_vertex hU_open α hα part T hα_tube
  obtain ⟨V', hV'_open_all, hV'_pathConn_all, hV'_sub_TV, hV'_last_eq, hα_passes_V'⟩ :=
    exists_refined_vertex_family hα_tube.passes_through_V hV'_open hV'_pathConn hα_V'
      hV'_sub_V
  have hV'_last_sub_U : V' (Fin.last (n' + 1)) ⊆ U := hV'_last_eq ▸ hV'_sub_U
  -- The neighborhood `N` of `α`: based paths satisfying the refined tube conditions.
  set N : Set (BasedPath x₀) := {β : BasedPath x₀ |
      (∀ (i : Fin (n' + 1)) (s : I),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → β.1 s ∈ T.U i) ∧
      (∀ j, β.1 (part.t j) ∈ V' j)} with hN_def
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · simpa [hN_def] using! isOpen_refined_tubeNeighborhood part T.U_open hV'_open_all
  · -- `α ∈ N`.
    exact ⟨hα_tube.stays_in_U, hα_passes_V'⟩
  · -- `N ⊆ endpoint ⁻¹' U`.
    exact fun β hβ ↦
      hV'_last_sub_U (by simpa [part.t_last] using! hβ.2 (Fin.last (n' + 1)))
  · -- Every `β ∈ N` is `JoinedIn (endpoint ⁻¹' U)` to `α`.
    exact fun β hβ ↦ joinedIn_endpoint_preimage_of_pathInTube hV'_open_all hV'_pathConn_all
      hV'_sub_TV hV'_last_sub_U hα_tube.stays_in_U hα_passes_V' hβ.1 hβ.2


/-- For an open neighborhood `U`, path components of `endpoint ⁻¹' U` are open. -/
public theorem isOpen_pathComponent_preimage
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hU_open : IsOpen U) (α : BasedPath x₀) :
    IsOpen (pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) α) := by
  apply isOpen_iff_mem_nhds.mpr
  intro β hβ
  have hβ_end_U : endpoint β ∈ U := hβ.target_mem
  obtain ⟨N, hN_open, hβ_N, _, hN_joined⟩ :=
    exists_open_nhds_pathComponent_preimage hU_open
      β
      (SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace (Set.range β.toPath))
      hβ_end_U
  refine mem_nhds_iff.mpr ⟨N, ?_, hN_open, hβ_N⟩
  intro γ hγ_N
  exact hβ.trans (hN_joined γ hγ_N)

section joinedInSLSC

/-! Reparametrisation helpers for
`toPath_homotopic_of_joinedIn_pathHomotopyTrivial` (private to this section). -/

private def joinedInSLSC_uReal (ts : ℝ × ℝ) : ℝ :=
  ts.1 + max 0 (2 * ts.2 - 1) * (1 - ts.1)

private def joinedInSLSC_vReal (ts : ℝ × ℝ) : ℝ :=
  min (2 * ts.2) 1

private theorem joinedInSLSC_uReal_mem (t s : I) :
    joinedInSLSC_uReal ((t : ℝ), (s : ℝ)) ∈ I := by
  simp only [joinedInSLSC_uReal]
  have hm_nn : (0 : ℝ) ≤ max 0 (2 * (s : ℝ) - 1) := le_max_left _ _
  have hm_le : max 0 (2 * (s : ℝ) - 1) ≤ 1 := max_le zero_le_one (by linarith [s.2.2])
  refine ⟨?_, ?_⟩
  · have h0 : 0 ≤ max 0 (2 * (s : ℝ) - 1) * (1 - (t : ℝ)) :=
      mul_nonneg hm_nn (by linarith [t.2.2])
    linarith [t.2.1]
  · nlinarith [t.2.1, t.2.2]

private theorem joinedInSLSC_vReal_mem (t s : I) :
    joinedInSLSC_vReal ((t : ℝ), (s : ℝ)) ∈ I := by
  refine ⟨le_min (by linarith [s.2.1]) zero_le_one, min_le_right _ _⟩

private def joinedInSLSC_uFn : I × I → I := fun ts ↦
  ⟨joinedInSLSC_uReal ((ts.1 : ℝ), (ts.2 : ℝ)), joinedInSLSC_uReal_mem ts.1 ts.2⟩

private def joinedInSLSC_vFn : I × I → I := fun ts ↦
  ⟨joinedInSLSC_vReal ((ts.1 : ℝ), (ts.2 : ℝ)), joinedInSLSC_vReal_mem ts.1 ts.2⟩

private theorem continuous_joinedInSLSC_uFn : Continuous joinedInSLSC_uFn := by
  have hu_cont : Continuous joinedInSLSC_uReal :=
    (continuous_fst).add <|
      (Continuous.max continuous_const (by fun_prop)).mul (by fun_prop)
  exact Continuous.subtype_mk (hu_cont.comp (by fun_prop)) _

private theorem continuous_joinedInSLSC_vFn : Continuous joinedInSLSC_vFn := by
  have hv_cont : Continuous joinedInSLSC_vReal :=
    Continuous.min (by fun_prop) continuous_const
  exact Continuous.subtype_mk (hv_cont.comp (by fun_prop)) _

/-- The uncurried evaluation of a path of based paths is continuous in both arguments. -/
private theorem continuous_uncurry_basedPath {α β : BasedPath x₀} (F : Path α β) :
    Continuous fun ts : I × I ↦ (F ts.1).1 ts.2 := by
  have h1 : Continuous (fun t : I ↦ ((F t).1 : C(I, X))) :=
    continuous_subtype_val.comp F.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨_, h1⟩

/-- **A square with prescribed edges is a path homotopy.** A continuous map on `I × I` that
restricts to `p` at `t = 0` and to `q` at `t = 1`, and is constant along each of the edges `s = 0`
and `s = 1`, exhibits `p` and `q` as homotopic paths. -/
private theorem homotopic_of_continuous_square {a b : X} {p q : Path a b} (K : I × I → X)
    (hK_cont : Continuous K) (hK_zero : ∀ s, K (0, s) = p s) (hK_one : ∀ s, K (1, s) = q s)
    (hK_left : ∀ t, K (t, 0) = a) (hK_right : ∀ t, K (t, 1) = b) : p.Homotopic q :=
  ⟨{ toFun := K
     continuous_toFun := hK_cont
     map_zero_left := hK_zero
     map_one_left := hK_one
     prop' := by
       intro t s hs
       rcases hs with rfl | hs
       · exact (hK_left t).trans p.source.symm
       · rw [Set.mem_singleton_iff] at hs
         subst hs
         exact (hK_right t).trans p.target.symm }⟩

private theorem joinedInSLSC_uFn_zero_left (s : I) :
    (joinedInSLSC_uFn (0, s) : ℝ) = max 0 (2 * (s : ℝ) - 1) := by
  simp [joinedInSLSC_uFn, joinedInSLSC_uReal]

private theorem joinedInSLSC_uFn_one_left (s : I) : joinedInSLSC_uFn (1, s) = 1 :=
  Subtype.ext (by simp [joinedInSLSC_uFn, joinedInSLSC_uReal])

private theorem joinedInSLSC_uFn_one_right (t : I) : joinedInSLSC_uFn (t, 1) = 1 :=
  Subtype.ext (by simp [joinedInSLSC_uFn, joinedInSLSC_uReal]; ring)

private theorem joinedInSLSC_vFn_left (t s : I) :
    (joinedInSLSC_vFn (t, s) : ℝ) = min (2 * (s : ℝ)) 1 := by
  simp [joinedInSLSC_vFn, joinedInSLSC_vReal]

private theorem joinedInSLSC_vFn_zero_right (t : I) : joinedInSLSC_vFn (t, 0) = 0 :=
  Subtype.ext (by simp [joinedInSLSC_vFn, joinedInSLSC_vReal])

private theorem joinedInSLSC_vFn_one_right (t : I) : joinedInSLSC_vFn (t, 1) = 1 :=
  Subtype.ext (by simp [joinedInSLSC_vFn, joinedInSLSC_vReal])

private theorem joinedInSLSC_uFn_zero_left_eq_zero_of_le_half {s : I}
    (hs : (s : ℝ) ≤ 1 / 2) : joinedInSLSC_uFn (0, s) = 0 :=
  Subtype.ext <| by
    rw [joinedInSLSC_uFn_zero_left, max_eq_left (by linarith)]; rfl

private theorem joinedInSLSC_uFn_zero_left_eq_two_mul_sub_one_of_half_le
    {s : I} (hs : 1 / 2 ≤ (s : ℝ)) :
    joinedInSLSC_uFn (0, s) =
      ⟨2 * (s : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨hs, s.2.2⟩⟩ :=
  Subtype.ext <| by
    rw [joinedInSLSC_uFn_zero_left, max_eq_right (by linarith)]

private theorem joinedInSLSC_vFn_eq_two_mul_of_le_half {t s : I}
    (hs : (s : ℝ) ≤ 1 / 2) :
    joinedInSLSC_vFn (t, s) =
      ⟨2 * (s : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ :=
  Subtype.ext <| by rw [joinedInSLSC_vFn_left, min_eq_left (by linarith)]

private theorem joinedInSLSC_vFn_eq_one_of_half_le {t s : I}
    (hs : 1 / 2 ≤ (s : ℝ)) : joinedInSLSC_vFn (t, s) = 1 :=
  Subtype.ext <| by
    rw [joinedInSLSC_vFn_left, min_eq_right (by linarith)]; rfl

end joinedInSLSC

/-- If `α` and `β` are based paths with the same endpoint `v ∈ U`, joined inside
`endpoint ⁻¹' U`, and `U` has the SLSC uniqueness property, then their associated paths
`α.toPath` and `β.toPath` are homotopic (after casting to a common endpoint).

This is the heart of the sheet-injectivity argument: a path in the based-path space descends
to a free homotopy of paths in `X` whose endpoint trace is a loop in `U`, which is killed by
the SLSC hypothesis. -/
public theorem toPath_homotopic_of_joinedIn_pathHomotopyTrivial
    {U : Set X} (hU_slsc : IsPathHomotopyTrivial U)
    {α β : BasedPath x₀}
    (heq : endpoint α = endpoint β)
    (hAB : JoinedIn (endpoint (x₀ := x₀) ⁻¹' U) α β) :
    Path.Homotopic (α.toPath.cast rfl heq.symm) β.toPath := by
  obtain ⟨F, hF_U⟩ := hAB
  set v : X := endpoint β with hv_def
  have hFv_cont := continuous_uncurry_basedPath F
  -- The endpoint-trace loop `L : Path v v`.
  have hF0_eq : (F (0 : I)).1 = α.1 := congrArg Subtype.val F.source
  have hF1_eq : (F (1 : I)).1 = β.1 := congrArg Subtype.val F.target
  have hv : v ∈ U := by simpa [v, hv_def, endpoint_def, hF1_eq] using hF_U 1
  let L : Path v v :=
    { toFun := fun t ↦ (F t).1 1
      continuous_toFun := by
        simpa using! hFv_cont.comp (continuous_id.prodMk (continuous_const (y := (1 : I))))
      source' := by rw [hF0_eq]; exact heq
      target' := by rw [hF1_eq]; rfl }
  have hL_refl : L.Homotopic (Path.refl v) :=
    hU_slsc.apply L (Path.refl v) (by rintro _ ⟨t, rfl⟩; exact hF_U t) (by
      rintro _ ⟨_, rfl⟩; simpa using! hv)
  -- Cast α.toPath to target `v`.
  let α' : Path x₀ v := α.toPath.cast rfl heq.symm
  -- The rectangle homotopy.
  let K_fn : I × I → X := fun ts ↦ (F (joinedInSLSC_uFn ts)).1 (joinedInSLSC_vFn ts)
  have K_fn_apply : ∀ ts : I × I, K_fn ts = (F (joinedInSLSC_uFn ts)).1 (joinedInSLSC_vFn ts) :=
    fun _ ↦ rfl
  have hK_cont : Continuous K_fn :=
    hFv_cont.comp (continuous_joinedInSLSC_uFn.prodMk continuous_joinedInSLSC_vFn)
  -- Auxiliary identities evaluating K at corners/edges.
  have hK_zero : ∀ s : I, K_fn (0, s) = (α'.trans L) s := fun s ↦ by
    rw [K_fn_apply, Path.trans_apply]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [dif_pos hs, joinedInSLSC_uFn_zero_left_eq_zero_of_le_half hs,
        joinedInSLSC_vFn_eq_two_mul_of_le_half hs, hF0_eq]; rfl
    · rw [dif_neg hs,
        joinedInSLSC_uFn_zero_left_eq_two_mul_sub_one_of_half_le (not_le.mp hs).le,
        joinedInSLSC_vFn_eq_one_of_half_le (not_le.mp hs).le]; rfl
  have hK_one : ∀ s : I, K_fn (1, s) = (β.toPath.trans (Path.refl v)) s := fun s ↦ by
    rw [K_fn_apply, Path.trans_apply, joinedInSLSC_uFn_one_left]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [dif_pos hs, joinedInSLSC_vFn_eq_two_mul_of_le_half hs, hF1_eq]; rfl
    · rw [dif_neg hs, joinedInSLSC_vFn_eq_one_of_half_le (not_le.mp hs).le, hF1_eq]; rfl
  have hK_at_zero : ∀ t : I, K_fn (t, 0) = x₀ := fun t ↦ by
    rw [K_fn_apply, joinedInSLSC_vFn_zero_right]
    exact (F (joinedInSLSC_uFn (t, 0))).2
  have hK_at_one : ∀ t : I, K_fn (t, 1) = v := fun t ↦ by
    rw [K_fn_apply, joinedInSLSC_uFn_one_right, joinedInSLSC_vFn_one_right, hF1_eq]; rfl
  -- The square deforms `α' ⬝ L` into `β ⬝ const`, and `L` is null-homotopic, so it collapses.
  exact (Path.Homotopic.trans_right_of_nullhomotopic hL_refl).symm.trans
    ((homotopic_of_continuous_square K_fn hK_cont hK_zero hK_one hK_at_zero hK_at_one).trans
      (Path.Homotopic.trans_refl β.toPath))


/-- Path components of `endpoint ⁻¹' U` are invariant under endpoint-preserving homotopy:
if `p ≃ q` are homotopic paths from `x₀` to `y ∈ U`, then the based paths `ofPath p` and
`ofPath q` lie in the same path component of `endpoint ⁻¹' U`. -/
public theorem pathComponentIn_ofPath_eq_of_homotopic
    {U : Set X} {y : X} (hy : y ∈ U)
    {p q : Path x₀ y} (h : Path.Homotopic p q) :
    pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath p) =
      pathComponentIn (endpoint (x₀ := x₀) ⁻¹' U) (ofPath q) :=
  pathComponentIn_congr (joinedIn_endpoint_preimage_of_homotopic x₀ hy h).symm

end BasedPath
