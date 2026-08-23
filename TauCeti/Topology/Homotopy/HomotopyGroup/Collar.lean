/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Transporting a generalized loop along a path

Let `γ : Path x y` and let `f : Ω^ N X x` be a generalized loop based at `x`. This file
constructs the generalized loop `TauCeti.GenLoop.transport γ f : Ω^ N X y` obtained by shrinking
`f` into the half-size cube and running `γ` outwards along the resulting collar, together with
the homotopy realising the deformation, and proves that this construction is *canonical*: any
homotopy whose boundary traces `γ` ends, up to homotopy relative to the cube boundary, at
`transport γ f`.

Everything is written in terms of the radial coordinate `TauCeti.cubeRad` of
`TauCeti/Topology/Homotopy/Cube/Radius.lean`, which is `1` exactly on `Cube.boundary N`. The
basic gadget is `TauCeti.collar`: given a radius function `r ≥ 1/2`, an inner family `F` of maps
on the cube and an outer family `G` of paths, it returns the map sending a point of radius at
most `r` to `F` at the point rescaled by `1 / r`, and a point of radius `u > r` to `G` at the
reparametrised time `2 - 2 * r / u`. The two branches agree where `u = r`, because rescaling by
`1 / r` lands on the cube boundary, where `F` is required to equal `G` at time `0`.

With the shrinking radius `r t = (2 - t) / 2` this is the collar homotopy
`TauCeti.GenLoop.collarHomotopy γ f`, which starts at `f`, traces `γ` on the cube boundary, and
ends at the transported loop, which is *defined* as its value at time `1`.

`TauCeti.GenLoop.HomotopyAlong γ f g` packages the data of a homotopy from `f` to `g` whose
restriction to the cube boundary is `γ`. Canonicity, `HomotopyAlong.homotopic_transport`, is the
homotopy extension property of the pair `(I^N, Cube.boundary N)` in the only form needed here.
It is proved by an explicit radial retraction `TauCeti.cubeRetract` of the top face of the
cylinder `I × I^N` onto its bottom face together with its sides: composing a homotopy along `γ`
with that retraction reproduces `transport γ f` on the nose, and the straight-line homotopy in
the convex cylinder from the identity to the retraction is stationary on the cube boundary, so
it descends to a homotopy relative to the boundary.

## Main declarations

* `TauCeti.collar`: the collar construction on a parametrised family.
* `TauCeti.GenLoop.collarHomotopy`: the collar homotopy attached to `γ` and `f`.
* `TauCeti.GenLoop.transport`: **the generalized loop `f` transported along `γ`.**
* `TauCeti.GenLoop.HomotopyAlong`: a homotopy of generalized loops whose boundary traces `γ`.
* `TauCeti.GenLoop.collarHomotopyAlong`: the collar homotopy, as such a homotopy.
* `TauCeti.cubeRetract`: the radial retraction of the top face of the cylinder onto the union of
  its bottom face and its sides.
* `TauCeti.GenLoop.HomotopyAlong.homotopic_transport`: **any homotopy along `γ` starting at `f`
  ends at a loop homotopic to `transport γ f`.**

## References

This is the analytic core of the base-point-change isomorphisms of higher homotopy groups
requested in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 3, item 9. The construction is
the classical one; see Hatcher, *Algebraic Topology*, Section 4.1.
-/

public section
noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

variable {N : Type*} [Fintype N] {X : Type*} [TopologicalSpace X] {x y : X}

/-! ### The collar construction -/

/-- The collar construction. Given a radius function `r ≥ 1/2`, a family `F` of maps on the cube
and a family `G` of paths agreeing with `F` on the cube boundary at time `0`, this sends a cube
point of radius at most `r` to `F` at the point rescaled by `1 / r`, and a cube point of larger
radius `u` to `G` at the time `2 - 2 * r / u`. -/
@[expose] def collar {P : Type*} [TopologicalSpace P] (r : C(P, ℝ))
    (F : C(P × (I^N), X)) (G : C(P × I, X)) (hr : ∀ p, 1 / 2 ≤ r p)
    (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) :
    C(P × (I^N), X) where
  toFun pz :=
    if cubeRad pz.2 ≤ r pz.1 then F (pz.1, cubeScale (1 / r pz.1) pz.2)
    else G (pz.1, Set.projIcc (0 : ℝ) 1 zero_le_one
      (2 - 2 * r pz.1 / max (cubeRad pz.2) (1 / 2)))
  continuous_toFun := by
    have hrpos : ∀ p, (0 : ℝ) < r p := fun p => lt_of_lt_of_le (by norm_num) (hr p)
    have h1 : Continuous fun pz : P × (I^N) => (1 / r pz.1 : ℝ) :=
      continuous_const.div (r.continuous.comp continuous_fst) fun pz => (hrpos pz.1).ne'
    have hmax : ∀ pz : P × (I^N), (0 : ℝ) < max (cubeRad pz.2) (1 / 2) := fun _ =>
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have h2 : Continuous fun pz : P × (I^N) =>
        (2 - 2 * r pz.1 / max (cubeRad pz.2) (1 / 2) : ℝ) := by
      refine continuous_const.sub (Continuous.div (by fun_prop) ?_ fun pz => (hmax pz).ne')
      exact (continuous_cubeRad.comp continuous_snd).max continuous_const
    refine Continuous.if_le
      (F.continuous.comp (continuous_fst.prodMk
        (continuous_cubeScale.comp (h1.prodMk continuous_snd))))
      (G.continuous.comp (continuous_fst.prodMk (continuous_projIcc.comp h2)))
      (continuous_cubeRad.comp continuous_snd) (r.continuous.comp continuous_fst) ?_
    rintro ⟨p, z⟩ hpz
    dsimp only at hpz ⊢
    have hrp := hrpos p
    have hbd : cubeScale (1 / r p) z ∈ Cube.boundary N := by
      rw [← cubeRad_eq_one_iff,
        cubeRad_cubeScale (by positivity) (by rw [hpz, one_div, inv_mul_cancel₀ hrp.ne']),
        hpz, one_div, inv_mul_cancel₀ hrp.ne']
    rw [hFG p _ hbd, hpz, max_eq_left (hr p)]
    congr 1
    have hzero : (2 : ℝ) - 2 * r p / r p = 0 := by
      rw [mul_div_assoc, div_self hrp.ne']
      ring
    rw [hzero, projIcc_zero]

theorem collar_apply {P : Type*} [TopologicalSpace P] (r : C(P, ℝ))
    (F : C(P × (I^N), X)) (G : C(P × I, X)) (hr : ∀ p, 1 / 2 ≤ r p)
    (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) (p : P) (z : I^N) :
    collar r F G hr hFG (p, z) =
      if cubeRad z ≤ r p then F (p, cubeScale (1 / r p) z)
      else G (p, Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 2 * r p / max (cubeRad z) (1 / 2))) :=
  rfl

namespace GenLoop

/-! ### The collar homotopy and the transported loop -/

/-- The collar homotopy of a generalized loop `f` along a path `γ`: at time `t` it is `f`
shrunk into the cube of radius `(2 - t) / 2`, with `γ` restricted to `[0, t]` filling the
collar outside. -/
@[expose] def collarHomotopy (γ : Path x y) (f : Ω^ N X x) : C(I × (I^N), X) :=
  collar ⟨fun t : I => (2 - (t : ℝ)) / 2, by fun_prop⟩
    ((f : C(I^N, X)).comp ContinuousMap.snd) (γ.toContinuousMap.comp ContinuousMap.snd)
    (fun t => by have := t.2.2; dsimp; linarith)
    (fun _ z hz => by simpa using (f.2 z hz).trans γ.source.symm)

theorem collarHomotopy_apply (γ : Path x y) (f : Ω^ N X x) (t : I) (z : I^N) :
    collarHomotopy γ f (t, z) =
      if cubeRad z ≤ (2 - (t : ℝ)) / 2 then f (cubeScale (1 / ((2 - (t : ℝ)) / 2)) z)
      else γ (Set.projIcc (0 : ℝ) 1 zero_le_one
        (2 - 2 * ((2 - (t : ℝ)) / 2) / max (cubeRad z) (1 / 2))) :=
  rfl

@[simp]
theorem collarHomotopy_zero (γ : Path x y) (f : Ω^ N X x) (z : I^N) :
    collarHomotopy γ f (0, z) = f z := by
  rw [collarHomotopy_apply, ite_eq_left_of_eq_true _ _ (eq_true (by
    show cubeRad z ≤ (2 - ((0 : I) : ℝ)) / 2
    have := cubeRad_le_one z
    norm_num
    linarith))]
  norm_num

/-- On the cube boundary the collar homotopy traces the path `γ`. -/
theorem collarHomotopy_boundary (γ : Path x y) (f : Ω^ N X x) (t : I) {z : I^N}
    (hz : z ∈ Cube.boundary N) : collarHomotopy γ f (t, z) = γ t := by
  have hu : cubeRad z = 1 := (cubeRad_eq_one_iff z).2 hz
  rw [collarHomotopy_apply, hu]
  have ht0 := t.2.1
  have ht1 := t.2.2
  by_cases h : (1 : ℝ) ≤ (2 - (t : ℝ)) / 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hc0 : ((0 : I) : ℝ) = 0 := by norm_num
    have ht : t = 0 := Subtype.ext (by rw [hc0]; linarith)
    subst ht
    rw [show (1 : ℝ) / ((2 - ((0 : I) : ℝ)) / 2) = 1 by rw [hc0]; norm_num, cubeScale_one,
      γ.source]
    exact f.2 z hz
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), max_eq_left (by norm_num)]
    congr 1
    rw [show (2 : ℝ) - 2 * ((2 - (t : ℝ)) / 2) / 1 = (t : ℝ) by ring]
    exact Set.projIcc_val _ _

/-- **The generalized loop `f` transported along the path `γ`**: the value at time `1` of the
collar homotopy, a generalized loop based at the far endpoint of `γ`. -/
@[expose] def transport (γ : Path x y) (f : Ω^ N X x) : Ω^ N X y :=
  ⟨(collarHomotopy γ f).curry 1, fun _z hz =>
    (collarHomotopy_boundary γ f 1 hz).trans γ.target⟩

theorem transport_apply (γ : Path x y) (f : Ω^ N X x) (z : I^N) :
    transport γ f z = collarHomotopy γ f (1, z) := rfl

theorem transport_apply_eq (γ : Path x y) (f : Ω^ N X x) (z : I^N) :
    transport γ f z =
      if cubeRad z ≤ 1 / 2 then f (cubeScale 2 z)
      else γ (Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 1 / max (cubeRad z) (1 / 2))) := by
  rw [transport_apply, collarHomotopy_apply, show ((1 : I) : ℝ) = 1 by norm_num]
  norm_num

end GenLoop

/-! ### The radial retraction of the cylinder -/

/-- The radial retraction of the top face of the cylinder `I × I^N` onto the union of its
bottom face and its sides, obtained by projecting away from the point sitting at height `2`
above the centre of the cube. It is the identity on the cube boundary. -/
@[expose] def cubeRetract : C(I^N, I × (I^N)) where
  toFun z :=
    if cubeRad z ≤ 1 / 2 then (0, cubeScale 2 z)
    else (Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 1 / max (cubeRad z) (1 / 2)),
      cubeScale (1 / max (cubeRad z) (1 / 2)) z)
  continuous_toFun := by
    have hmax : ∀ z : I^N, (0 : ℝ) < max (cubeRad z) (1 / 2) := fun _ =>
      lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hc : Continuous fun z : I^N => max (cubeRad z) (1 / 2 : ℝ) :=
      continuous_cubeRad.max continuous_const
    refine Continuous.if_le ?_ ?_ continuous_cubeRad continuous_const ?_
    · exact continuous_const.prodMk (continuous_cubeScale.comp'
        (continuous_const.prodMk continuous_id))
    · refine Continuous.prodMk (continuous_projIcc.comp' ?_) ?_
      · exact continuous_const.sub (continuous_const.div hc fun z => (hmax z).ne')
      · exact continuous_cubeScale.comp'
          ((continuous_const.div hc fun z => (hmax z).ne').prodMk continuous_id)
    · intro z hz
      rw [hz, max_eq_left (by norm_num)]
      norm_num [projIcc_zero]

theorem cubeRetract_apply (z : I^N) :
    cubeRetract z =
      if cubeRad z ≤ 1 / 2 then ((0 : I), cubeScale 2 z)
      else (Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 1 / max (cubeRad z) (1 / 2)),
        cubeScale (1 / max (cubeRad z) (1 / 2)) z) := rfl

theorem cubeRetract_of_mem_boundary {z : I^N} (hz : z ∈ Cube.boundary N) :
    cubeRetract z = (1, z) := by
  have hu : cubeRad z = 1 := (cubeRad_eq_one_iff z).2 hz
  rw [cubeRetract_apply, hu, ite_eq_right_of_eq_false _ _ (eq_false (by norm_num)),
    max_eq_left (by norm_num)]
  norm_num [projIcc_one]

namespace GenLoop

/-! ### Homotopies along a path, and canonicity of the transported loop -/

/-- A homotopy from a generalized loop `f` based at `x` to a generalized loop `g` based at `y`
whose restriction to the cube boundary traces the path `γ` from `x` to `y`. -/
structure HomotopyAlong (γ : Path x y) (f : Ω^ N X x) (g : Ω^ N X y) where
  /-- the underlying continuous map on the cylinder -/
  map : C(I × (I^N), X)
  /-- the homotopy starts at `f` -/
  map_zero : ∀ z, map (0, z) = f z
  /-- the homotopy ends at `g` -/
  map_one : ∀ z, map (1, z) = g z
  /-- on the cube boundary the homotopy traces `γ` -/
  map_boundary : ∀ t : I, ∀ z ∈ Cube.boundary N, map (t, z) = γ t

/-- The collar homotopy is a homotopy along `γ` from `f` to the transported loop. -/
def collarHomotopyAlong (γ : Path x y) (f : Ω^ N X x) :
    HomotopyAlong γ f (transport γ f) where
  map := collarHomotopy γ f
  map_zero := collarHomotopy_zero γ f
  map_one z := (transport_apply γ f z).symm
  map_boundary t _ hz := collarHomotopy_boundary γ f t hz

/-- Composing a homotopy along `γ` with the radial retraction of the cylinder reproduces the
transported loop exactly. -/
theorem HomotopyAlong.map_cubeRetract {γ : Path x y} {f : Ω^ N X x} {g : Ω^ N X y}
    (h : HomotopyAlong γ f g) (z : I^N) : h.map (cubeRetract z) = transport γ f z := by
  rw [cubeRetract_apply, transport_apply_eq]
  by_cases hz : cubeRad z ≤ 1 / 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), ite_eq_left_of_eq_true _ _ (eq_true hz)]
    exact h.map_zero _
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hz), ite_eq_right_of_eq_false _ _ (eq_false hz)]
    have hmax : max (cubeRad z) (1 / 2 : ℝ) = cubeRad z := max_eq_left (le_of_not_ge hz)
    have hpos : (0 : ℝ) < cubeRad z := lt_of_lt_of_le (by norm_num) (le_of_not_ge hz)
    refine h.map_boundary _ _ ?_
    rw [← cubeRad_eq_one_iff, hmax,
      cubeRad_cubeScale (by positivity) (by rw [one_div, inv_mul_cancel₀ hpos.ne']),
      one_div, inv_mul_cancel₀ hpos.ne']

/-- **Canonicity of the transported loop.** A homotopy along `γ` starting at `f` ends at a
generalized loop homotopic, relative to the cube boundary, to `transport γ f`. -/
theorem HomotopyAlong.homotopic_transport {γ : Path x y} {f : Ω^ N X x} {g : Ω^ N X y}
    (h : HomotopyAlong γ f g) : GenLoop.Homotopic g (transport γ f) := by
  have hcont : Continuous fun sz : I × (I^N) =>
      ((unitIntervalLerp sz.1 1 (cubeRetract sz.2).1 : I),
        (fun i => unitIntervalLerp sz.1 (sz.2 i) ((cubeRetract sz.2).2 i) : I^N)) := by
    refine Continuous.prodMk ?_ (continuous_pi fun i => ?_)
    · exact continuous_unitIntervalLerp.comp' (continuous_fst.prodMk (continuous_const.prodMk
        (continuous_fst.comp (cubeRetract.continuous.comp continuous_snd))))
    · exact continuous_unitIntervalLerp.comp' (continuous_fst.prodMk
        (((continuous_apply i).comp continuous_snd).prodMk
          ((continuous_apply i).comp (continuous_snd.comp
            (cubeRetract.continuous.comp continuous_snd)))))
  refine ⟨⟨⟨⟨fun sz => h.map (unitIntervalLerp sz.1 1 (cubeRetract sz.2).1,
      fun i => unitIntervalLerp sz.1 (sz.2 i) ((cubeRetract sz.2).2 i)),
      h.map.continuous.comp hcont⟩, ?_, ?_⟩, ?_⟩⟩
  · intro z
    simp only [unitIntervalLerp_zero]
    exact h.map_one z
  · intro z
    simp only [unitIntervalLerp_one]
    exact h.map_cubeRetract z
  · intro t z hz
    change h.map (unitIntervalLerp t 1 (cubeRetract z).1,
      fun i => unitIntervalLerp t (z i) ((cubeRetract z).2 i)) = g z
    simp only [cubeRetract_of_mem_boundary hz, unitIntervalLerp_self]
    exact h.map_one z

end GenLoop

end TauCeti
