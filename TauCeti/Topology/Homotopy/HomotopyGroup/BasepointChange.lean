/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Collar

/-!
# Base-point change for higher homotopy groups

A path `γ` from `x` to `y` induces an isomorphism `π_n(X, x) ≃* π_n(X, y)`. This file proves
it, in the form
`TauCeti.homotopyGroupMulEquivOfPath : HomotopyGroup N X x ≃* HomotopyGroup N X y` for a finite
nonempty index type `N`, together with its functoriality: transport along a constant path is
the identity, transport along a concatenation is the composite, and transport depends only on
the homotopy class of the path.

The construction of the transported generalized loop and the key canonicity statement — a
homotopy of generalized loops whose boundary traces `γ` ends at the transported loop, up to
homotopy relative to the cube boundary — are in
`TauCeti/Topology/Homotopy/HomotopyGroup/Collar.lean`. Canonicity is what makes all four
properties routine: each is obtained by exhibiting *some* homotopy along the relevant path and
then invoking `TauCeti.GenLoop.HomotopyAlong.homotopic_transport`. The homotopies are:

* concatenating two collar homotopies in the time direction, for the concatenation law;
* the constant homotopy, for the constant path;
* concatenating two collar homotopies in the `i`-th cube direction, for multiplicativity.

Two statements are instead proved by deforming the *outer* half of the collar directly, using
the file-local `transportFamily`, the collar attached to a continuous family: that transport
respects homotopy of generalized loops, which is what makes it descend to homotopy groups, and
that it only depends on the homotopy class of the path.

The group structure enters only through Mathlib's `HomotopyGroup.mul_spec`, which computes a
product as the class of a concatenation `GenLoop.transAt i` in any cube direction `i`.

## Main declarations

* `TauCeti.homotopyGroupTransport`: transport of homotopy classes along a path, with
  `TauCeti.homotopyGroupTransport_refl`, `TauCeti.homotopyGroupTransport_trans` and
  `TauCeti.homotopyGroupTransport_congr`.
* `TauCeti.homotopyGroupEquivOfPath`: transport is a bijection, with inverse the transport
  along the reversed path.
* `TauCeti.homotopyGroupMulEquivOfPath`: **a path from `x` to `y` induces a group isomorphism
  `HomotopyGroup N X x ≃* HomotopyGroup N X y`.**
* `TauCeti.nonempty_homotopyGroupMulEquiv`: on a path-connected space, all the homotopy groups
  in a fixed dimension are isomorphic.

## References

This closes the base-point-change part of the higher-homotopy API requested in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 3, item 9. It is the higher-dimensional
analogue of Mathlib's `FundamentalGroup.fundamentalGroupMulEquivOfPath`; see Hatcher,
*Algebraic Topology*, Section 4.1.
-/

public section
noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

variable {N : Type*} [Fintype N] {X : Type*} [TopologicalSpace X] {x y : X}

/-! ### The collar of a continuous family -/

/-- The collar of a continuous family: `TauCeti.collar` at the constant radius `1 / 2`, so that
each member of the family is transported exactly as in
`TauCeti.GenLoop.transport_apply_eq`. -/
private def transportFamily {P : Type*} [TopologicalSpace P] (F : C(P × (I^N), X))
    (G : C(P × I, X)) (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) :
    C(P × (I^N), X) :=
  collar ⟨fun _ => 1 / 2, continuous_const⟩ F G (fun _ => le_rfl) hFG

private theorem transportFamily_apply {P : Type*} [TopologicalSpace P] (F : C(P × (I^N), X))
    (G : C(P × I, X)) (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) (p : P)
    (z : I^N) :
    transportFamily F G hFG (p, z) =
      if cubeRadius z ≤ 1 / 2 then F (p, cubeScale 2 z)
      else G (p, Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 1 / max (cubeRadius z) (1 / 2))) := by
  rw [transportFamily, collar_apply]
  norm_num

/-- At a parameter where the family restricts to `f` and the path family restricts to `γ`, the
collar of the family is the transport of `f` along `γ`. -/
private theorem transportFamily_apply_eq_transport {P : Type*} [TopologicalSpace P]
    (F : C(P × (I^N), X)) (G : C(P × I, X))
    (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) {p : P} {γ : Path x y}
    {f : Ω^ N X x} (hF : ∀ z, F (p, z) = f z) (hG : ∀ u, G (p, u) = γ u) (z : I^N) :
    transportFamily F G hFG (p, z) = GenLoop.transport γ f z := by
  rw [transportFamily_apply, GenLoop.transport_apply_eq]
  by_cases hz : cubeRadius z ≤ 1 / 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), ite_eq_left_of_eq_true _ _ (eq_true hz), hF]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hz),
      ite_eq_right_of_eq_false _ _ (eq_false hz), hG]

/-- On the cube boundary the collar of a family is the endpoint of the path family. -/
private theorem transportFamily_apply_of_mem_boundary {P : Type*} [TopologicalSpace P]
    (F : C(P × (I^N), X)) (G : C(P × I, X))
    (hFG : ∀ p, ∀ z ∈ Cube.boundary N, F (p, z) = G (p, 0)) (p : P) {z : I^N}
    (hz : z ∈ Cube.boundary N) : transportFamily F G hFG (p, z) = G (p, 1) := by
  have hu : cubeRadius z = 1 := (cubeRadius_eq_one_iff z).2 hz
  rw [transportFamily_apply, hu, ite_eq_right_of_eq_false _ _ (eq_false (by norm_num)),
    max_eq_left (by norm_num)]
  norm_num [Set.projIcc_right]

namespace GenLoop

/-! ### Transport respects homotopy -/

/-- Transport along a fixed path sends homotopic generalized loops to homotopic generalized
loops. -/
theorem homotopic_transport_of_homotopic (γ : Path x y) {f f' : Ω^ N X x}
    (h : GenLoop.Homotopic f f') :
    GenLoop.Homotopic (transport γ f) (transport γ f') := by
  obtain ⟨K⟩ := h
  have hFG : ∀ s : I, ∀ z ∈ Cube.boundary N,
      K.toContinuousMap (s, z) = (γ.toContinuousMap.comp ContinuousMap.snd) (s, 0) :=
    fun s z hz => (K.eq_fst s hz).trans ((f.2 z hz).trans γ.source.symm)
  refine ⟨⟨⟨transportFamily K.toContinuousMap
    (γ.toContinuousMap.comp ContinuousMap.snd) hFG, ?_, ?_⟩, ?_⟩⟩
  · intro z
    exact transportFamily_apply_eq_transport _ _ hFG (fun w => K.apply_zero w) (fun _ => rfl) z
  · intro z
    exact transportFamily_apply_eq_transport _ _ hFG (fun w => K.apply_one w) (fun _ => rfl) z
  · intro t z hz
    exact (transportFamily_apply_of_mem_boundary _ _ hFG t hz).trans
      (γ.target.trans ((transport γ f).2 z hz).symm)

/-- Transport along homotopic paths gives homotopic generalized loops. -/
theorem homotopic_transport_of_path_homotopic {γ δ : Path x y} (h : γ.Homotopic δ)
    (f : Ω^ N X x) : GenLoop.Homotopic (transport γ f) (transport δ f) := by
  obtain ⟨G⟩ := h
  have h0 : (0 : I) ∈ ({0, 1} : Set I) := by simp
  have h1 : (1 : I) ∈ ({0, 1} : Set I) := by simp
  have hFG : ∀ s : I, ∀ z ∈ Cube.boundary N,
      ((f : C(I^N, X)).comp ContinuousMap.snd) (s, z) = G.toContinuousMap (s, 0) :=
    fun s z hz => (f.2 z hz).trans (γ.source.symm.trans (G.eq_fst s h0).symm)
  refine ⟨⟨⟨transportFamily ((f : C(I^N, X)).comp ContinuousMap.snd) G.toContinuousMap hFG,
    ?_, ?_⟩, ?_⟩⟩
  · intro w
    exact transportFamily_apply_eq_transport _ _ hFG (fun _ => rfl) (fun u => G.apply_zero u) w
  · intro w
    exact transportFamily_apply_eq_transport _ _ hFG (fun _ => rfl) (fun u => G.apply_one u) w
  · intro t w hw
    exact (transportFamily_apply_of_mem_boundary _ _ hFG t hw).trans
      ((G.eq_fst t h1).trans (γ.target.trans ((transport γ f).2 w hw).symm))

/-! ### Functoriality of transport -/

/-- The constant homotopy is a homotopy along the constant path. -/
def HomotopyAlong.refl (f : Ω^ N X x) : HomotopyAlong (Path.refl x) f f where
  toHomotopy := ContinuousMap.Homotopy.refl (f : C(I^N, X))
  map_boundary _ z hz := f.2 z hz

/-- Transport along a constant path does nothing, up to homotopy. -/
theorem homotopic_transport_refl (f : Ω^ N X x) :
    GenLoop.Homotopic f (transport (Path.refl x) f) :=
  (HomotopyAlong.refl f).homotopic_transport

/-- Concatenating two homotopies along paths, in the time direction, gives a homotopy along the
concatenated path. -/
def HomotopyAlong.trans {w : X} {γ : Path x y} {δ : Path y w} {f : Ω^ N X x} {g : Ω^ N X y}
    {k : Ω^ N X w} (h₁ : HomotopyAlong γ f g) (h₂ : HomotopyAlong δ g k) :
    HomotopyAlong (γ.trans δ) f k where
  toHomotopy := h₁.toHomotopy.trans h₂.toHomotopy
  map_boundary t z hz := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact h₁.map_boundary _ z hz
    · exact h₂.map_boundary _ z hz

/-- Transport along a concatenation is the composite of the transports. -/
theorem homotopic_transport_trans {w : X} (γ : Path x y) (δ : Path y w) (f : Ω^ N X x) :
    GenLoop.Homotopic (transport δ (transport γ f)) (transport (γ.trans δ) f) :=
  ((collarHomotopyAlong γ f).trans (collarHomotopyAlong δ (transport γ f))).homotopic_transport

/-- Transport along the reversed path undoes transport, up to homotopy. -/
theorem homotopic_transport_symm_transport (γ : Path x y) (f : Ω^ N X x) :
    GenLoop.Homotopic (transport γ.symm (transport γ f)) f :=
  ((homotopic_transport_trans γ γ.symm f).trans
    (homotopic_transport_of_path_homotopic (Path.Homotopic.trans_symm γ) f)).trans
      (homotopic_transport_refl f).symm

/-- Transport undoes transport along the reversed path, up to homotopy. -/
theorem homotopic_transport_transport_symm (γ : Path x y) (f : Ω^ N X y) :
    GenLoop.Homotopic (transport γ (transport γ.symm f)) f :=
  ((homotopic_transport_trans γ.symm γ f).trans
    (homotopic_transport_of_path_homotopic (Path.Homotopic.symm_trans γ) f)).trans
      (homotopic_transport_refl f).symm

/-! ### Transport and concatenation of generalized loops -/

omit [Fintype N] in
/-- Evaluating Mathlib's concatenation of two generalized loops in the `i`-th cube direction:
by definition it is the half-and-half split of the `i`-th coordinate. -/
private theorem transAt_apply [DecidableEq N] (i : N) (f g : Ω^ N X x) (z : I^N) :
    _root_.GenLoop.transAt i f g z =
      if ((z i : I) : ℝ) ≤ 1 / 2
        then f (Function.update z i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * z i)))
        else g (Function.update z i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * z i - 1))) :=
  rfl

/-- Concatenating two homotopies along the same path in the `i`-th cube direction, as a homotopy
between the concatenated generalized loops. This is the underlying homotopy of
`TauCeti.GenLoop.HomotopyAlong.transAt`, split off so that `transAtHomotopy_apply` can expose
its values. -/
private def transAtHomotopy [DecidableEq N] (i : N) {γ : Path x y} {f f' : Ω^ N X x}
    {g g' : Ω^ N X y} (h₁ : HomotopyAlong γ f g) (h₂ : HomotopyAlong γ f' g') :
    ContinuousMap.Homotopy (_root_.GenLoop.transAt i f f' : C(I^N, X))
      (_root_.GenLoop.transAt i g g' : C(I^N, X)) where
  toContinuousMap := ⟨fun tz => if ((tz.2 i : I) : ℝ) ≤ 1 / 2
      then h₁.toHomotopy (tz.1,
        Function.update tz.2 i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * tz.2 i)))
      else h₂.toHomotopy (tz.1,
        Function.update tz.2 i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * tz.2 i - 1))), by
    refine Continuous.if_le ?_ ?_ (by fun_prop) continuous_const ?_
    · exact h₁.toHomotopy.continuous.comp' (continuous_fst.prodMk
        (continuous_snd.update i (continuous_projIcc.comp' (by fun_prop))))
    · exact h₂.toHomotopy.continuous.comp' (continuous_fst.prodMk
        (continuous_snd.update i (continuous_projIcc.comp' (by fun_prop))))
    · rintro ⟨t, z⟩ ht
      dsimp only at ht ⊢
      have h_double : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      have h_sub : (1 : ℝ) - 1 = 0 := by norm_num
      rw [ht, h_double, h_sub, Set.projIcc_right, Set.projIcc_left]
      exact (h₁.map_boundary t _ ⟨i, Or.inr (Function.update_self ..)⟩).trans
        (h₂.map_boundary t _ ⟨i, Or.inl (Function.update_self ..)⟩).symm⟩
  map_zero_left := by
    intro z
    dsimp only
    rw [_root_.GenLoop.coe_coe, transAt_apply]
    split_ifs
    · exact h₁.map_zero_left _
    · exact h₂.map_zero_left _
  map_one_left := by
    intro z
    dsimp only
    rw [_root_.GenLoop.coe_coe, transAt_apply]
    split_ifs
    · exact h₁.map_one_left _
    · exact h₂.map_one_left _

omit [Fintype N] in
/-- Evaluating the concatenated homotopy: it is the half-and-half split of the `i`-th
coordinate. -/
private theorem transAtHomotopy_apply [DecidableEq N] (i : N) {γ : Path x y} {f f' : Ω^ N X x}
    {g g' : Ω^ N X y} (h₁ : HomotopyAlong γ f g) (h₂ : HomotopyAlong γ f' g') (t : I) (z : I^N) :
    transAtHomotopy i h₁ h₂ (t, z) =
      if ((z i : I) : ℝ) ≤ 1 / 2
        then h₁.toHomotopy (t,
          Function.update z i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * z i)))
        else h₂.toHomotopy (t,
          Function.update z i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * z i - 1))) :=
  rfl

/-- Concatenating two homotopies along the *same* path, in the `i`-th cube direction, gives a
homotopy along that path between the concatenated generalized loops. -/
def HomotopyAlong.transAt [DecidableEq N] (i : N) {γ : Path x y} {f f' : Ω^ N X x}
    {g g' : Ω^ N X y} (h₁ : HomotopyAlong γ f g) (h₂ : HomotopyAlong γ f' g') :
    HomotopyAlong γ (_root_.GenLoop.transAt i f f') (_root_.GenLoop.transAt i g g') where
  toHomotopy := transAtHomotopy i h₁ h₂
  map_boundary t z hz := by
    rw [transAtHomotopy_apply]
    obtain ⟨j, hj⟩ := hz
    by_cases hji : j = i
    · subst hji
      rcases hj with hj | hj
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hj]; norm_num))]
        refine h₁.map_boundary t _ ⟨j, Or.inl ?_⟩
        rw [Function.update_self, hj]
        norm_num [Set.projIcc_left]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hj]; norm_num))]
        refine h₂.map_boundary t _ ⟨j, Or.inr ?_⟩
        rw [Function.update_self, hj]
        norm_num [Set.projIcc_right]
    · split_ifs
      · exact h₁.map_boundary t _ ⟨j, by rwa [Function.update_of_ne hji]⟩
      · exact h₂.map_boundary t _ ⟨j, by rwa [Function.update_of_ne hji]⟩

/-- Transport commutes with concatenation of generalized loops, up to homotopy. -/
theorem homotopic_transAt_transport [DecidableEq N] (i : N) (γ : Path x y) (f f' : Ω^ N X x) :
    GenLoop.Homotopic (_root_.GenLoop.transAt i (transport γ f) (transport γ f'))
      (transport γ (_root_.GenLoop.transAt i f f')) :=
  ((collarHomotopyAlong γ f).transAt i (collarHomotopyAlong γ f')).homotopic_transport

end GenLoop

/-! ### Base-point change on homotopy groups -/

/-- Transport of homotopy classes along a path. -/
def homotopyGroupTransport (γ : Path x y) :
    HomotopyGroup N X x → HomotopyGroup N X y :=
  Quotient.map (GenLoop.transport γ) fun _ _ h =>
    GenLoop.homotopic_transport_of_homotopic γ h

@[simp]
theorem homotopyGroupTransport_mk (γ : Path x y) (f : Ω^ N X x) :
    homotopyGroupTransport γ (⟦f⟧ : HomotopyGroup N X x) = ⟦GenLoop.transport γ f⟧ := by
  unfold homotopyGroupTransport
  rfl

/-- Transport along the constant path is the identity on homotopy groups. -/
@[simp]
theorem homotopyGroupTransport_refl :
    homotopyGroupTransport (N := N) (Path.refl x) = id := by
  funext a
  refine Quotient.inductionOn a fun f => ?_
  exact (Quotient.sound (GenLoop.homotopic_transport_refl f)).symm

/-- Transport along a concatenation of paths is the composite of the two transports. -/
@[simp]
theorem homotopyGroupTransport_trans {w : X} (γ : Path x y) (δ : Path y w) :
    homotopyGroupTransport (N := N) (γ.trans δ) =
      homotopyGroupTransport δ ∘ homotopyGroupTransport γ := by
  funext a
  refine Quotient.inductionOn a fun f => ?_
  exact (Quotient.sound (GenLoop.homotopic_transport_trans γ δ f)).symm

/-- Homotopic paths induce the same transport on homotopy groups. -/
theorem homotopyGroupTransport_congr {γ δ : Path x y} (h : γ.Homotopic δ) :
    homotopyGroupTransport (N := N) γ = homotopyGroupTransport δ := by
  funext a
  refine Quotient.inductionOn a fun f => ?_
  exact Quotient.sound (GenLoop.homotopic_transport_of_path_homotopic h f)

/-- Transport along a path is a bijection on homotopy classes, with inverse the transport
along the reversed path. -/
def homotopyGroupEquivOfPath (γ : Path x y) :
    HomotopyGroup N X x ≃ HomotopyGroup N X y where
  toFun := homotopyGroupTransport γ
  invFun := homotopyGroupTransport γ.symm
  left_inv a := by
    have h := congrFun (homotopyGroupTransport_trans (N := N) γ γ.symm) a
    rw [homotopyGroupTransport_congr (Path.Homotopic.trans_symm γ),
      homotopyGroupTransport_refl] at h
    exact h.symm
  right_inv a := by
    have h := congrFun (homotopyGroupTransport_trans (N := N) γ.symm γ) a
    rw [homotopyGroupTransport_congr (Path.Homotopic.symm_trans γ),
      homotopyGroupTransport_refl] at h
    exact h.symm

@[simp]
theorem homotopyGroupEquivOfPath_mk (γ : Path x y) (f : Ω^ N X x) :
    homotopyGroupEquivOfPath γ (⟦f⟧ : HomotopyGroup N X x) = ⟦GenLoop.transport γ f⟧ := by
  unfold homotopyGroupEquivOfPath
  exact homotopyGroupTransport_mk γ f

@[simp]
theorem homotopyGroupEquivOfPath_symm_mk (γ : Path x y) (f : Ω^ N X y) :
    (homotopyGroupEquivOfPath γ).symm (⟦f⟧ : HomotopyGroup N X y) =
      ⟦GenLoop.transport γ.symm f⟧ := by
  unfold homotopyGroupEquivOfPath
  exact homotopyGroupTransport_mk γ.symm f

/-- **Base-point change for higher homotopy groups.** A path from `x` to `y` induces a group
isomorphism between the homotopy groups based at `x` and at `y`. -/
def homotopyGroupMulEquivOfPath [Nonempty N] [DecidableEq N] (γ : Path x y) :
    HomotopyGroup N X x ≃* HomotopyGroup N X y where
  toEquiv := homotopyGroupEquivOfPath γ
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    -- Mathlib's `HomotopyGroup.mul_spec` itself records a TODO to replace this quotient-wrapper
    -- definitional equality with a `HomotopyGroup.mk` API. Until that exists, expose the wrapper
    -- here so that `mul_spec` can rewrite both products with their intended group instances.
    change homotopyGroupTransport γ
        (((· * ·) : _ → _ → HomotopyGroup N X x) ⟦p⟧ ⟦q⟧) =
      ((· * ·) : _ → _ → HomotopyGroup N X y)
        (homotopyGroupTransport γ ⟦p⟧) (homotopyGroupTransport γ ⟦q⟧)
    rw [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N), homotopyGroupTransport_mk,
      homotopyGroupTransport_mk, homotopyGroupTransport_mk,
      _root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    exact (Quotient.sound (GenLoop.homotopic_transAt_transport _ γ q p)).symm

/-- The multiplicative base-point-change equivalence acts by transport. -/
@[simp]
theorem homotopyGroupMulEquivOfPath_apply [Nonempty N] [DecidableEq N] (γ : Path x y)
    (a : HomotopyGroup N X x) :
    homotopyGroupMulEquivOfPath γ a = homotopyGroupTransport γ a := by
  unfold homotopyGroupMulEquivOfPath homotopyGroupEquivOfPath
  rfl

/-- The inverse multiplicative base-point-change equivalence acts by transport along the
reversed path. -/
@[simp]
theorem homotopyGroupMulEquivOfPath_symm_apply [Nonempty N] [DecidableEq N] (γ : Path x y)
    (a : HomotopyGroup N X y) :
    (homotopyGroupMulEquivOfPath γ).symm a = homotopyGroupTransport γ.symm a := by
  unfold homotopyGroupMulEquivOfPath homotopyGroupEquivOfPath
  rfl

/-- The multiplicative equivalence for a constant path is the identity. -/
@[simp]
theorem homotopyGroupMulEquivOfPath_refl [Nonempty N] [DecidableEq N] :
    homotopyGroupMulEquivOfPath (N := N) (Path.refl x) =
      MulEquiv.refl (HomotopyGroup N X x) := by
  ext a
  rw [homotopyGroupMulEquivOfPath_apply, homotopyGroupTransport_refl]
  rfl

/-- The multiplicative equivalence for a concatenated path is the composite equivalence. -/
@[simp]
theorem homotopyGroupMulEquivOfPath_trans [Nonempty N] [DecidableEq N] {w : X}
    (γ : Path x y) (δ : Path y w) :
    homotopyGroupMulEquivOfPath (N := N) (γ.trans δ) =
      (homotopyGroupMulEquivOfPath γ).trans (homotopyGroupMulEquivOfPath δ) := by
  ext a
  rw [homotopyGroupMulEquivOfPath_apply, MulEquiv.trans_apply,
    homotopyGroupMulEquivOfPath_apply, homotopyGroupMulEquivOfPath_apply]
  exact congrFun (homotopyGroupTransport_trans γ δ) a

/-- Homotopic paths induce the same multiplicative base-point-change equivalence. -/
theorem homotopyGroupMulEquivOfPath_congr [Nonempty N] [DecidableEq N]
    {γ δ : Path x y} (h : γ.Homotopic δ) :
    homotopyGroupMulEquivOfPath (N := N) γ = homotopyGroupMulEquivOfPath δ := by
  ext a
  rw [homotopyGroupMulEquivOfPath_apply, homotopyGroupMulEquivOfPath_apply]
  exact congrFun (homotopyGroupTransport_congr h) a

/-- Reversing the path gives the inverse multiplicative equivalence. -/
theorem homotopyGroupMulEquivOfPath_symm [Nonempty N] [DecidableEq N] (γ : Path x y) :
    (homotopyGroupMulEquivOfPath γ).symm = homotopyGroupMulEquivOfPath (N := N) γ.symm := by
  ext a
  rw [homotopyGroupMulEquivOfPath_symm_apply, homotopyGroupMulEquivOfPath_apply]

omit [Fintype N] in
/-- On a path-connected space the homotopy groups in a fixed dimension at any two base points
are isomorphic. -/
theorem nonempty_homotopyGroupMulEquiv [Finite N] [Nonempty N] [DecidableEq N]
    [PathConnectedSpace X] :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) := by
  have : Fintype N := Fintype.ofFinite N
  exact ⟨homotopyGroupMulEquivOfPath (PathConnectedSpace.somePath x y)⟩

end TauCeti
