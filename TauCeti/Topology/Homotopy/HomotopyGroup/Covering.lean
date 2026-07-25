/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Homotopy.Cube
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# A covering map induces isomorphisms on higher homotopy groups

Let `p : E → X` be a covering map and let `e : E`. This file shows that postcomposition with
`p` identifies the homotopy groups of `E` at `e` with those of `X` at `p e`, in every
dimension `≥ 2`.

Both halves are consequences of Mathlib's covering-space lifting toolkit.

* **Injectivity** holds already in dimension `≥ 1`. Two generalized loops in `E` whose
  postcompositions with `p` are homotopic relative to the cube boundary are themselves
  homotopic relative to the cube boundary: this is Mathlib's
  `IsCoveringMap.homotopicRel_iff_comp`, whose hypothesis "the two maps agree at a point of
  the relative set" is supplied by the corner `0` of the cube, where both generalized loops
  take the value `e`.
* **Surjectivity** needs dimension `≥ 2`. Splitting off one cube coordinate turns a
  generalized loop `f : I^N → X` into a homotopy `I × I^{j ≠ i} → X` starting at the constant
  map `p e`. Mathlib's `IsCoveringMap.liftHomotopyRel` lifts it relative to the boundary of the
  remaining coordinates, so the lift is constant there and at both ends of the split
  coordinate. A second coordinate, supplied by `Nontrivial N`, ensures that every boundary face
  is of one of these forms.

The conclusion is packaged as a multiplicative equivalence `π_n(E, e) ≃* π_n(X, p e)` for
`n ≥ 2`, in the general indexed form and in the `Fin (n + 2)` form.

This is Stage 3, item 10 of the Tau Ceti universal-covers roadmap
(`TauCetiRoadmap/UniversalCovers/README.md`): "`p_* : π_n(X̃) ≅ π_n(X)` for `n ≥ 2`, any
cover".

## Main declarations

* `TauCeti.GenLoop.map_homotopic_iff`: postcomposition with a covering map reflects (and
  preserves) homotopy of generalized loops.
* `TauCeti.GenLoop.map_surjective`: in dimension `≥ 2`, every generalized loop in the base
  lifts to a generalized loop in the total space based at a prescribed point of the fibre.
* `TauCeti.HomotopyGroup.map_injective`, `TauCeti.HomotopyGroup.map_surjective`: the induced
  map on homotopy classes.
* `TauCeti.IsCoveringMap.homotopyGroupMulEquiv`: the isomorphism
  `HomotopyGroup N E e ≃* HomotopyGroup N X (p e)` for `[Nontrivial N]`.
* `TauCeti.IsCoveringMap.homotopyGroupPiMulEquiv`: its `π_(n + 2)` form.

## References

The lifting machinery consumed here (`IsCoveringMap.liftHomotopyRel`,
`IsCoveringMap.homotopicRel_iff_comp`) is Junyan Xu's
covering-space API in `Mathlib.Topology.Homotopy.Lifting` and
`Mathlib.Topology.Covering.Basic`. Compare Proposition 4.1 of [hatcher02].
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X} {e : E}

namespace GenLoop

/-- Postcomposition with a covering map `p` neither creates nor destroys homotopies between
generalized loops in the total space: two generalized loops based at `e` are homotopic
relative to the cube boundary if and only if their postcompositions with `p` are.

The reverse implication is `TauCeti.GenLoop.map_homotopic` and needs no hypothesis on `p`;
the forward implication lifts the homotopy, using that both generalized loops take the value
`e` at the corner `0` of the cube. -/
@[simp]
theorem map_homotopic_iff [Nonempty N] (hp : IsCoveringMap p) {F G : Ω^ N E e} :
    _root_.GenLoop.Homotopic (map ⟨p, hp.continuous⟩ rfl F) (map ⟨p, hp.continuous⟩ rfl G) ↔
      _root_.GenLoop.Homotopic F G :=
  (hp.homotopicRel_iff_comp (f₀ := (F : C(I^N, E))) (f₁ := (G : C(I^N, E)))
    ⟨0, zero_mem_cubeBoundary,
      (_root_.GenLoop.boundary F 0 zero_mem_cubeBoundary).trans
        (_root_.GenLoop.boundary G 0 zero_mem_cubeBoundary).symm⟩).symm

/-- Every generalized loop in the base of a covering map lifts, in dimensions `≥ 2`, to a
generalized loop in the total space based at any prescribed point `e` of the fibre.

The index type is assumed nontrivial (equivalently: the dimension is at least `2`), so after
splitting off one coordinate there is another coordinate whose boundary can be held fixed by a
relative homotopy lift. In dimension `1` the statement is false: a loop in the base lifts to a
*path* in the total space, whose endpoint need not return to `e`. -/
theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) (f : Ω^ N X (p e)) :
    ∃ F : Ω^ N E e, map ⟨p, hp.continuous⟩ rfl F = f := by
  classical
  -- Read `f` as a homotopy in the `i`-th cube coordinate; it starts at the constant map `p e`.
  let i := Classical.arbitrary N
  letI : Nonempty { j // j ≠ i } := ⟨⟨(exists_ne i).choose, (exists_ne i).choose_spec⟩⟩
  let q : C(I × I^{ j // j ≠ i }, X) := (f : C(I^N, X)).comp (Cube.insertAt i)
  let cX : C(I^{ j // j ≠ i }, X) := .const _ (p e)
  let cE : C(I^{ j // j ≠ i }, E) := .const _ e
  let qRel : cX.HomotopyRel cX (Cube.boundary { j // j ≠ i }) :=
    { toContinuousMap := q
      map_zero_left := fun a =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inl rfl)))
      map_one_left := fun a =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inr rfl)))
      prop' := fun t a ha =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inr ha)) }
  let QRel : cE.HomotopyRel cE (Cube.boundary { j // j ≠ i }) :=
    hp.liftHomotopyRel qRel ⟨0, zero_mem_cubeBoundary, rfl⟩
      (funext fun _ => rfl) (funext fun _ => rfl)
  let Q : C(I × I^{ j // j ≠ i }, E) := QRel.toContinuousMap
  have hQ : p ∘ Q = q := by
    simp only [Q, QRel, IsCoveringMap.liftHomotopyRel]
    exact hp.liftHomotopy_lifts _ _ _
  let F : C(I^N, E) := Q.comp (Cube.splitAt i)
  have hF_apply (y : I^N) : F y = QRel (Cube.splitAt i y) := rfl
  have hpF : ∀ y, p (F y) = f y := fun y => by
    calc
      p (F y) = p (Q (Cube.splitAt i y)) := rfl
      _ = q (Cube.splitAt i y) := congrFun hQ (Cube.splitAt i y)
      _ = f y := congr_arg f (Homeomorph.symm_apply_apply (Cube.splitAt i) y)
  -- The relative lift is constant on every boundary face.
  have hbd : ∀ y ∈ Cube.boundary N, F y = e := by
    rintro y ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · have ht : (Cube.splitAt i y).1 = 0 := by
          simpa only [Homeomorph.funSplitAt_apply] using hj
        have hz : Cube.splitAt i y = (0, (Cube.splitAt i y).2) := Prod.ext ht rfl
        rw [hF_apply, hz]
        exact QRel.apply_zero _
      · have ht : (Cube.splitAt i y).1 = 1 := by
          simpa only [Homeomorph.funSplitAt_apply] using hj
        have hz : Cube.splitAt i y = (1, (Cube.splitAt i y).2) := Prod.ext ht rfl
        rw [hF_apply, hz]
        exact QRel.apply_one _
    · have ha : (Cube.splitAt i y).2 ∈ Cube.boundary { j // j ≠ i } :=
        ⟨⟨j, hji⟩, by simpa only [Homeomorph.funSplitAt_apply] using hj⟩
      rw [hF_apply]
      exact QRel.prop (Cube.splitAt i y).1 (Cube.splitAt i y).2 ha
  exact ⟨⟨F, hbd⟩, _root_.GenLoop.ext _ _ hpF⟩

end GenLoop

namespace HomotopyGroup

/-- A covering map is injective on homotopy groups in every positive dimension. -/
theorem map_injective [Nonempty N] (hp : IsCoveringMap p) :
    Function.Injective (map (N := N) (⟨p, hp.continuous⟩ : C(E, X)) (rfl : p e = p e)) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun F G h => ?_
  exact Quotient.sound ((GenLoop.map_homotopic_iff hp).1 (Quotient.exact h))

/-- A covering map is surjective on homotopy groups in dimensions `≥ 2`. -/
theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) :
    Function.Surjective (map (N := N) (⟨p, hp.continuous⟩ : C(E, X)) (rfl : p e = p e)) := by
  refine Quotient.ind fun f => ?_
  obtain ⟨F, hF⟩ := GenLoop.map_surjective hp f
  exact ⟨⟦F⟧, by rw [map_mk, hF]⟩

end HomotopyGroup

/-- **A covering map induces an isomorphism on homotopy groups in dimensions `≥ 2`.**

Postcomposition with `p` is a group isomorphism `π_N(E, e) ≃* π_N(X, p e)` whenever the index
type `N` has at least two elements. No connectivity hypothesis on `E` or `X` is needed: both
halves are statements about lifting cubes. -/
noncomputable def IsCoveringMap.homotopyGroupMulEquiv [DecidableEq N] [Nontrivial N]
    (hp : _root_.IsCoveringMap p) (e : E) :
    HomotopyGroup N E e ≃* HomotopyGroup N X (p e) := by
  classical
  exact MulEquiv.ofBijective (HomotopyGroup.mapHom (⟨p, hp.continuous⟩ : C(E, X)) rfl)
    ⟨HomotopyGroup.map_injective hp, HomotopyGroup.map_surjective hp⟩

@[simp]
theorem IsCoveringMap.homotopyGroupMulEquiv_apply [DecidableEq N] [Nontrivial N]
    (hp : _root_.IsCoveringMap p) (e : E) (a : HomotopyGroup N E e) :
    IsCoveringMap.homotopyGroupMulEquiv hp e a =
      HomotopyGroup.map (⟨p, hp.continuous⟩ : C(E, X)) rfl a :=
  (rfl)

/-- The `π_(n + 2)` form of `TauCeti.IsCoveringMap.homotopyGroupMulEquiv`: a covering map
`p : E → X` induces `π_(n + 2)(E, e) ≃* π_(n + 2)(X, p e)` for every `n : ℕ`. -/
noncomputable def IsCoveringMap.homotopyGroupPiMulEquiv (hp : _root_.IsCoveringMap p)
    (e : E) (n : ℕ) : π_ (n + 2) E e ≃* π_ (n + 2) X (p e) :=
  IsCoveringMap.homotopyGroupMulEquiv hp e

@[simp]
theorem IsCoveringMap.homotopyGroupPiMulEquiv_apply (hp : _root_.IsCoveringMap p) (e : E)
    (n : ℕ) (a : π_ (n + 2) E e) :
    IsCoveringMap.homotopyGroupPiMulEquiv hp e n a =
      HomotopyGroup.map (⟨p, hp.continuous⟩ : C(E, X)) rfl a :=
  (rfl)

end TauCeti
