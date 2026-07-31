/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Functoriality of homotopy groups

Mathlib defines the generalized loop space `Ω^ N X x` and the quotient
`HomotopyGroup N X x`, but it does not yet provide the map induced by a based continuous
map. This file supplies that small API: postcomposition sends generalized loops based at
`x` to generalized loops based at `y`, descends to homotopy classes, respects identity and
composition, handles constant maps and subsingleton targets, and is a monoid homomorphism in
positive dimensions.

This is a prerequisite for the higher-homotopy API requested in the Tau Ceti universal-covers
roadmap, Stage 3 item 9, before proving that a covering map induces isomorphisms on
`π_n` for `n ≥ 2`.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- A based continuous map sends generalized loops to generalized loops by postcomposition. -/
@[expose] def map (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) : Ω^ N Y y :=
  ⟨f.comp p.1, fun t ht => by simpa [hf] using congrArg f (_root_.GenLoop.boundary p t ht)⟩

@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) (t : I^N) :
    map f hf p t = f (p t) :=
  rfl

@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (_root_.GenLoop.const : Ω^ N X x) =
      (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  simp [hf]

/-- Postcomposition by a constant continuous map gives the constant generalized loop.

This is not a `simp` lemma: baking the basepoint proof `rfl` into the statement forces the
target basepoint to be `(ContinuousMap.const X y) x` rather than `y`, so `simp` cannot close
even its own statement. Use it as an explicit rewrite. -/
theorem map_continuousMap_const (y : Y) (p : Ω^ N X x) :
    map (ContinuousMap.const X y) rfl p = (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  rw [map_apply]
  exact _root_.GenLoop.const_apply.symm

@[simp]
theorem map_id (p : Ω^ N X x) :
    map (ContinuousMap.id X) rfl p = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

@[simp]
theorem map_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (p : Ω^ N X x) :
    map g hg (map f hf p) = map (g.comp f) (by simp [hf, hg]) p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- Postcomposition preserves homotopy relative to the cube boundary. -/
theorem map_homotopic {f g : Ω^ N X x} (h : _root_.GenLoop.Homotopic f g)
    (F : C(X, Y)) (hF : F x = y) :
    _root_.GenLoop.Homotopic (map F hF f) (map F hF g) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h F

variable [DecidableEq N]

@[simp]
theorem map_transAt (F : C(X, Y)) (hF : F x = y) (i : N) (p q : Ω^ N X x) :
    map F hF (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt i (map F hF p) (map F hF q) := by
  apply _root_.GenLoop.ext
  intro t
  simp only [map_apply, _root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  split_ifs <;> rfl

@[simp]
theorem map_symmAt (F : C(X, Y)) (hF : F x = y) (i : N) (p : Ω^ N X x) :
    map F hF (_root_.GenLoop.symmAt i p) =
      _root_.GenLoop.symmAt i (map F hF p) := by
  apply _root_.GenLoop.ext
  intro t
  simp only [map_apply, _root_.GenLoop.symmAt, _root_.GenLoop.coe_copy]

end GenLoop

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- In positive dimensions, the class of the constant generalized loop is the identity element.
This is `HomotopyGroup.one_def` oriented towards `1`, so that `1` is the simp normal form for
the constant-map results below. -/
@[simp]
theorem mk_const_eq_one [DecidableEq N] [Nonempty N] :
    (⟦(_root_.GenLoop.const : Ω^ N X x)⟧ : HomotopyGroup N X x) = (1 : HomotopyGroup N X x) :=
  _root_.HomotopyGroup.one_def.symm

/-- The map on homotopy classes induced by a based continuous map. -/
@[expose] def map (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (GenLoop.map f hf) fun _ _ h => GenLoop.map_homotopic h f hf

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    map f hf (⟦p⟧ : HomotopyGroup N X x) = ⟦GenLoop.map f hf p⟧ :=
  rfl

/-- A constant continuous map sends every homotopy class to the class of the constant
generalized loop. This statement also covers dimension zero, where the target need not carry
the positive-dimensional group structure. -/
@[simp]
theorem map_continuousMap_const_apply (y : Y) (hy : (ContinuousMap.const X y) x = y)
    (a : HomotopyGroup N X x) :
    map (x := x) (ContinuousMap.const X y) hy a =
      (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_mk]
  exact congrArg _ (GenLoop.map_continuousMap_const y p)

/-- A based map into a subsingleton space induces the same map as the constant map at the
target basepoint. -/
theorem map_eq_continuousMap_const_of_subsingleton [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) :
    map (N := N) f hf = map (x := x) (ContinuousMap.const X y) rfl := by
  have h : f = ContinuousMap.const X y := Subsingleton.elim _ _
  subst f
  rfl

/-- A based map into a subsingleton space sends every homotopy class to the class of the
constant generalized loop. -/
@[simp]
theorem map_apply_of_subsingleton [Subsingleton Y] (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    map (N := N) f hf a =
      (⟦(_root_.GenLoop.const : Ω^ N Y y)⟧ : HomotopyGroup N Y y) := by
  rw [map_eq_continuousMap_const_of_subsingleton]
  exact map_continuousMap_const_apply y _ a

/-- In positive dimensions, a constant continuous map sends every homotopy class to the
identity.

This is not a `simp` lemma: the positive-dimensional normal form is already reached by
`map_continuousMap_const_apply` followed by `mk_const_eq_one`, so a separate `⟦const⟧`-keyed
`= 1` rule would be redundant. It is kept as an explicit rewrite. -/
theorem map_continuousMap_const_apply_eq_one [DecidableEq N] [Nonempty N]
    (y : Y) (hy : (ContinuousMap.const X y) x = y) (a : HomotopyGroup N X x) :
    map (x := x) (ContinuousMap.const X y) hy a = 1 :=
  (map_continuousMap_const_apply y hy a).trans _root_.HomotopyGroup.one_def.symm

/-- In positive dimensions, a based map into a subsingleton space sends every homotopy class
to the identity.

This is not a `simp` lemma: the positive-dimensional normal form is already reached by
`map_apply_of_subsingleton` followed by `mk_const_eq_one`, so a separate composite `= 1` rule
would be redundant. It is kept as an explicit rewrite. -/
theorem map_apply_eq_one_of_subsingleton [DecidableEq N] [Nonempty N] [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup N X x) :
    map (N := N) f hf a = 1 :=
  (map_apply_of_subsingleton f hf a).trans _root_.HomotopyGroup.one_def.symm

/-- Identity law: the map induced by the identity continuous map is the identity on homotopy
classes. -/
@[simp]
theorem map_id_apply (a : HomotopyGroup N X x) :
    map (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, GenLoop.map_id]
    rfl

/-- Composition law: the map induced by a composite continuous map is the composite of the
induced maps on homotopy classes. -/
@[simp]
theorem map_comp_apply (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by simp [hf, hg]) a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp
  -- both sides are now `⟦GenLoop.map (g.comp f) _ p⟧` and differ only in the basepoint proof
  -- carried by `GenLoop.map`, which is proof-irrelevant.
  rfl

/-- The induced map `HomotopyGroup.map` depends only on the underlying continuous map, not on the
chosen proof of the basepoint equation. -/
theorem map_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (a : HomotopyGroup N X x) :
    map f₁ h₁ a = map f₂ h₂ a := by
  subst hfe
  rfl

/-- If `g ∘ f` is the identity, then the induced map of `g` undoes the induced map of `f` on
homotopy classes. -/
theorem map_map_of_comp_eq_id (g : C(Y, X)) (f : C(X, Y)) (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = a := by
  rw [map_comp_apply]
  exact (map_congr hgf _ rfl a).trans (map_id_apply a)

/-- In positive dimensions, the map induced by a based continuous map is a monoid
homomorphism for the standard group structure on homotopy groups. -/
@[expose] def mapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    rw [_root_.HomotopyGroup.one_def, map_mk, GenLoop.map_const]
    exact _root_.HomotopyGroup.one_def.symm
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    -- as in `map_comp_apply`, the two sides differ only in the proof-irrelevant basepoint
    -- argument of `GenLoop.map`.
    rfl

@[simp]
theorem mapHom_apply [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    mapHom f hf a = map f hf a :=
  rfl

/-- In positive dimensions, a constant continuous map induces the trivial homomorphism on
homotopy groups.

This is not a `simp` lemma: baking the basepoint proof `rfl` into the statement forces the
target basepoint to be `(ContinuousMap.const X y) x` rather than `y`, so `simp` cannot close
even its own statement. Use it as an explicit rewrite. -/
theorem mapHom_continuousMap_const_eq_one [DecidableEq N] [Nonempty N] (y : Y) :
    mapHom (N := N) (x := x) (ContinuousMap.const X y) rfl = 1 := by
  ext a
  exact map_continuousMap_const_apply_eq_one (x := x) y rfl a

/-- A based map into a subsingleton space induces the trivial homomorphism on every
positive-dimensional homotopy group. -/
@[simp]
theorem mapHom_eq_one_of_subsingleton [DecidableEq N] [Nonempty N] [Subsingleton Y]
    (f : C(X, Y)) (hf : f x = y) : mapHom (N := N) f hf = 1 := by
  ext a
  exact map_apply_eq_one_of_subsingleton f hf a

/-- Identity law for the bundled homomorphism: the induced monoid homomorphism of the identity
continuous map is the identity homomorphism. -/
@[simp]
theorem mapHom_id [DecidableEq N] [Nonempty N] :
    mapHom (ContinuousMap.id X) rfl = MonoidHom.id (HomotopyGroup N X x) :=
  MonoidHom.ext fun a => map_id_apply a

/-- Composition law for the bundled homomorphism: the induced monoid homomorphism of a composite
continuous map is the composite of the induced homomorphisms. -/
@[simp]
theorem mapHom_comp [DecidableEq N] [Nonempty N] (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    (mapHom g hg).comp (mapHom f hf) = mapHom (N := N) (g.comp f) (by simp [hf, hg]) :=
  MonoidHom.ext fun a => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, mapHom_apply, map_comp_apply]

@[simp]
theorem map_mul [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y)
    (a b : HomotopyGroup N X x) :
    map f hf (a * b) = map f hf a * map f hf b :=
  (mapHom f hf).map_mul a b

@[simp]
theorem map_one [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    map f hf (1 : HomotopyGroup N X x) = 1 :=
  (mapHom f hf).map_one

end HomotopyGroup

end TauCeti
