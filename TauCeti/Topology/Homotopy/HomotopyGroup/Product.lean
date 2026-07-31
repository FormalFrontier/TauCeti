/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Product
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Homotopy groups of products

Generalized loops and homotopies relative to the cube boundary are computed coordinatewise.
Consequently, the homotopy group of a binary or indexed product is the corresponding product
of homotopy groups. This file supplies the generalized-loop constructions, their characteristic
API, and the resulting equivalences of homotopy groups. In positive dimensions the equivalences
are multiplicative.

The relative-homotopy product constructions are due to Praneeth Kolichala and come from
`Mathlib.Topology.Homotopy.Product`.

This is the product prerequisite for the torus calculation requested in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13: combining the indexed-product
equivalence with the vanishing of the higher homotopy groups of a circle computes the higher
homotopy groups of a torus.

## Main declarations

* `TauCeti.HomotopyGroup.prodEquiv`: the homotopy group of a binary product is the product
  of the homotopy groups.
* `TauCeti.HomotopyGroup.piEquiv`: the homotopy group of an indexed product is the indexed
  product of the homotopy groups.
* `TauCeti.HomotopyGroup.prodMulEquiv`, `TauCeti.HomotopyGroup.piMulEquiv`: the
  positive-dimensional multiplicative forms.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The coordinatewise product of two generalized loops. -/
def prod (p : Ω^ N X x) (q : Ω^ N Y y) : Ω^ N (X × Y) (x, y) :=
  ⟨ContinuousMap.prodMk p.1 q.1, fun t ht ↦
    Prod.ext (_root_.GenLoop.boundary p t ht) (_root_.GenLoop.boundary q t ht)⟩

@[simp]
theorem prod_apply (p : Ω^ N X x) (q : Ω^ N Y y) (t : I^N) :
    prod p q t = (p t, q t) :=
  (rfl)

/-- Taking the first coordinate of a product generalized loop recovers the first loop. -/
@[simp]
theorem map_fst_prod (p : Ω^ N X x) (q : Ω^ N Y y) :
    map (ContinuousMap.fst : C(X × Y, X)) rfl (prod p q) = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- Taking the second coordinate of a product generalized loop recovers the second loop. -/
@[simp]
theorem map_snd_prod (p : Ω^ N X x) (q : Ω^ N Y y) :
    map (ContinuousMap.snd : C(X × Y, Y)) rfl (prod p q) = q := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- A generalized loop in a product is recovered from its two coordinate loops. -/
@[simp]
theorem prod_map_fst_map_snd (p : Ω^ N (X × Y) (x, y)) :
    prod (map (ContinuousMap.fst : C(X × Y, X)) rfl p)
      (map (ContinuousMap.snd : C(X × Y, Y)) rfl p) = p := by
  apply _root_.GenLoop.ext
  intro t
  exact Prod.ext rfl rfl

/-- Coordinatewise products preserve homotopy relative to the cube boundary. -/
theorem prod_homotopic {p p' : Ω^ N X x} {q q' : Ω^ N Y y}
    (hp : _root_.GenLoop.Homotopic p p') (hq : _root_.GenLoop.Homotopic q q') :
    _root_.GenLoop.Homotopic (prod p q) (prod p' q') := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨ContinuousMap.HomotopyRel.prod hp hq⟩

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

/-- The coordinatewise indexed product of generalized loops. -/
def pi (p : ∀ i, Ω^ N (Z i) (z i)) : Ω^ N (∀ i, Z i) z :=
  ⟨ContinuousMap.pi fun i ↦ (p i).1, fun t ht ↦
    funext fun i ↦ _root_.GenLoop.boundary (p i) t ht⟩

@[simp]
theorem pi_apply (p : ∀ i, Ω^ N (Z i) (z i)) (t : I^N) (i : ι) :
    pi p t i = p i t :=
  (rfl)

/-- Taking a coordinate of an indexed product generalized loop recovers that coordinate loop. -/
@[simp]
theorem map_eval_pi (p : ∀ i, Ω^ N (Z i) (z i)) (i : ι) :
    map (ContinuousMap.eval i) rfl (pi p) = p i := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- A generalized loop in an indexed product is recovered from all of its coordinate loops. -/
@[simp]
theorem pi_map_eval (p : Ω^ N (∀ i, Z i) z) :
    pi (fun i ↦ map (ContinuousMap.eval i) rfl p) = p := by
  apply _root_.GenLoop.ext
  intro t
  rfl

/-- Indexed products preserve coordinatewise homotopy relative to the cube boundary. -/
theorem pi_homotopic {p q : ∀ i, Ω^ N (Z i) (z i)}
    (h : ∀ i, _root_.GenLoop.Homotopic (p i) (q i)) :
    _root_.GenLoop.Homotopic (pi p) (pi q) :=
  ⟨ContinuousMap.HomotopyRel.pi fun i ↦ Classical.choice (h i)⟩

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The product of two homotopy classes, represented by the coordinatewise product of
generalized loops. -/
def prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    HomotopyGroup N (X × Y) (x, y) :=
  Quotient.map₂ GenLoop.prod
    (fun {p p'} hp {q q'} hq ↦ GenLoop.prod_homotopic (p := p) (p' := p')
      (q := q) (q' := q') hp hq) a b

@[simp]
theorem prod_mk (p : Ω^ N X x) (q : Ω^ N Y y) :
    prod (⟦p⟧ : HomotopyGroup N X x) (⟦q⟧ : HomotopyGroup N Y y) =
      (⟦GenLoop.prod p q⟧ : HomotopyGroup N (X × Y) (x, y)) :=
  (rfl)

/-- The first-coordinate map sends a product of homotopy classes to its first factor. -/
@[simp]
theorem map_fst_prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (ContinuousMap.fst : C(X × Y, X)) rfl (prod a b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rw [prod_mk, map_mk, GenLoop.map_fst_prod]
  rfl

/-- The second-coordinate map sends a product of homotopy classes to its second factor. -/
@[simp]
theorem map_snd_prod (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (ContinuousMap.snd : C(X × Y, Y)) rfl (prod a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  rw [prod_mk, map_mk, GenLoop.map_snd_prod]
  rfl

/-- A homotopy class in a product is recovered from its two coordinate classes. -/
@[simp]
theorem prod_map_fst_map_snd (a : HomotopyGroup N (X × Y) (x, y)) :
    prod (map (ContinuousMap.fst : C(X × Y, X)) rfl a)
      (map (ContinuousMap.snd : C(X × Y, Y)) rfl a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_mk, map_mk, prod_mk, GenLoop.prod_map_fst_map_snd]
  rfl

/-- The homotopy group of a binary product is the product of the homotopy groups. -/
def prodEquiv (x : X) (y : Y) :
    HomotopyGroup N (X × Y) (x, y) ≃
      HomotopyGroup N X x × HomotopyGroup N Y y where
  toFun a :=
    (map (ContinuousMap.fst : C(X × Y, X)) rfl a,
      map (ContinuousMap.snd : C(X × Y, Y)) rfl a)
  invFun a := prod a.1 a.2
  left_inv := prod_map_fst_map_snd
  right_inv a := Prod.ext (map_fst_prod a.1 a.2) (map_snd_prod a.1 a.2)

@[simp]
theorem prodEquiv_apply (x : X) (y : Y) (a : HomotopyGroup N (X × Y) (x, y)) :
    prodEquiv x y a =
      (map (ContinuousMap.fst : C(X × Y, X)) rfl a,
        map (ContinuousMap.snd : C(X × Y, Y)) rfl a) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (x : X) (y : Y)
    (a : HomotopyGroup N X x × HomotopyGroup N Y y) :
    (prodEquiv x y).symm a = prod a.1 a.2 :=
  (rfl)

/-- In positive dimensions, the homotopy group of a binary product is multiplicatively
equivalent to the product of the homotopy groups. -/
def prodMulEquiv [DecidableEq N] [Nonempty N] (x : X) (y : Y) :
    HomotopyGroup N (X × Y) (x, y) ≃*
      HomotopyGroup N X x × HomotopyGroup N Y y :=
  { prodEquiv x y with
    map_mul' := fun a b ↦ Prod.ext
      (map_mul (ContinuousMap.fst : C(X × Y, X)) rfl a b)
      (map_mul (ContinuousMap.snd : C(X × Y, Y)) rfl a b) }

@[simp]
theorem prodMulEquiv_apply [DecidableEq N] [Nonempty N] (x : X) (y : Y)
    (a : HomotopyGroup N (X × Y) (x, y)) :
    prodMulEquiv x y a = prodEquiv x y a :=
  (rfl)

@[simp]
theorem prodMulEquiv_symm_apply [DecidableEq N] [Nonempty N] (x : X) (y : Y)
    (a : HomotopyGroup N X x × HomotopyGroup N Y y) :
    (prodMulEquiv x y).symm a = prod a.1 a.2 :=
  (rfl)

/-- The coordinatewise product of identity homotopy classes is the identity. -/
@[simp]
theorem prod_one [DecidableEq N] [Nonempty N] :
    prod (1 : HomotopyGroup N X x) (1 : HomotopyGroup N Y y) = 1 := by
  simpa only [prodMulEquiv_symm_apply, Prod.fst_one, Prod.snd_one] using
    (prodMulEquiv (N := N) x y).symm.map_one

/-- Coordinatewise products commute with multiplication of homotopy classes. -/
@[simp]
theorem prod_mul [DecidableEq N] [Nonempty N]
    (a₁ a₂ : HomotopyGroup N X x) (b₁ b₂ : HomotopyGroup N Y y) :
    prod (a₁ * a₂) (b₁ * b₂) = prod a₁ b₁ * prod a₂ b₂ := by
  simpa only [prodMulEquiv_symm_apply, Prod.fst_mul, Prod.snd_mul] using
    (prodMulEquiv (N := N) x y).symm.map_mul (a₁, b₁) (a₂, b₂)

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

/-- The indexed product of homotopy classes, represented by the coordinatewise product of
generalized loops. -/
noncomputable def pi (a : ∀ i, HomotopyGroup N (Z i) (z i)) :
    HomotopyGroup N (∀ i, Z i) z :=
  (Quotient.map GenLoop.pi fun {p q} h ↦
    GenLoop.pi_homotopic (p := p) (q := q) h) (Quotient.choice a)

@[simp]
theorem pi_mk (p : ∀ i, Ω^ N (Z i) (z i)) :
    pi (fun i ↦ (⟦p i⟧ : HomotopyGroup N (Z i) (z i))) =
      (⟦GenLoop.pi p⟧ : HomotopyGroup N (∀ i, Z i) z) := by
  unfold pi
  rw [Quotient.choice_eq, Quotient.map_mk]

/-- Taking a coordinate of an indexed product of homotopy classes recovers that coordinate. -/
@[simp]
theorem map_eval_pi (a : ∀ i, HomotopyGroup N (Z i) (z i)) (i : ι) :
    map (ContinuousMap.eval i) rfl (pi a) = a i := by
  induction a using Quotient.induction_on_pi
  simp only [pi_mk, map_mk, GenLoop.map_eval_pi]
  rfl

/-- A homotopy class in an indexed product is recovered from all of its coordinate classes. -/
@[simp]
theorem pi_map_eval (a : HomotopyGroup N (∀ i, Z i) z) :
    pi (fun i ↦ map (ContinuousMap.eval i) rfl a) = a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [map_mk, pi_mk, GenLoop.pi_map_eval]
  rfl

/-- The homotopy group of an indexed product is the indexed product of the homotopy groups. -/
noncomputable def piEquiv (z : ∀ i, Z i) :
    HomotopyGroup N (∀ i, Z i) z ≃ ∀ i, HomotopyGroup N (Z i) (z i) where
  toFun a i := map (ContinuousMap.eval i) rfl a
  invFun := pi
  left_inv := pi_map_eval
  right_inv a := funext fun i ↦ map_eval_pi a i

@[simp]
theorem piEquiv_apply (z : ∀ i, Z i) (a : HomotopyGroup N (∀ i, Z i) z) (i : ι) :
    piEquiv z a i = map (ContinuousMap.eval i) rfl a :=
  (rfl)

@[simp]
theorem piEquiv_symm_apply (z : ∀ i, Z i)
    (a : ∀ i, HomotopyGroup N (Z i) (z i)) :
    (piEquiv z).symm a = pi a :=
  (rfl)

/-- The homotopy group of an indexed product is a subsingleton when every factor homotopy
group is a subsingleton. -/
instance subsingleton_pi [∀ i, Subsingleton (HomotopyGroup N (Z i) (z i))] :
    Subsingleton (HomotopyGroup N (∀ i, Z i) z) :=
  (piEquiv z).subsingleton_congr.mpr inferInstance

/-- In positive dimensions, the homotopy group of an indexed product is multiplicatively
equivalent to the indexed product of the homotopy groups. -/
noncomputable def piMulEquiv [DecidableEq N] [Nonempty N] (z : ∀ i, Z i) :
    HomotopyGroup N (∀ i, Z i) z ≃* ∀ i, HomotopyGroup N (Z i) (z i) :=
  { piEquiv z with
    map_mul' := fun a b ↦ funext fun i ↦
      map_mul (ContinuousMap.eval i) rfl a b }

@[simp]
theorem piMulEquiv_apply [DecidableEq N] [Nonempty N] (z : ∀ i, Z i)
    (a : HomotopyGroup N (∀ i, Z i) z) (i : ι) :
    piMulEquiv z a i = map (ContinuousMap.eval i) rfl a :=
  (rfl)

@[simp]
theorem piMulEquiv_symm_apply [DecidableEq N] [Nonempty N] (z : ∀ i, Z i)
    (a : ∀ i, HomotopyGroup N (Z i) (z i)) :
    (piMulEquiv z).symm a = pi a :=
  (rfl)

/-- The coordinatewise indexed product of identity homotopy classes is the identity. -/
@[simp]
theorem pi_one [DecidableEq N] [Nonempty N] :
    pi (fun _ ↦ 1 : ∀ i, HomotopyGroup N (Z i) (z i)) = 1 := by
  rw [← piMulEquiv_symm_apply (N := N) z]
  exact (piMulEquiv (N := N) z).symm.map_one

/-- Coordinatewise indexed products commute with multiplication of homotopy classes. -/
@[simp]
theorem pi_mul [DecidableEq N] [Nonempty N]
    (a b : ∀ i, HomotopyGroup N (Z i) (z i)) :
    pi (a * b) = pi a * pi b := by
  simpa only [piMulEquiv_symm_apply] using
    (piMulEquiv (N := N) z).symm.map_mul a b

end HomotopyGroup

end TauCeti
