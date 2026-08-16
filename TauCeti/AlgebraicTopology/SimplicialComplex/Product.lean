/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Preorder.Chain
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Ordered products of abstract simplicial complexes

The ordered product of two simplicial complexes is the standard staircase triangulation of their
product. Its vertices are pairs of vertices. A finite set of pairs is a face when both coordinate
projections are faces and the pairs form a chain for the coordinatewise order. The chain condition
is essential: without it, the four vertices of a square would span a tetrahedron rather than two
triangles.

This file constructs the product first for `PreAbstractSimplicialComplex`, then for
`AbstractSimplicialComplex`. It also supplies the simplicial coordinate projections,
fixed-coordinate inclusions, and the ordered cylinder obtained by taking the second factor to be
the standard one-simplex on `Fin 2`.

The construction is the simplicial product used in the collapse track of layer 11 of the
geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`). In particular, the
ordered cylinder is the missing product `K × I` in the statement of Zeeman's conjecture. The
definition follows the ordered (staircase) triangulation convention in Rourke--Sanderson,
*Introduction to Piecewise-Linear Topology*, Chapter 2. No claim about the realization of this
product is made here; identifying its realization with the product of realizations is later work.

## Main definitions

* `PreAbstractSimplicialComplex.orderedProd`: the ordered product of two precomplexes.
* `AbstractSimplicialComplex.orderedProd`: the ordered product of two complexes.
* `AbstractSimplicialComplex.orderedCylinder`: product with the standard one-simplex.
* `PreAbstractSimplicialComplex.SimplicialMap.orderedProdFst` and
  `orderedProdSnd`: the coordinate projections.
* `PreAbstractSimplicialComplex.SimplicialMap.prodMkLeft` and `prodMkRight`:
  fixed-coordinate inclusions into an ordered product.
-/

public section

namespace PreAbstractSimplicialComplex

variable {α β γ δ : Type*}

section OrderedProd

variable [LinearOrder α] [LinearOrder β]

/-- The ordered product of two pre-abstract simplicial complexes.

A finite set of pairs is a face exactly when its two coordinate images are faces of the factors
and it is a chain for the coordinatewise order on the product. The linear orders are data in the
construction: changing them can change the triangulation, though not its intended PL type. -/
public def orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : PreAbstractSimplicialComplex (α × β) where
  faces := {σ | σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
    IsChain (· ≤ ·) (σ : Set (α × β))}
  isRelLowerSet_faces := by
    rintro σ ⟨hK, hL, hchain⟩
    refine ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces hK).1, fun τ hτσ hτ => ?_⟩
    refine ⟨?_, ?_, hchain.mono (Finset.coe_subset.mpr hτσ)⟩
    · exact (K.isRelLowerSet_faces hK).2 (Finset.image_subset_image hτσ)
        (Finset.image_nonempty.mpr hτ)
    · exact (L.isRelLowerSet_faces hL).2 (Finset.image_subset_image hτσ)
        (Finset.image_nonempty.mpr hτ)

variable {K K' : PreAbstractSimplicialComplex α}
  {L L' : PreAbstractSimplicialComplex β}

/-- Membership in an ordered product is characterized by the two projected face conditions and
the staircase chain condition. -/
@[simp]
theorem mem_orderedProd_iff {σ : Finset (α × β)} :
    σ ∈ orderedProd K L ↔ σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
      IsChain (· ≤ ·) (σ : Set (α × β)) :=
  Iff.rfl

/-- The first-coordinate image of a face of an ordered product is a face of the first factor. -/
theorem image_fst_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.fst ∈ K :=
  (mem_orderedProd_iff.mp hσ).1

/-- The second-coordinate image of a face of an ordered product is a face of the second factor. -/
theorem image_snd_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.snd ∈ L :=
  (mem_orderedProd_iff.mp hσ).2.1

/-- Every face of an ordered product is a chain for the coordinatewise order. -/
theorem isChain_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : IsChain (· ≤ ·) (σ : Set (α × β)) :=
  (mem_orderedProd_iff.mp hσ).2.2

/-- Ordered product is monotone in both factors. -/
theorem orderedProd_mono (hK : K ≤ K') (hL : L ≤ L') :
    orderedProd K L ≤ orderedProd K' L' := by
  rintro σ ⟨hσK, hσL, hchain⟩
  exact ⟨hK hσK, hL hσL, hchain⟩

end OrderedProd

namespace SimplicialMap

section Projections

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- The first coordinate projection from an ordered product is simplicial. -/
public def orderedProdFst (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : SimplicialMap (orderedProd K L) K where
  toFun := Prod.fst
  map_face' := fun _ hσ ↦ image_fst_mem_of_mem_orderedProd (K := K) (L := L) hσ

@[simp]
theorem coe_orderedProdFst (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : ⇑(orderedProdFst K L) = Prod.fst := by
  simp only [orderedProdFst, coe_mk]

@[simp]
theorem orderedProdFst_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (p : α × β) : orderedProdFst K L p = p.1 :=
  congrFun (coe_orderedProdFst K L) p

/-- The second coordinate projection from an ordered product is simplicial. -/
public def orderedProdSnd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : SimplicialMap (orderedProd K L) L where
  toFun := Prod.snd
  map_face' := fun _ hσ ↦ image_snd_mem_of_mem_orderedProd (K := K) (L := L) hσ

@[simp]
theorem coe_orderedProdSnd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) : ⇑(orderedProdSnd K L) = Prod.snd := by
  simp only [orderedProdSnd, coe_mk]

@[simp]
theorem orderedProdSnd_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (p : α × β) : orderedProdSnd K L p = p.2 :=
  congrFun (coe_orderedProdSnd K L) p

end Projections

section ProdMkLeft

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Fixing a vertex `b` of the second factor gives the simplicial inclusion `a ↦ (a, b)` of the
first factor into the ordered product. -/
public def prodMkLeft (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β)
    (b : β) (hb : ({b} : Finset β) ∈ L) : SimplicialMap K (orderedProd K L) where
  toFun := fun a => (a, b)
  map_face' := by
    intro σ hσ
    have hσne := (K.isRelLowerSet_faces hσ).1
    rw [mem_orderedProd_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def] using hσ
    · simpa [Finset.image_image, Function.comp_def, Finset.image_const hσne b] using hb
    · rw [Finset.coe_image]
      have hmono : Monotone (fun a : α => (a, b)) := fun _ _ h ↦ ⟨h, le_rfl⟩
      exact hmono.isChain_image (isChain_of_trichotomous (σ : Set α))

@[simp]
theorem coe_prodMkLeft (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) :
    ⇑(prodMkLeft K L b hb) = fun a ↦ (a, b) := by
  simp only [prodMkLeft, coe_mk]

@[simp]
theorem prodMkLeft_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) (a : α) :
    prodMkLeft K L b hb a = (a, b) :=
  congrFun (coe_prodMkLeft K L b hb) a

/-- The fixed-second-coordinate copy of the first factor is a subcomplex of the ordered product. -/
theorem map_prodMkLeft_le_orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (b : β) (hb : ({b} : Finset β) ∈ L) :
    K.map (fun a => (a, b)) ≤ orderedProd K L :=
  (prodMkLeft K L b hb).map_le

end ProdMkLeft

section ProdMkRight

variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Fixing a vertex `a` of the first factor gives the simplicial inclusion `b ↦ (a, b)` of the
second factor into the ordered product. -/
public def prodMkRight (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β)
    (a : α) (ha : ({a} : Finset α) ∈ K) : SimplicialMap L (orderedProd K L) where
  toFun := fun b => (a, b)
  map_face' := by
    intro σ hσ
    have hσne := (L.isRelLowerSet_faces hσ).1
    rw [mem_orderedProd_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def, Finset.image_const hσne a] using ha
    · simpa [Finset.image_image, Function.comp_def] using hσ
    · rw [Finset.coe_image]
      have hmono : Monotone (fun b : β => (a, b)) := fun _ _ h ↦ ⟨le_rfl, h⟩
      exact hmono.isChain_image (isChain_of_trichotomous (σ : Set β))

@[simp]
theorem coe_prodMkRight (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) :
    ⇑(prodMkRight K L a ha) = fun b ↦ (a, b) := by
  simp only [prodMkRight, coe_mk]

@[simp]
theorem prodMkRight_apply (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) (b : β) :
    prodMkRight K L a ha b = (a, b) :=
  congrFun (coe_prodMkRight K L a ha) b

/-- The fixed-first-coordinate copy of the second factor is a subcomplex of the ordered product. -/
theorem map_prodMkRight_le_orderedProd (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) (a : α) (ha : ({a} : Finset α) ∈ K) :
    L.map (fun b => (a, b)) ≤ orderedProd K L :=
  (prodMkRight K L a ha).map_le

end ProdMkRight

section OrderedProdMap

variable [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Monotone simplicial maps induce a simplicial map between ordered products. Monotonicity is
needed because the product triangulation depends on the chosen vertex orders. -/
public def orderedProdMap {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) :
    SimplicialMap (orderedProd K L) (orderedProd Kγ Lδ) where
  toFun := fun p => (f p.1, g p.2)
  map_face' := by
    intro σ hσ
    rw [mem_orderedProd_iff] at hσ ⊢
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finset.image_image, Function.comp_def] using f.map_face hσ.1
    · simpa [Finset.image_image, Function.comp_def] using g.map_face hσ.2.1
    · rw [Finset.coe_image]
      have hmono : Monotone (fun p : α × β => (f p.1, g p.2)) :=
        fun _ _ h ↦ ⟨hf h.1, hg h.2⟩
      exact hmono.isChain_image hσ.2.2

@[simp]
theorem coe_orderedProdMap {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) :
    ⇑(orderedProdMap f g hf hg) = fun p ↦ (f p.1, g p.2) := by
  simp only [orderedProdMap, coe_mk]

@[simp]
theorem orderedProdMap_apply {Kγ : PreAbstractSimplicialComplex γ}
    {Lδ : PreAbstractSimplicialComplex δ} (f : SimplicialMap K Kγ)
    (g : SimplicialMap L Lδ) (hf : Monotone f) (hg : Monotone g) (p : α × β) :
    orderedProdMap f g hf hg p = (f p.1, g p.2) :=
  congrFun (coe_orderedProdMap f g hf hg) p

end OrderedProdMap

end SimplicialMap

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {α β : Type*}

section OrderedProd

variable [LinearOrder α] [LinearOrder β]

/-- The ordered product of two abstract simplicial complexes. -/
public def orderedProd (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β) :
    AbstractSimplicialComplex (α × β) :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex (α × β)
    (PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) fun p => by
        exact PreAbstractSimplicialComplex.mem_orderedProd_iff.mpr
          ⟨by rw [Finset.image_singleton]; exact K.singleton_mem p.1,
            by rw [Finset.image_singleton]; exact L.singleton_mem p.2, by simp⟩

variable {K K' : AbstractSimplicialComplex α} {L L' : AbstractSimplicialComplex β}

/-- Forgetting that the ordered product contains every singleton recovers the product of the
underlying precomplexes. -/
@[simp]
theorem orderedProd_toPreAbstractSimplicialComplex :
    (orderedProd K L).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex := by
  ext σ
  rfl

/-- Membership in an abstract ordered product has the same projected-face and chain
characterization as for precomplexes. -/
@[simp]
theorem mem_orderedProd_iff {σ : Finset (α × β)} :
    σ ∈ orderedProd K L ↔ σ.image Prod.fst ∈ K ∧ σ.image Prod.snd ∈ L ∧
      IsChain (· ≤ ·) (σ : Set (α × β)) := by
  simp only [← mem_toPreAbstractSimplicialComplex,
    orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_orderedProd_iff

/-- The first-coordinate image of a face of an abstract ordered product is a face of the first
factor. -/
theorem image_fst_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.fst ∈ K :=
  (mem_orderedProd_iff.mp hσ).1

/-- The second-coordinate image of a face of an abstract ordered product is a face of the second
factor. -/
theorem image_snd_mem_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : σ.image Prod.snd ∈ L :=
  (mem_orderedProd_iff.mp hσ).2.1

/-- Every face of an abstract ordered product is a chain for the coordinatewise order. -/
theorem isChain_of_mem_orderedProd {σ : Finset (α × β)}
    (hσ : σ ∈ orderedProd K L) : IsChain (· ≤ ·) (σ : Set (α × β)) :=
  (mem_orderedProd_iff.mp hσ).2.2

/-- Ordered product is monotone in both abstract simplicial complexes. -/
theorem orderedProd_mono (hK : K ≤ K') (hL : L ≤ L') :
    orderedProd K L ≤ orderedProd K' L' := by
  rw [← _root_.AbstractSimplicialComplex.toPreAbstractSimplicialComplex_le_iff]
  rw [orderedProd_toPreAbstractSimplicialComplex, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.orderedProd_mono hK hL

/-- The ordered simplicial cylinder on `K`, obtained by taking its ordered product with the
standard one-simplex on `Fin 2`. -/
def orderedCylinder (K : AbstractSimplicialComplex α) :
    AbstractSimplicialComplex (α × Fin 2) :=
  orderedProd K (⊤ : AbstractSimplicialComplex (Fin 2))

/-- The underlying precomplex of an ordered cylinder is the ordered product with the top
precomplex on `Fin 2`. -/
@[simp]
theorem orderedCylinder_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex α) :
    (orderedCylinder K).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.orderedProd K.toPreAbstractSimplicialComplex ⊤ := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex,
    _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]

/-- A face of the ordered cylinder is a face in the first coordinate and a chain in the product
order. The second projection condition is automatic because the interval factor is top. -/
@[simp]
theorem mem_orderedCylinder_iff {σ : Finset (α × Fin 2)} :
    σ ∈ orderedCylinder K ↔ σ.image Prod.fst ∈ K ∧
      IsChain (· ≤ ·) (σ : Set (α × Fin 2)) := by
  rw [orderedCylinder, mem_orderedProd_iff]
  constructor
  · rintro ⟨hK, _, hchain⟩
    exact ⟨hK, hchain⟩
  · rintro ⟨hK, hchain⟩
    refine ⟨hK, ?_, hchain⟩
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.image_nonempty.mpr (Finset.image_nonempty.mp (K.isRelLowerSet_faces hK).1)

/-- The first-coordinate image of a face of an ordered cylinder is a face of the original
complex. -/
theorem image_fst_mem_of_mem_orderedCylinder {σ : Finset (α × Fin 2)}
    (hσ : σ ∈ orderedCylinder K) : σ.image Prod.fst ∈ K :=
  (mem_orderedCylinder_iff.mp hσ).1

/-- Every face of an ordered cylinder is a chain for the product order. -/
theorem isChain_of_mem_orderedCylinder {σ : Finset (α × Fin 2)}
    (hσ : σ ∈ orderedCylinder K) : IsChain (· ≤ ·) (σ : Set (α × Fin 2)) :=
  (mem_orderedCylinder_iff.mp hσ).2

end OrderedProd

section EndpointInclusions

variable [LinearOrder α]
variable {K : AbstractSimplicialComplex α}

/-- The zero-end copy of a complex is a simplicial subcomplex of its ordered cylinder. -/
theorem map_prodMk_zero_le_orderedCylinder (K : AbstractSimplicialComplex α) :
    K.toPreAbstractSimplicialComplex.map (fun a => (a, (0 : Fin 2))) ≤
      (orderedCylinder K).toPreAbstractSimplicialComplex := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.SimplicialMap.map_prodMkLeft_le_orderedProd
    K.toPreAbstractSimplicialComplex
    (⊤ : AbstractSimplicialComplex (Fin 2)).toPreAbstractSimplicialComplex 0
    ((⊤ : AbstractSimplicialComplex (Fin 2)).singleton_mem 0)

/-- The one-end copy of a complex is a simplicial subcomplex of its ordered cylinder. -/
theorem map_prodMk_one_le_orderedCylinder (K : AbstractSimplicialComplex α) :
    K.toPreAbstractSimplicialComplex.map (fun a => (a, (1 : Fin 2))) ≤
      (orderedCylinder K).toPreAbstractSimplicialComplex := by
  rw [orderedCylinder, orderedProd_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.SimplicialMap.map_prodMkLeft_le_orderedProd
    K.toPreAbstractSimplicialComplex
    (⊤ : AbstractSimplicialComplex (Fin 2)).toPreAbstractSimplicialComplex 1
    ((⊤ : AbstractSimplicialComplex (Fin 2)).singleton_mem 1)

/-- The bundled simplicial inclusion of the zero endpoint into an ordered cylinder. -/
def orderedCylinderZero (K : AbstractSimplicialComplex α) :
    PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      (orderedCylinder K).toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.SimplicialMap.ofMapLE (fun a => (a, (0 : Fin 2)))
    (map_prodMk_zero_le_orderedCylinder K)

@[simp]
theorem coe_orderedCylinderZero (K : AbstractSimplicialComplex α) :
    ⇑(orderedCylinderZero K) = fun a => (a, (0 : Fin 2)) := by
  simp only [orderedCylinderZero,
    PreAbstractSimplicialComplex.SimplicialMap.coe_ofMapLE]

@[simp]
theorem orderedCylinderZero_apply (K : AbstractSimplicialComplex α) (a : α) :
    orderedCylinderZero K a = (a, (0 : Fin 2)) :=
  congrFun (coe_orderedCylinderZero K) a

/-- The bundled simplicial inclusion of the one endpoint into an ordered cylinder. -/
def orderedCylinderOne (K : AbstractSimplicialComplex α) :
    PreAbstractSimplicialComplex.SimplicialMap K.toPreAbstractSimplicialComplex
      (orderedCylinder K).toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.SimplicialMap.ofMapLE (fun a => (a, (1 : Fin 2)))
    (map_prodMk_one_le_orderedCylinder K)

@[simp]
theorem coe_orderedCylinderOne (K : AbstractSimplicialComplex α) :
    ⇑(orderedCylinderOne K) = fun a => (a, (1 : Fin 2)) := by
  simp only [orderedCylinderOne,
    PreAbstractSimplicialComplex.SimplicialMap.coe_ofMapLE]

@[simp]
theorem orderedCylinderOne_apply (K : AbstractSimplicialComplex α) (a : α) :
    orderedCylinderOne K a = (a, (1 : Fin 2)) :=
  congrFun (coe_orderedCylinderOne K) a

end EndpointInclusions

/-! The following three computations pin down the staircase convention on the square. The two
monotone triangles are faces, while the pair of incomparable off-diagonal vertices is not. -/

/-- The `fst ≤ snd` triangle is a face of the ordered square. -/
theorem fstLeSndTriangle_mem_orderedProd_finTwo :
    ({((0 : Fin 2), (0 : Fin 2)), (0, 1), (1, 1)} : Finset (Fin 2 × Fin 2)) ∈
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  have htop : ({(0 : Fin 2), 1} : Finset (Fin 2)) ∈
      (⊤ : AbstractSimplicialComplex (Fin 2)) := by
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.insert_nonempty 0 {1}
  refine ⟨by simpa using htop, by simpa using htop, ?_⟩
  simp [IsChain, Set.pairwise_insert]

/-- The `snd ≤ fst` triangle is a face of the ordered square. -/
theorem sndLeFstTriangle_mem_orderedProd_finTwo :
    ({((0 : Fin 2), (0 : Fin 2)), (1, 0), (1, 1)} : Finset (Fin 2 × Fin 2)) ∈
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  have htop : ({(0 : Fin 2), 1} : Finset (Fin 2)) ∈
      (⊤ : AbstractSimplicialComplex (Fin 2)) := by
    rw [← mem_toPreAbstractSimplicialComplex,
      _root_.AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
    exact Finset.insert_nonempty 0 {1}
  refine ⟨by simpa using htop, by simpa using htop, ?_⟩
  simp [IsChain, Set.pairwise_insert]

/-- The incomparable off-diagonal vertices do not form a face of the ordered square. -/
theorem offDiagonalPair_notMem_orderedProd_finTwo :
    ({((0 : Fin 2), (1 : Fin 2)), (1, 0)} : Finset (Fin 2 × Fin 2)) ∉
      orderedProd (⊤ : AbstractSimplicialComplex (Fin 2)) ⊤ := by
  rw [mem_orderedProd_iff]
  rintro ⟨_, _, hchain⟩
  simp [IsChain, Set.pairwise_insert] at hchain

end AbstractSimplicialComplex

