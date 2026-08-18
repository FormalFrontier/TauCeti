/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic

public section

/-!
# The simply connected root datum of type `Dₙ`

This file constructs, uniformly in the rank `n ≥ 4`, the pinned integral root datum of type `Dₙ` on
the character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.D n` and the
`i`-th simple coroot is the `i`-th standard basis vector.

## The coordinates

Simple roots and coordinates alike are indexed from zero throughout: the simple root `αᵢ` is
Bourbaki node `i + 1`, and `e_j` is the zero-based coordinate `j`, so what is called `α_{n-1}` here
is Bourbaki's fork root `α_n`.

The classical model is `ℤ ^ n` with the dot product: the `2 * n * (n - 1)` roots are the vectors
`±e_a ± e_b` with `a ≠ b`, which are exactly the integral vectors of squared length two, and the
Bourbaki simple roots are `αᵢ = eᵢ - eᵢ₊₁` for `i + 1 < n` together with the fork root
`α_{n-1} = e_{n-2} + e_{n-1}`. That model, its enumeration by `Fin (2 * n * (n - 1))` with the
simple roots first, the expansion of every root in the simple roots, their linear independence and
reflection in a root are all supplied by `TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD` and are
consumed here rather than rebuilt.

Type `Dₙ` is simply laced, so `α^∨ = α` under the dot product and both pinned lattices are images
of the one classical model:

```text
typeDWeight x = (x ⬝ᵥ αⱼ)ⱼ,      typeDSimpleRootCoordinates x = the coefficients of x in the αᵢ.
```

The first records a vector by its pairings against the simple coroots, the second by its
coordinates in the simple coroots. Because the second family reconstructs the classical vector,
the pinned pairing is the classical dot product, `typeDWeight_dotProduct_coordinates`, and every
axiom of the datum reduces to a statement about `⬝ᵥ` on `ℤ ^ n`.

The roots are indexed by `Fin (2 * n * (n - 1))` through `TauCeti.DynkinType.typeDRootEquiv`, whose
first `n` values are the simple roots in Bourbaki order. That index type is the one Layer 6 pins
for the type, since `(DynkinType.D n).numRoots` is `2 * n * (n - 1)` by definition.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeDSimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index four (Bourbaki, Plate IV), so the datum is a `RootDatum`
carrying no `RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means
here.

## Main definitions

* `TauCeti.DynkinType.typeDSimplyConnectedRootDatum`: the pinned root datum of type `Dₙ`.
* `TauCeti.DynkinType.typeDSimplyConnectedBase`: the base formed by the first `n` root indices.

## Main results

* `TauCeti.DynkinType.root_typeDSimpleIndex` and `TauCeti.DynkinType.coroot_typeDSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.D n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.toLinearMap_typeDSimplyConnectedRootDatum` and
  `TauCeti.DynkinType.toLinearMap_typeDSimplyConnectedRootDatum_single_single`: the pinned pairing
  is the classical dot product, and the standard basis of the character lattice is the family of
  fundamental weights.
* `TauCeti.DynkinType.hasCartanType_typeDSimplyConnectedRootDatum`: the pinned base has Cartan type
  `D n`.
* `TauCeti.DynkinType.corootSpan_typeDSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate IV, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. The layout of the file follows its sibling
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A` (#2594), whose type-agnostic
scaffolding — the perfect pairing, the pinned support, the Cartan-type criterion and the coroot
span — now lives in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic` and is shared
with this file. This is the `Dₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The Gram matrix of the Bourbaki simple roots -/

private lemma typeDSimpleRoot_apply_of_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) (k : Fin n) :
    typeDSimpleRoot n hn i k =
      (if (k : ℕ) = (i : ℕ) then 1 else 0) - (if (k : ℕ) = (i : ℕ) + 1 then 1 else 0) := by
  rw [typeDSimpleRoot_of_add_one_lt hn hi]
  simp [Pi.single_apply, Fin.ext_iff]

private lemma typeDSimpleRoot_apply_of_not_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) (k : Fin n) :
    typeDSimpleRoot n hn i k =
      (if (k : ℕ) = n - 2 then 1 else 0) + (if (k : ℕ) = n - 1 then 1 else 0) := by
  rw [typeDSimpleRoot_of_not_add_one_lt hn hi]
  simp [Pi.single_apply, Fin.ext_iff]

/-- The Bourbaki `Dₙ` diagram read off `CartanMatrix.D`: two distinct nodes are joined when they
are consecutive among the first `n - 1` nodes, or are the branch node `n - 3` and the last node
`n - 1`. Separating this from the six-way definition keeps the Gram-matrix case analysis below
small. -/
private lemma cartanMatrixD_apply (i j : Fin n) :
    CartanMatrix.D n i j =
      (if (i : ℕ) = (j : ℕ) then 2 else 0) -
        (if ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 ≤ n) ∨
              ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 ≤ n) ∨
              ((i : ℕ) + 3 = n ∧ (j : ℕ) + 1 = n) ∨ ((j : ℕ) + 3 = n ∧ (i : ℕ) + 1 = n) then 1
          else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- A chain simple root pairs with the others by the corresponding row of the Cartan matrix. -/
private lemma typeDSimpleRoot_dotProduct_of_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) (j : Fin n) :
    typeDSimpleRoot n hn i ⬝ᵥ typeDSimpleRoot n hn j = CartanMatrix.D n i j := by
  have hi' := i.isLt
  have hj' := j.isLt
  rw [typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct, single_dotProduct, single_dotProduct,
    cartanMatrixD_apply]
  by_cases hj : (j : ℕ) + 1 < n
  · simp only [typeDSimpleRoot_apply_of_add_one_lt hn hj, one_mul]
    split_ifs <;> omega
  · simp only [typeDSimpleRoot_apply_of_not_add_one_lt hn hj, one_mul]
    split_ifs <;> omega

/-- The fork simple root pairs with the others by the last row of the Cartan matrix. -/
private lemma typeDSimpleRoot_dotProduct_of_not_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) (j : Fin n) :
    typeDSimpleRoot n hn i ⬝ᵥ typeDSimpleRoot n hn j = CartanMatrix.D n i j := by
  have hi' := i.isLt
  have hj' := j.isLt
  rw [typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct, single_dotProduct,
    single_dotProduct, cartanMatrixD_apply]
  by_cases hj : (j : ℕ) + 1 < n
  · simp only [typeDSimpleRoot_apply_of_add_one_lt hn hj, one_mul]
    split_ifs <;> omega
  · simp only [typeDSimpleRoot_apply_of_not_add_one_lt hn hj, one_mul]
    split_ifs <;> omega

/-- **The simple roots of type `Dₙ` have the Cartan matrix as Gram matrix.** Type `Dₙ` is simply
laced and its roots have squared length two, so the coroot of a root is the root itself and the
Cartan integer `⟨αᵢ, αⱼ^∨⟩` is the classical dot product. -/
private lemma typeDSimpleRoot_dotProduct (hn : 4 ≤ n) (i j : Fin n) :
    typeDSimpleRoot n hn i ⬝ᵥ typeDSimpleRoot n hn j = CartanMatrix.D n i j := by
  by_cases hi : (i : ℕ) + 1 < n
  · exact typeDSimpleRoot_dotProduct_of_add_one_lt hn hi j
  · exact typeDSimpleRoot_dotProduct_of_not_add_one_lt hn hi j

/-- A combination of the simple roots orthogonal to every simple root is orthogonal to itself,
hence zero. This is the nondegeneracy behind both injectivity of the roots and linear independence
of the simple ones. -/
private lemma sum_smul_typeDSimpleRoot_eq_zero (hn : 4 ≤ n) {c : Fin n → ℤ}
    (h : ∀ j, (∑ i : Fin n, c i • typeDSimpleRoot n hn i) ⬝ᵥ typeDSimpleRoot n hn j = 0) :
    ∑ i : Fin n, c i • typeDSimpleRoot n hn i = 0 := by
  refine dotProduct_self_eq_zero.mp ?_
  rw [dotProduct_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [dotProduct_smul, h i, smul_zero]

/-! ## The two pinned coordinate families -/

/-- The character-lattice coordinates of a classical vector of type `Dₙ`: its pairings against the
Bourbaki-numbered simple coroots, which for a simply laced type are the simple roots. Reading the
simple roots as the rows of a matrix exhibits this as a linear map. -/
private def typeDWeight (n : ℕ) (hn : 4 ≤ n) : (Fin n → ℤ) →ₗ[ℤ] Fin n → ℤ :=
  (Matrix.of (typeDSimpleRoot n hn)).mulVecLin

private lemma typeDWeight_apply (hn : 4 ≤ n) (x : Fin n → ℤ) (j : Fin n) :
    typeDWeight n hn x j = x ⬝ᵥ typeDSimpleRoot n hn j := by
  rw [typeDWeight, Matrix.mulVecLin_apply]
  exact dotProduct_comm _ _

/-- **The pinned pairing is the classical dot product.** Pairing the weight coordinates of a vector
against the coefficients of a root evaluates the vector on that root, because the coefficients
reconstruct the root. -/
private lemma typeDWeight_dotProduct_coordinates (hn : 4 ≤ n) (x : Fin n → ℤ) (y : TypeDRoot n) :
    typeDWeight n hn x ⬝ᵥ typeDSimpleRootCoordinates n hn y = x ⬝ᵥ y.1 := by
  have hleft : typeDWeight n hn x ⬝ᵥ typeDSimpleRootCoordinates n hn y =
      ∑ j : Fin n, typeDSimpleRootCoordinates n hn y j • (x ⬝ᵥ typeDSimpleRoot n hn j) := by
    simp only [dotProduct, typeDWeight_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hleft]
  conv_rhs => rw [← sum_smul_typeDSimpleRootCoordinates hn y]
  rw [dotProduct_sum]
  exact Finset.sum_congr rfl fun j _ => (dotProduct_smul _ _ _).symm

private lemma typeDWeight_injective (hn : 4 ≤ n) :
    Injective fun x : TypeDRoot n => typeDWeight n hn x.1 := by
  intro x y hxy
  have hxy' : typeDWeight n hn x.1 = typeDWeight n hn y.1 := hxy
  -- The difference of two roots is the combination of the simple roots with the difference of
  -- their coordinates, and the hypothesis makes it orthogonal to every simple root.
  have hexp : x.1 - y.1 = ∑ i : Fin n,
      (typeDSimpleRootCoordinates n hn x - typeDSimpleRootCoordinates n hn y) i •
        typeDSimpleRoot n hn i := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib,
      sum_smul_typeDSimpleRootCoordinates]
  refine Subtype.ext (sub_eq_zero.mp ?_)
  rw [hexp]
  refine sum_smul_typeDSimpleRoot_eq_zero hn fun j => ?_
  rw [← hexp, ← typeDWeight_apply hn, map_sub, hxy', sub_self, Pi.zero_apply]

private lemma typeDSimpleRootCoordinates_injective (hn : 4 ≤ n) :
    Injective (typeDSimpleRootCoordinates n hn) := by
  intro x y h
  refine Subtype.ext ?_
  rw [← sum_smul_typeDSimpleRootCoordinates hn x, ← sum_smul_typeDSimpleRootCoordinates hn y, h]

/-! ## Reflections -/

private lemma typeDWeight_typeDRootReflection (hn : 4 ≤ n) (u v : TypeDRoot n) :
    typeDWeight n hn (typeDRootReflection u v).1 =
      typeDWeight n hn v.1 - (v.1 ⬝ᵥ u.1) • typeDWeight n hn u.1 := by
  rw [typeDRootReflection_val, map_sub, map_smul]

/-- Reflection in the root indexed by `k`, transported to the enumeration of the roots. -/
private noncomputable def typeDReflectionPerm (n : ℕ) (hn : 4 ≤ n)
    (k : Fin (2 * n * (n - 1))) : Fin (2 * n * (n - 1)) ≃ Fin (2 * n * (n - 1)) :=
  ((typeDRootEquiv n hn).trans (typeDRootReflectionEquiv (typeDRootEquiv n hn k))).trans
    (typeDRootEquiv n hn).symm

private lemma typeDRootEquiv_typeDReflectionPerm (hn : 4 ≤ n) (k l : Fin (2 * n * (n - 1))) :
    typeDRootEquiv n hn (typeDReflectionPerm n hn k l) =
      typeDRootReflection (typeDRootEquiv n hn k) (typeDRootEquiv n hn l) := by
  simp [typeDReflectionPerm]

private lemma typeDReflectionPerm_root (hn : 4 ≤ n) (k l : Fin (2 * n * (n - 1))) :
    typeDWeight n hn (typeDRootEquiv n hn l).1 -
        (typeDWeight n hn (typeDRootEquiv n hn l).1 ⬝ᵥ
          typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k)) •
          typeDWeight n hn (typeDRootEquiv n hn k).1 =
      typeDWeight n hn (typeDRootEquiv n hn (typeDReflectionPerm n hn k l)).1 := by
  rw [typeDRootEquiv_typeDReflectionPerm, typeDWeight_typeDRootReflection,
    typeDWeight_dotProduct_coordinates]

private lemma typeDReflectionPerm_coroot (hn : 4 ≤ n) (k l : Fin (2 * n * (n - 1))) :
    typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn l) -
        (typeDWeight n hn (typeDRootEquiv n hn k).1 ⬝ᵥ
          typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn l)) •
          typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) =
      typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn (typeDReflectionPerm n hn k l)) := by
  rw [typeDRootEquiv_typeDReflectionPerm, typeDSimpleRootCoordinates_typeDRootReflection,
    typeDWeight_dotProduct_coordinates,
    dotProduct_comm (typeDRootEquiv n hn k).1 (typeDRootEquiv n hn l).1]

/-! ## The pinned root datum -/

/-- The pinned simply connected root datum of type `Dₙ`, for `n ≥ 4`.

Both lattices are `Fin n → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. The `2 * n * (n - 1)` roots are the classical
`±e_a ± e_b` with `a ≠ b`, enumerated with the simple roots first; see
`TauCeti.DynkinType.root_typeDSimpleIndex`. -/
noncomputable def typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    RootDatum (Fin (2 * n * (n - 1))) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨fun k => typeDWeight n hn (typeDRootEquiv n hn k).1,
    (typeDWeight_injective hn).comp (typeDRootEquiv n hn).injective⟩
  coroot := ⟨fun k => typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k),
    (typeDSimpleRootCoordinates_injective hn).comp (typeDRootEquiv n hn).injective⟩
  root_coroot_two k :=
    (typeDWeight_dotProduct_coordinates hn _ (typeDRootEquiv n hn k)).trans
      (typeDRootEquiv n hn k).2
  reflectionPerm := typeDReflectionPerm n hn
  reflectionPerm_root := typeDReflectionPerm_root hn
  reflectionPerm_coroot := typeDReflectionPerm_coroot hn

-- The body of `typeDSimplyConnectedRootDatum` is not `@[expose]`d, so these three unfolding
-- lemmas are the only proofs that open it up; everything public below goes through them.
private lemma toLinearMap_eq_dotProductBilin (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).toLinearMap = dotProductBilin ℤ ℤ :=
  rfl

private lemma root_eq_typeDWeight (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).root k = typeDWeight n hn (typeDRootEquiv n hn k).1 :=
  rfl

private lemma coroot_eq_typeDSimpleRootCoordinates (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).coroot k =
      typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) :=
  rfl

/-- **The pinned pairing is the classical dot product**, in both the fundamental-weight and the
simple-coroot coordinates. -/
theorem toLinearMap_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) (x y : Fin n → ℤ) :
    (typeDSimplyConnectedRootDatum n hn).toLinearMap x y = x ⬝ᵥ y := by
  rw [toLinearMap_eq_dotProductBilin]
  rfl

/-- **The standard basis of the character lattice is the family of fundamental weights.** By
`TauCeti.DynkinType.coroot_typeDSimpleIndex` the `j`-th simple coroot is `Pi.single j 1`, so this
says `⟨ωᵢ, αⱼ^∨⟩ = δᵢⱼ`. -/
@[simp] theorem toLinearMap_typeDSimplyConnectedRootDatum_single_single (hn : 4 ≤ n)
    (i j : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).toLinearMap (Pi.single i 1) (Pi.single j 1) =
      if i = j then 1 else 0 := by
  rw [toLinearMap_typeDSimplyConnectedRootDatum, single_dotProduct, one_mul, Pi.single_apply]

/-- The `k`-th root of the pinned datum, in the fundamental-weight basis: its `j`-th coordinate is
the pairing of the `k`-th classical root with the `j`-th simple root. -/
theorem root_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) (j : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).root k j =
      (typeDRootEquiv n hn k).1 ⬝ᵥ typeDSimpleRoot n hn j := by
  rw [root_eq_typeDWeight, typeDWeight_apply]

/-- The `k`-th coroot of the pinned datum, in the simple-coroot basis: type `Dₙ` is simply laced,
so it is the family of coefficients of the `k`-th classical root in the simple roots. -/
theorem coroot_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).coroot k =
      typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) :=
  coroot_eq_typeDSimpleRootCoordinates hn k

private lemma pairing_typeDSimplyConnectedRootDatum (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).pairing k l =
      (typeDSimplyConnectedRootDatum n hn).root k ⬝ᵥ
        (typeDSimplyConnectedRootDatum n hn).coroot l :=
  rfl

/-- The root--coroot pairing of the pinned type `D` datum is symmetric. -/
theorem pairing_typeDSimplyConnectedRootDatum_comm (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).pairing k l =
      (typeDSimplyConnectedRootDatum n hn).pairing l k := by
  rw [pairing_typeDSimplyConnectedRootDatum, pairing_typeDSimplyConnectedRootDatum,
    root_eq_typeDWeight, root_eq_typeDWeight, coroot_eq_typeDSimpleRootCoordinates,
    coroot_eq_typeDSimpleRootCoordinates, typeDWeight_dotProduct_coordinates,
    typeDWeight_dotProduct_coordinates, dotProduct_comm]

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `Dₙ` datum is the `i`-th row of `CartanMatrix.D n`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) =
      fun k => CartanMatrix.D n i k := by
  funext k
  rw [root_typeDSimplyConnectedRootDatum, typeDRootEquiv_apply_typeDSimpleIndex]
  exact typeDSimpleRoot_dotProduct hn i k

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) = Pi.single i 1 := by
  rw [coroot_typeDSimplyConnectedRootDatum,
    typeDSimpleRootCoordinates_typeDRootEquiv_apply_typeDSimpleIndex]

/-- The pairing of two simple roots of the pinned datum is the corresponding entry of the
Bourbaki-numbered Cartan matrix. -/
@[simp] theorem pairing_typeDSimpleIndex (hn : 4 ≤ n) (i j : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).pairing (typeDSimpleIndex n hn i)
        (typeDSimpleIndex n hn j) = CartanMatrix.D n i j := by
  rw [pairing_typeDSimplyConnectedRootDatum, root_typeDSimpleIndex, coroot_typeDSimpleIndex,
    dotProduct_single, mul_one]

/-! ## The pinned base -/

/-- The support of the pinned base of type `Dₙ`: the first `n` root indices. -/
private abbrev typeDSimpleSupport (n : ℕ) (hn : 4 ≤ n) : Finset (Fin (2 * n * (n - 1))) :=
  simpleSupport (typeDSimpleIndex_injective hn)

private lemma mem_typeDSimpleSupport (hn : 4 ≤ n) {k : Fin (2 * n * (n - 1))} :
    k ∈ typeDSimpleSupport n hn ↔ (k : ℕ) < n :=
  mem_simpleSupport_iff_lt (typeDSimpleIndex_injective hn) (typeDSimpleIndex_val hn)

/-- In the character lattice a root is the combination of the simple roots recorded by its
classical coefficients; the coroot counterpart below uses the same coefficients. -/
private lemma sum_smul_root_typeDSimpleIndex (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) i •
        (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) =
      (typeDSimplyConnectedRootDatum n hn).root k := by
  simp only [root_eq_typeDWeight, typeDRootEquiv_apply_typeDSimpleIndex, ← map_smul]
  rw [← map_sum, sum_smul_typeDSimpleRootCoordinates]

private lemma sum_smul_coroot_typeDSimpleIndex (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) i •
        (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) =
      (typeDSimplyConnectedRootDatum n hn).coroot k := by
  rw [coroot_typeDSimplyConnectedRootDatum]
  funext j
  simp only [coroot_typeDSimpleIndex, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private lemma image_root_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).root ''
        (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) =
      range fun i : Fin n =>
        (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) :=
  image_simpleSupport _ _

private lemma image_coroot_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).coroot ''
        (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) =
      range fun i : Fin n =>
        (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) :=
  image_simpleSupport _ _

private lemma linearIndependent_root_typeDSimpleIndex (hn : 4 ≤ n) :
    LinearIndependent ℤ fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) := by
  have hroot : (fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i)) =
      fun i : Fin n => typeDWeight n hn (typeDSimpleRoot n hn i) := by
    funext i
    rw [root_eq_typeDWeight, typeDRootEquiv_apply_typeDSimpleIndex]
  rw [hroot, Fintype.linearIndependent_iff]
  intro g hg
  -- The relation says that `w = ∑ gᵢ αᵢ` is orthogonal to every simple root, hence zero.
  have hzero : typeDWeight n hn (∑ i : Fin n, g i • typeDSimpleRoot n hn i) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hg
  exact Fintype.linearIndependent_iff.mp (linearIndependent_typeDSimpleRoot hn) g
    (sum_smul_typeDSimpleRoot_eq_zero hn fun j => by
      rw [← typeDWeight_apply hn, hzero, Pi.zero_apply])

private lemma linearIndependent_coroot_typeDSimpleIndex (hn : 4 ≤ n) :
    LinearIndependent ℤ fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) := by
  simpa only [coroot_typeDSimpleIndex] using Pi.linearIndependent_single_one (Fin n) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Dₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
noncomputable def typeDSimplyConnectedBase (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).Base where
  support := typeDSimpleSupport n hn
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_root_typeDSimpleIndex hn)
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ (linearIndependent_coroot_typeDSimpleIndex hn)
  root_mem_or_neg_mem k := by
    rw [image_root_typeDSimpleSupport, ← sum_smul_root_typeDSimpleIndex hn k]
    exact sum_smul_mem_or_neg_mem_closure _ _
      (typeDSimpleRootCoordinates_nonneg_or_nonpos hn (typeDRootEquiv n hn k))
  coroot_mem_or_neg_mem k := by
    rw [image_coroot_typeDSimpleSupport, ← sum_smul_coroot_typeDSimpleIndex hn k]
    exact sum_smul_mem_or_neg_mem_closure _ _
      (typeDSimpleRootCoordinates_nonneg_or_nonpos hn (typeDRootEquiv n hn k))

/-- Membership in the pinned base support is exactly membership among the first `n` root
indices. -/
@[simp] theorem mem_typeDSimplyConnectedBase_support (hn : 4 ≤ n)
    {k : Fin (2 * n * (n - 1))} :
    k ∈ (typeDSimplyConnectedBase n hn).support ↔ (k : ℕ) < n :=
  mem_typeDSimpleSupport hn

/-- **The pinned datum of type `Dₙ` has Cartan type `D n`.** Its Bourbaki-numbered base realizes
the standard Cartan matrix `CartanMatrix.D n`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    HasCartanType (typeDSimplyConnectedRootDatum n hn) (typeDSimplyConnectedBase n hn) (.D n) :=
  hasCartanType_of_pairing_eq (typeDSimpleIndex_injective (n := n) hn) rfl fun i j =>
    (pairing_typeDSimpleIndex hn i j).trans (by simp)

/-- **The coroots of the pinned type `Dₙ` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which sits inside the
weight lattice with index four (Bourbaki, Plate IV). -/
theorem corootSpan_typeDSimplyConnectedRootDatum_eq_top (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single (coroot_typeDSimpleIndex hn)

end DynkinType

end TauCeti
