/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# The simply connected root datum of type `Dₙ`

This file constructs, uniformly in the rank `n ≥ 4`, the pinned integral root datum of type `Dₙ` on
the character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.D n` and the
`i`-th simple coroot is the `i`-th standard basis vector.

## The coordinates

The classical model is `ℤ ^ n` with the dot product: the `2 * n * (n - 1)` roots are the vectors
`±e_a ± e_b` with `a ≠ b`, which are exactly the integral vectors of squared length two, and the
Bourbaki simple roots are `αᵢ = eᵢ - eᵢ₊₁` for `i + 1 < n` together with the fork root
`α_{n-1} = e_{n-2} + e_{n-1}`. That model, its enumeration by `Fin (2 * n * (n - 1))` with the
simple roots first, the expansion of every root in the simple roots, and reflection in a root are
all supplied by `TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD` and are consumed here rather than
rebuilt.

Type `Dₙ` is simply laced, so `α^∨ = α` under the dot product and both pinned lattices are images
of the one classical model:

```text
typeDWeight x = (x ⬝ᵥ αⱼ)ⱼ,      typeDSimpleRootCoordinates x = the coefficients of x in the αᵢ.
```

The first records a vector by its pairings against the simple coroots, the second by its
coordinates in the simple coroots. Because the second family reconstructs the classical vector,
the pinned pairing is the classical dot product, `typeDWeight_dotProduct_coordinates`, and every
axiom of the datum reduces to a statement about `⬝ᵥ` on `ℤ ^ n`.

The coefficients themselves are recovered from the classical vector by
`two_mul_typeDSimpleRootCoordinates`: twice the `k`-th coefficient is the dot product with an
explicit integral vector `typeDDoubleCoweight n k`, twice the `k`-th fundamental coweight. Halving
is unavoidable — the last two fundamental coweights of type `Dₙ` are not integral vectors — and
doubling is harmless, since `ℤ` is torsion free. That one family does two jobs: it is a dual family
for the simple roots up to the factor two, which gives their linear independence, and it makes the
coefficient map visibly linear, which gives the reflection axiom for the coroots.

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
* `TauCeti.DynkinType.linearIndependent_typeDSimpleRoot`: the classical simple roots are linearly
  independent.
* `TauCeti.DynkinType.hasCartanType_typeDSimplyConnectedRootDatum`: the pinned base has Cartan type
  `D n`.
* `TauCeti.DynkinType.corootSpan_typeDSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate IV, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Dₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The Gram matrix of the Bourbaki simple roots -/

private lemma typeDSimpleRoot_apply (hn : 4 ≤ n) (i k : Fin n) :
    typeDSimpleRoot n hn i k =
      if (i : ℕ) + 1 < n then
        (if (k : ℕ) = (i : ℕ) then 1 else 0) - (if (k : ℕ) = (i : ℕ) + 1 then 1 else 0)
      else (if (k : ℕ) = n - 2 then 1 else 0) + (if (k : ℕ) = n - 1 then 1 else 0) := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSimpleRoot_of_add_one_lt hn hi, if_pos hi]
    simp [Pi.single_apply, Fin.ext_iff]
  · rw [typeDSimpleRoot_of_not_add_one_lt hn hi, if_neg hi]
    simp [Pi.single_apply, Fin.ext_iff]

private lemma typeDSimpleRoot_apply_of_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) (k : Fin n) :
    typeDSimpleRoot n hn i k =
      (if (k : ℕ) = (i : ℕ) then 1 else 0) - (if (k : ℕ) = (i : ℕ) + 1 then 1 else 0) := by
  rw [typeDSimpleRoot_apply, if_pos hi]

private lemma typeDSimpleRoot_apply_of_not_add_one_lt (hn : 4 ≤ n) {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) (k : Fin n) :
    typeDSimpleRoot n hn i k =
      (if (k : ℕ) = n - 2 then 1 else 0) + (if (k : ℕ) = n - 1 then 1 else 0) := by
  rw [typeDSimpleRoot_apply, if_neg hi]

/-- The Bourbaki `Dₙ` diagram read off `CartanMatrix.D`: two distinct nodes are joined when they
are consecutive among the first `n - 1` nodes, or are the branch node `n - 3` and the last node
`n - 1`. Separating this from the six-way definition keeps the Gram-matrix case analysis below
small. -/
private lemma cartanMatrix_D_apply (i j : Fin n) :
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
    cartanMatrix_D_apply]
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
    single_dotProduct, cartanMatrix_D_apply]
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

/-! ## The doubled fundamental coweights -/

/-- Twice the `k`-th fundamental coweight of type `Dₙ`, in classical orthogonal coordinates. The
last two fundamental coweights of type `Dₙ` are half-integral, so the doubling is what keeps this
family inside `ℤ ^ n`; over `ℤ` it is still enough to separate the simple roots. -/
private def typeDDoubleCoweight (n : ℕ) (k : Fin n) : Fin n → ℤ := fun j =>
  if (k : ℕ) + 2 < n then (if (j : ℕ) ≤ (k : ℕ) then 2 else 0)
  else if (k : ℕ) + 1 < n then (if (j : ℕ) + 1 = n then -1 else 1)
  else 1

/-- The doubled fundamental coweights are dual to the simple roots, up to the factor two. -/
private lemma typeDDoubleCoweight_dotProduct_typeDSimpleRoot (hn : 4 ≤ n) (k i : Fin n) :
    typeDDoubleCoweight n k ⬝ᵥ typeDSimpleRoot n hn i = if (k : ℕ) = (i : ℕ) then 2 else 0 := by
  have hk := k.isLt
  have hi' := i.isLt
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSimpleRoot_of_add_one_lt hn hi, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp only [typeDDoubleCoweight, mul_one]
    split_ifs <;> omega
  · rw [typeDSimpleRoot_of_not_add_one_lt hn hi, dotProduct_add, dotProduct_single,
      dotProduct_single]
    simp only [typeDDoubleCoweight, mul_one]
    split_ifs <;> omega

/-- **The Bourbaki simple roots of type `Dₙ` are linearly independent.** Pairing a relation with a
doubled fundamental coweight isolates twice one coefficient, and `ℤ` is torsion free. -/
theorem linearIndependent_typeDSimpleRoot (hn : 4 ≤ n) :
    LinearIndependent ℤ (typeDSimpleRoot n hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h : typeDDoubleCoweight n k ⬝ᵥ ∑ i : Fin n, g i • typeDSimpleRoot n hn i = 0 := by
    rw [hg, dotProduct_zero]
  rw [dotProduct_sum] at h
  simp only [dotProduct_smul, smul_eq_mul, typeDDoubleCoweight_dotProduct_typeDSimpleRoot,
    Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  omega

/-- Twice the coefficients of a root in the Bourbaki simple-root basis are the dot products with
the doubled fundamental coweights. This exhibits the coefficient map as the restriction of a linear
map, which is what the reflection axiom for the coroots needs. -/
private lemma two_mul_typeDSimpleRootCoordinates (hn : 4 ≤ n) (x : TypeDRoot n) (k : Fin n) :
    2 * typeDSimpleRootCoordinates n hn x k = typeDDoubleCoweight n k ⬝ᵥ x.1 := by
  conv_rhs => rw [← sum_smul_typeDSimpleRootCoordinates hn x]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, typeDDoubleCoweight_dotProduct_typeDSimpleRoot,
    Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-! ## The two pinned coordinate families -/

/-- The character-lattice coordinates of a classical vector of type `Dₙ`: its pairings against the
Bourbaki-numbered simple coroots, which for a simply laced type are the simple roots. -/
private def typeDWeight (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ) : Fin n → ℤ :=
  fun j => x ⬝ᵥ typeDSimpleRoot n hn j

private lemma typeDWeight_sub (hn : 4 ≤ n) (x y : Fin n → ℤ) :
    typeDWeight n hn (x - y) = typeDWeight n hn x - typeDWeight n hn y := by
  funext j
  simp only [typeDWeight, Pi.sub_apply, sub_dotProduct]

private lemma typeDWeight_sub_smul (hn : 4 ≤ n) (x y : Fin n → ℤ) (t : ℤ) :
    typeDWeight n hn (x - t • y) = typeDWeight n hn x - t • typeDWeight n hn y := by
  funext j
  simp only [typeDWeight, Pi.sub_apply, Pi.smul_apply, sub_dotProduct, smul_dotProduct]

private lemma typeDWeight_sum_smul (hn : 4 ≤ n) (g : Fin n → ℤ) (v : Fin n → (Fin n → ℤ)) :
    typeDWeight n hn (∑ i : Fin n, g i • v i) = ∑ i : Fin n, g i • typeDWeight n hn (v i) := by
  funext j
  simp only [typeDWeight, Finset.sum_apply, Pi.smul_apply, sum_dotProduct, smul_dotProduct]

/-- **The pinned pairing is the classical dot product.** Pairing the weight coordinates of a vector
against the coefficients of a root evaluates the vector on that root, because the coefficients
reconstruct the root. -/
private lemma typeDWeight_dotProduct_coordinates (hn : 4 ≤ n) (x : Fin n → ℤ) (y : TypeDRoot n) :
    typeDWeight n hn x ⬝ᵥ typeDSimpleRootCoordinates n hn y = x ⬝ᵥ y.1 := by
  calc typeDWeight n hn x ⬝ᵥ typeDSimpleRootCoordinates n hn y
      = ∑ j : Fin n, x ⬝ᵥ (typeDSimpleRootCoordinates n hn y j • typeDSimpleRoot n hn j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, smul_eq_mul, mul_comm]
        rfl
    _ = x ⬝ᵥ ∑ j : Fin n, typeDSimpleRootCoordinates n hn y j • typeDSimpleRoot n hn j :=
        (dotProduct_sum _ _ _).symm
    _ = x ⬝ᵥ y.1 := by rw [sum_smul_typeDSimpleRootCoordinates hn y]

private lemma typeDWeight_injective (hn : 4 ≤ n) :
    Injective fun x : TypeDRoot n => typeDWeight n hn x.1 := by
  intro x y hxy
  have hxy' : typeDWeight n hn x.1 = typeDWeight n hn y.1 := hxy
  have hzero : typeDWeight n hn (x.1 - y.1) = 0 := by
    rw [typeDWeight_sub, hxy']
    exact sub_self _
  have hd : ∀ z : TypeDRoot n, (x.1 - y.1) ⬝ᵥ z.1 = 0 := fun z => by
    rw [← typeDWeight_dotProduct_coordinates hn (x.1 - y.1) z, hzero, zero_dotProduct]
  have hself : (x.1 - y.1) ⬝ᵥ (x.1 - y.1) = 0 := by
    rw [dotProduct_sub, hd x, hd y, sub_zero]
  exact Subtype.ext (sub_eq_zero.mp (dotProduct_self_eq_zero.mp hself))

private lemma typeDSimpleRootCoordinates_injective (hn : 4 ≤ n) :
    Injective (typeDSimpleRootCoordinates n hn) := by
  intro x y h
  refine Subtype.ext ?_
  rw [← sum_smul_typeDSimpleRootCoordinates hn x, ← sum_smul_typeDSimpleRootCoordinates hn y, h]

/-! ## Reflections -/

private lemma typeDWeight_typeDRootReflection (hn : 4 ≤ n) (u v : TypeDRoot n) :
    typeDWeight n hn (typeDRootReflection u v).1 =
      typeDWeight n hn v.1 - (v.1 ⬝ᵥ u.1) • typeDWeight n hn u.1 := by
  rw [typeDRootReflection_val, typeDWeight_sub_smul]

private lemma typeDSimpleRootCoordinates_typeDRootReflection (hn : 4 ≤ n) (u v : TypeDRoot n) :
    typeDSimpleRootCoordinates n hn (typeDRootReflection u v) =
      typeDSimpleRootCoordinates n hn v - (v.1 ⬝ᵥ u.1) • typeDSimpleRootCoordinates n hn u := by
  funext k
  have h := two_mul_typeDSimpleRootCoordinates hn (typeDRootReflection u v) k
  rw [typeDRootReflection_val, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    ← two_mul_typeDSimpleRootCoordinates hn v k, ← two_mul_typeDSimpleRootCoordinates hn u k] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

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

private instance : (dotProductBilin ℤ ℤ :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] ℤ).IsPerfPair := by
  -- `dotProductEquiv` has `dotProductBilin` as its underlying linear map by definition.
  change (dotProductEquiv ℤ (Fin n)).toLinearMap.IsPerfPair
  infer_instance

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

/-- The root index type used above is the one the Dynkin type pins. -/
example (n : ℕ) : (DynkinType.D n).numRoots = 2 * n * (n - 1) := numRoots_D n

private lemma root_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).root k = typeDWeight n hn (typeDRootEquiv n hn k).1 :=
  rfl

private lemma coroot_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).coroot k =
      typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) :=
  rfl

private lemma pairing_typeDSimplyConnectedRootDatum (hn : 4 ≤ n)
    (k l : Fin (2 * n * (n - 1))) :
    (typeDSimplyConnectedRootDatum n hn).pairing k l =
      (typeDSimplyConnectedRootDatum n hn).root k ⬝ᵥ
        (typeDSimplyConnectedRootDatum n hn).coroot l :=
  rfl

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

/-! ## The pinned base -/

private lemma sum_smul_mem_closure {M : Type*} [AddCommGroup M] (v : Fin n → M) (c : Fin n → ℤ)
    (hc : ∀ i, 0 ≤ c i) : (∑ i : Fin n, c i • v i) ∈ AddSubmonoid.closure (range v) := by
  refine AddSubmonoid.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hc i)
  rw [hm, natCast_zsmul]
  exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (mem_range_self i)) m

private lemma sum_smul_mem_or_neg_mem_closure {M : Type*} [AddCommGroup M] (v : Fin n → M)
    (c : Fin n → ℤ) (hc : (∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)) :
    (∑ i : Fin n, c i • v i) ∈ AddSubmonoid.closure (range v) ∨
      -(∑ i : Fin n, c i • v i) ∈ AddSubmonoid.closure (range v) := by
  rcases hc with h | h
  · exact Or.inl (sum_smul_mem_closure v c h)
  · refine Or.inr ?_
    rw [← Finset.sum_neg_distrib]
    simp only [← neg_smul]
    exact sum_smul_mem_closure v (fun i => -c i) fun i => neg_nonneg.mpr (h i)

/-- The support of the pinned base of type `Dₙ`: the first `n` root indices. -/
private def typeDSimpleSupport (n : ℕ) (hn : 4 ≤ n) : Finset (Fin (2 * n * (n - 1))) :=
  Finset.univ.map ⟨typeDSimpleIndex n hn, typeDSimpleIndex_injective hn⟩

private lemma mem_typeDSimpleSupport (hn : 4 ≤ n) {k : Fin (2 * n * (n - 1))} :
    k ∈ typeDSimpleSupport n hn ↔ (k : ℕ) < n := by
  constructor
  · rintro hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hk
    simpa only [Function.Embedding.coeFn_mk, typeDSimpleIndex_val] using i.isLt
  · intro hk
    exact Finset.mem_map.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

private lemma coe_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) = range (typeDSimpleIndex n hn) := by
  simp [typeDSimpleSupport]

/-- In the character lattice a root is the combination of the simple roots recorded by its
classical coefficients; the coroot counterpart below uses the same coefficients. -/
private lemma sum_smul_root_typeDSimpleIndex (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) i •
        (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) =
      (typeDSimplyConnectedRootDatum n hn).root k := by
  simp only [root_typeDSimplyConnectedRootDatum, typeDRootEquiv_apply_typeDSimpleIndex]
  rw [← typeDWeight_sum_smul, sum_smul_typeDSimpleRootCoordinates]

private lemma sum_smul_coroot_typeDSimpleIndex (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn k) i •
        (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) =
      (typeDSimplyConnectedRootDatum n hn).coroot k := by
  rw [coroot_typeDSimplyConnectedRootDatum]
  funext j
  simp only [coroot_typeDSimpleIndex, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma image_root_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).root ''
        (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) =
      range fun i : Fin n =>
        (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) := by
  rw [coe_typeDSimpleSupport, ← range_comp]
  rfl

private lemma image_coroot_typeDSimpleSupport (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).coroot ''
        (typeDSimpleSupport n hn : Set (Fin (2 * n * (n - 1)))) =
      range fun i : Fin n =>
        (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) := by
  rw [coe_typeDSimpleSupport, ← range_comp]
  rfl

private lemma linearIndependent_root_typeDSimpleIndex (hn : 4 ≤ n) :
    LinearIndependent ℤ fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i) := by
  have hroot : (fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).root (typeDSimpleIndex n hn i)) =
      fun i : Fin n => typeDWeight n hn (typeDSimpleRoot n hn i) := by
    funext i
    rw [root_typeDSimplyConnectedRootDatum, typeDRootEquiv_apply_typeDSimpleIndex]
  rw [hroot, Fintype.linearIndependent_iff]
  intro g hg
  -- The relation says that `w = ∑ gᵢ αᵢ` is orthogonal to every simple root, hence to itself.
  have hzero : typeDWeight n hn (∑ i : Fin n, g i • typeDSimpleRoot n hn i) = 0 := by
    rw [typeDWeight_sum_smul]
    exact hg
  have horth : ∀ j : Fin n,
      (∑ i : Fin n, g i • typeDSimpleRoot n hn i) ⬝ᵥ typeDSimpleRoot n hn j = 0 :=
    fun j => congrFun hzero j
  have hself : (∑ i : Fin n, g i • typeDSimpleRoot n hn i) ⬝ᵥ
      ∑ i : Fin n, g i • typeDSimpleRoot n hn i = 0 := by
    rw [dotProduct_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dotProduct_smul, horth i, smul_zero]
  exact Fintype.linearIndependent_iff.mp (linearIndependent_typeDSimpleRoot hn) g
    (dotProduct_self_eq_zero.mp hself)

private lemma linearIndependent_coroot_typeDSimpleIndex (hn : 4 ≤ n) :
    LinearIndependent ℤ fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i) := by
  have hcoroot : (fun i : Fin n =>
      (typeDSimplyConnectedRootDatum n hn).coroot (typeDSimpleIndex n hn i)) =
      fun i : Fin n => (Pi.basisFun ℤ (Fin n)) i := by
    funext i
    rw [coroot_typeDSimpleIndex]
    simp
  rw [hcoroot]
  exact (Pi.basisFun ℤ (Fin n)).linearIndependent

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Dₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
noncomputable def typeDSimplyConnectedBase (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).Base where
  support := typeDSimpleSupport n hn
  linearIndepOn_root := by
    have h : LinearIndepOn ℤ (typeDSimplyConnectedRootDatum n hn).root
        (range (typeDSimpleIndex n hn)) := by
      rw [linearIndepOn_range_iff (typeDSimpleIndex_injective hn)]
      exact linearIndependent_root_typeDSimpleIndex hn
    rwa [← coe_typeDSimpleSupport] at h
  linearIndepOn_coroot := by
    have h : LinearIndepOn ℤ (typeDSimplyConnectedRootDatum n hn).coroot
        (range (typeDSimpleIndex n hn)) := by
      rw [linearIndepOn_range_iff (typeDSimpleIndex_injective hn)]
      exact linearIndependent_coroot_typeDSimpleIndex hn
    rwa [← coe_typeDSimpleSupport] at h
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

/-- The support of the pinned base is the Bourbaki numbering of the simple roots. -/
private def typeDBaseEquiv (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedBase n hn).support ≃ Fin n where
  toFun x := ⟨(x : Fin (2 * n * (n - 1))), (mem_typeDSimpleSupport hn).mp x.2⟩
  invFun i := ⟨typeDSimpleIndex n hn i, (mem_typeDSimpleSupport hn).mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    simp
  right_inv i := by
    apply Fin.ext
    simp

private lemma pairing_typeDSimpleIndex (hn : 4 ≤ n) (i j : Fin n) :
    (typeDSimplyConnectedRootDatum n hn).pairing (typeDSimpleIndex n hn i)
        (typeDSimpleIndex n hn j) = CartanMatrix.D n i j := by
  rw [pairing_typeDSimplyConnectedRootDatum, root_typeDSimpleIndex, coroot_typeDSimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `Dₙ` has Cartan type `D n`.** Its Bourbaki-numbered base realizes
the standard Cartan matrix `CartanMatrix.D n`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_typeDSimplyConnectedRootDatum (n : ℕ) (hn : 4 ≤ n) :
    HasCartanType (typeDSimplyConnectedRootDatum n hn) (typeDSimplyConnectedBase n hn) (.D n) := by
  rw [hasCartanType_iff]
  refine ⟨typeDBaseEquiv n hn, fun i j => ?_⟩
  have hi : (i : Fin (2 * n * (n - 1))) = typeDSimpleIndex n hn (typeDBaseEquiv n hn i) :=
    Fin.ext (by simp [typeDBaseEquiv])
  have hj : (j : Fin (2 * n * (n - 1))) = typeDSimpleIndex n hn (typeDBaseEquiv n hn j) :=
    Fin.ext (by simp [typeDBaseEquiv])
  rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply, hi, hj, pairing_typeDSimpleIndex,
    cartanMatrix_D]
  rfl

/-- **The coroots of the pinned type `Dₙ` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which sits inside the
weight lattice with index four (Bourbaki, Plate IV). -/
theorem corootSpan_typeDSimplyConnectedRootDatum_eq_top (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).corootSpan ℤ = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨typeDSimpleIndex n hn i, by rw [coroot_typeDSimpleIndex]; simp⟩

end DynkinType

end TauCeti
