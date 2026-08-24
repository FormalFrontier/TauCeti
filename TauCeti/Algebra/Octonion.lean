/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The split octonions

The split octonions over a commutative ring `R` are realized here as **Zorn vector matrices**: an
element is a formal `2 × 2` matrix

`⟨a, b, v, w⟩ = [[a, v], [w, b]]`

with scalar diagonal `a b : R` and vector off-diagonal `v w : Fin 3 → R`, multiplied by

`[[a, v], [w, b]] * [[a', v'], [w', b']] =`
`  [[a * a' + v ⬝ᵥ w', a • v' + b' • v - w ⨯₃ w'], [a' • w + b • w' + v ⨯₃ v', b * b' + w ⬝ᵥ v']]`

using the dot and cross products of `Fin 3 → R`. This is an `8`-dimensional unital `R`-algebra
carrying the multiplicative norm `N ⟨a, b, v, w⟩ = a * b - v ⬝ᵥ w`, the determinant of the vector
matrix: it is the split Cayley algebra, the split form of the octonions. It is alternative, and the
worked examples at the end of the file exhibit an `R` — namely `ℤ` — over which it is neither
commutative nor associative; no such failure is claimed for every base ring, since over the zero
ring `Octonion R` is trivial and hence both.

Zorn's model is used rather than a Cayley--Dickson doubling of the split quaternions because the two
produce the same algebra while the vector matrices carry the norm form on their sleeve: `N` is a
determinant, and its multiplicativity reduces to Mathlib's scalar quadruple product identity
`Matrix.cross_dot_cross`.

Everything is stated over a commutative ring; no field, characteristic or closedness hypothesis is
needed for the algebra structure, the conjugation, or the norm. Only the two dimension counts
`TauCeti.Octonion.finrank_eq_eight` and `TauCeti.Octonion.finrank_imaginary` ask for a base over
which ranks are well behaved, and each asks for it as `StrongRankCondition` and nothing more.

## Main definitions

* `TauCeti.Octonion`: the split octonions over `R`, as Zorn vector matrices, with their
  `NonAssocRing` and `Module R` structure and the two scalar towers.
* `TauCeti.Octonion.conj`: octonion conjugation `⟨a, b, v, w⟩ ↦ ⟨b, a, -v, -w⟩`, an `R`-linear
  involution.
* `TauCeti.Octonion.trace` and `TauCeti.Octonion.norm`: the trace `a + b` and the norm
  `a * b - v ⬝ᵥ w` of the composition algebra.
* `TauCeti.Octonion.imaginary`: the imaginary octonions, the kernel of the trace.

## Main results

* `TauCeti.Octonion.finrank_eq_eight`: the split octonions are `8`-dimensional.
* `TauCeti.Octonion.self_mul_conj` and `TauCeti.Octonion.conj_mul_self`:
  `x * x̄ = x̄ * x = N x • 1`.
* `TauCeti.Octonion.norm_mul`: the norm is **multiplicative**, so `𝕆` is a composition algebra.
* `TauCeti.Octonion.normQuadraticForm`: the norm, bundled as a `QuadraticForm`, so that Mathlib's
  `QuadraticMap.polar` API supplies the associated symmetric bilinear form. That form is visible
  inside the algebra as `TauCeti.Octonion.mul_conj_add_mul_conj`,
  `x * conj y + y * conj x = QuadraticMap.polar (normQuadraticForm R) x y • 1`, and it is the trace
  form of the composition algebra, `TauCeti.Octonion.trace_mul_conj`.
* `TauCeti.Octonion.left_alternative`, `TauCeti.Octonion.right_alternative` and
  `TauCeti.Octonion.flexible`: `𝕆` is **alternative** and **flexible**.
* `TauCeti.Octonion.moufang_left`, `TauCeti.Octonion.moufang_right` and
  `TauCeti.Octonion.moufang_middle`: the three **Moufang identities**.
* `TauCeti.Octonion.mul_self`: every octonion satisfies its rank-two equation
  `x * x = trace x • x - norm x • 1`.
* `TauCeti.Octonion.finrank_imaginary`: the imaginary octonions, the trace-zero subspace, are
  `7`-dimensional. The derivation algebra `Der 𝕆` is `TauCeti.derivationLieAlgebra R (Octonion R)`
  (`TauCeti/Algebra/Lie/Derivation.lean`); identifying the imaginary octonions with the fundamental
  representation of `G₂ = Der 𝕆` still waits on the count `finrank (Der 𝕆) = 14` and the
  isomorphism with `LieAlgebra.g₂`, neither of which is proved here.

## Implementation notes

Almost every identity below is proved without ever looking at a coordinate: `Octonion.ext` splits an
equation of octonions into its four entries, a file-local simp set pushes the dot and cross products
of `Fin 3 → R` through the linear combinations that make up an entry of a product and reduces the
compound products that survive by Mathlib's `Matrix.cross_dot_cross`,
`Matrix.cross_cross_eq_smul_sub_smul` and `Matrix.cross_cross_eq_smul_sub_smul'`, and `module` or
`ring` finishes. The two Moufang identities proved directly are the exception: they need relations
special to three coordinates that Mathlib does not name, so they — and the worked examples — expand
the vector entries into coordinates through `Matrix.vec3_dotProduct` and `Matrix.cross_apply`, with
a private coordinate extensionality lemma splitting an equation of octonions into its eight scalar
coordinates.

No definition here is exposed: consumers work through the projection `simp` lemmas rather than
through any definition body. The additive and module structures are built directly on the
componentwise operations, and `TauCeti.Octonion.linearEquivProd` packages a vector matrix as the
tuple of its four entries, an `R`-linear isomorphism, which is what the dimension count runs
through.

The norm is available both as the bare map `Octonion R → R` the roadmap pins and, through
`TauCeti.Octonion.normQuadraticForm`, as a `QuadraticForm R (Octonion R)`; the bundled form is what
gives its polarization Mathlib's bilinearity and symmetry API for free. The derivation algebra
`Der 𝕆` is
`TauCeti.derivationLieAlgebra R (Octonion R)`, built in `TauCeti/Algebra/Lie/Derivation.lean`.

## References

This implements the split-octonion target of Layer 8 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` ("The split octonions `𝕆` ... built
here (`Octonion K`) with its conjugation, norm, alternative and Moufang identities, and its
multiplication as an honest `K`-bilinear operation"), whose `Suggested.lean` pins it as `Octonion`,
`finrank_octonion`, `octonionConj`, `octonionNorm`, `octonionNorm_mul`, `octonion_left_alternative`,
`imaginaryOctonion` and `finrank_imaginaryOctonion`; those are the declarations below, named inside
the `Octonion` namespace. That roadmap's `## Ordering` marks this unit as buildable from scratch at
any time, independently of every other layer.

The model is M. Zorn, *Alternativkörper und quadratische Systeme*, Abh. Math. Sem. Univ. Hamburg 9
(1933); see also T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional
Groups*, §1.8, and J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002), §2.
-/

public section

namespace TauCeti

open Matrix

/-- The **split octonions** over `R`, as Zorn vector matrices: the element `⟨a, b, v, w⟩` is the
formal matrix `[[a, v], [w, b]]` with scalar diagonal and vector off-diagonal entries. -/
@[ext]
structure Octonion (R : Type*) where
  /-- The top-left, scalar entry of the vector matrix. -/
  a : R
  /-- The bottom-right, scalar entry of the vector matrix. -/
  b : R
  /-- The top-right, vector entry of the vector matrix. -/
  v : Fin 3 → R
  /-- The bottom-left, vector entry of the vector matrix. -/
  w : Fin 3 → R

namespace Octonion

variable {R S : Type*}

/-- Two vector matrices agreeing in each of their eight scalar coordinates are equal. This is the
form of extensionality the coordinate computations of the Moufang identities use; it is private,
since `Octonion.ext` is the extensionality lemma consumers want. -/
private theorem ext_coords {x y : Octonion R} (ha : x.a = y.a) (hb : x.b = y.b)
    (hv₀ : x.v 0 = y.v 0) (hv₁ : x.v 1 = y.v 1) (hv₂ : x.v 2 = y.v 2)
    (hw₀ : x.w 0 = y.w 0) (hw₁ : x.w 1 = y.w 1) (hw₂ : x.w 2 = y.w 2) : x = y := by
  refine Octonion.ext ha hb (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    exacts [hv₀, hv₁, hv₂]
  · fin_cases i
    exacts [hw₀, hw₁, hw₂]

/-! ### The additive and module structure -/

instance [Zero R] : Zero (Octonion R) := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem zero_a [Zero R] : (0 : Octonion R).a = 0 := (rfl)
@[simp] theorem zero_b [Zero R] : (0 : Octonion R).b = 0 := (rfl)
@[simp] theorem zero_v [Zero R] : (0 : Octonion R).v = 0 := (rfl)
@[simp] theorem zero_w [Zero R] : (0 : Octonion R).w = 0 := (rfl)

instance [Zero R] : Inhabited (Octonion R) := ⟨0⟩

instance [Zero R] [One R] : One (Octonion R) := ⟨⟨1, 1, 0, 0⟩⟩

@[simp] theorem one_a [Zero R] [One R] : (1 : Octonion R).a = 1 := (rfl)
@[simp] theorem one_b [Zero R] [One R] : (1 : Octonion R).b = 1 := (rfl)
@[simp] theorem one_v [Zero R] [One R] : (1 : Octonion R).v = 0 := (rfl)
@[simp] theorem one_w [Zero R] [One R] : (1 : Octonion R).w = 0 := (rfl)

instance [Add R] : Add (Octonion R) :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.v + y.v, x.w + y.w⟩⟩

@[simp] theorem add_a [Add R] (x y : Octonion R) : (x + y).a = x.a + y.a := (rfl)
@[simp] theorem add_b [Add R] (x y : Octonion R) : (x + y).b = x.b + y.b := (rfl)
@[simp] theorem add_v [Add R] (x y : Octonion R) : (x + y).v = x.v + y.v := (rfl)
@[simp] theorem add_w [Add R] (x y : Octonion R) : (x + y).w = x.w + y.w := (rfl)

instance [Neg R] : Neg (Octonion R) := ⟨fun x => ⟨-x.a, -x.b, -x.v, -x.w⟩⟩

@[simp] theorem neg_a [Neg R] (x : Octonion R) : (-x).a = -x.a := (rfl)
@[simp] theorem neg_b [Neg R] (x : Octonion R) : (-x).b = -x.b := (rfl)
@[simp] theorem neg_v [Neg R] (x : Octonion R) : (-x).v = -x.v := (rfl)
@[simp] theorem neg_w [Neg R] (x : Octonion R) : (-x).w = -x.w := (rfl)

instance [Sub R] : Sub (Octonion R) :=
  ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.v - y.v, x.w - y.w⟩⟩

@[simp] theorem sub_a [Sub R] (x y : Octonion R) : (x - y).a = x.a - y.a := (rfl)
@[simp] theorem sub_b [Sub R] (x y : Octonion R) : (x - y).b = x.b - y.b := (rfl)
@[simp] theorem sub_v [Sub R] (x y : Octonion R) : (x - y).v = x.v - y.v := (rfl)
@[simp] theorem sub_w [Sub R] (x y : Octonion R) : (x - y).w = x.w - y.w := (rfl)

instance [SMul S R] : SMul S (Octonion R) :=
  ⟨fun s x => ⟨s • x.a, s • x.b, s • x.v, s • x.w⟩⟩

@[simp] theorem smul_a [SMul S R] (s : S) (x : Octonion R) : (s • x).a = s • x.a := (rfl)
@[simp] theorem smul_b [SMul S R] (s : S) (x : Octonion R) : (s • x).b = s • x.b := (rfl)
@[simp] theorem smul_v [SMul S R] (s : S) (x : Octonion R) : (s • x).v = s • x.v := (rfl)
@[simp] theorem smul_w [SMul S R] (s : S) (x : Octonion R) : (s • x).w = s • x.w := (rfl)

/- The structures below are built directly on the componentwise operations rather than transported
along an injection into `R × R × (Fin 3 → R) × (Fin 3 → R)`: a transport would have to name that
injection and its injectivity proof in an instance body, and an instance body may mention only
public declarations, so the helper would have to be part of the public API. -/
instance [AddCommGroup R] : AddCommGroup (Octonion R) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  neg_add_cancel _ := by ext <;> simp
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  add_comm _ _ := by ext <;> simp [add_comm]
  nsmul n x := n • x
  nsmul_zero _ := by ext <;> simp
  nsmul_succ _ _ := by ext <;> simp [succ_nsmul]
  zsmul n x := n • x
  zsmul_zero' _ := by ext <;> simp
  zsmul_succ' _ _ := by ext <;> simp [add_zsmul]
  zsmul_neg' _ _ := by ext <;> simp [add_zsmul, succ_nsmul]

instance [Monoid S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S (Octonion R) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

instance [Semiring S] [AddCommGroup R] [Module S R] : Module S (Octonion R) where
  add_smul _ _ _ := by ext <;> simp [add_smul]
  zero_smul _ := by ext <;> simp

instance [AddCommGroup R] [One R] : AddCommGroupWithOne (Octonion R) where
  __ := (inferInstance : AddCommGroup (Octonion R))
  one := 1

/-- The components of a vector matrix, as an `R`-linear isomorphism with the tuple of its four
entries. -/
def linearEquivProd (R : Type*) [CommRing R] :
    Octonion R ≃ₗ[R] R × R × (Fin 3 → R) × (Fin 3 → R) where
  toFun x := (x.a, x.b, x.v, x.w)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem linearEquivProd_apply [CommRing R] (x : Octonion R) :
    linearEquivProd R x = (x.a, x.b, x.v, x.w) := (rfl)

@[simp] theorem linearEquivProd_symm_apply [CommRing R] (p : R × R × (Fin 3 → R) × (Fin 3 → R)) :
    (linearEquivProd R).symm p = ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ := (rfl)

instance [CommRing R] : Module.Free R (Octonion R) :=
  Module.Free.of_equiv (linearEquivProd R).symm

instance [CommRing R] : Module.Finite R (Octonion R) :=
  Module.Finite.equiv (linearEquivProd R).symm

/-- **The split octonions are `8`-dimensional**: two scalar and two vector entries. -/
theorem finrank_eq_eight (R : Type*) [CommRing R] [StrongRankCondition R] :
    Module.finrank R (Octonion R) = 8 := by
  rw [(linearEquivProd R).finrank_eq]
  simp

/-! ### The multiplication -/

variable [CommRing R]

/-- The Zorn vector-matrix product: the matrix product of `[[a, v], [w, b]]` and
`[[a', v'], [w', b']]`, with the vector entries paired by the dot product and corrected by a cross
product. -/
instance : Mul (Octonion R) :=
  ⟨fun x y => ⟨x.a * y.a + x.v ⬝ᵥ y.w, x.b * y.b + x.w ⬝ᵥ y.v,
    x.a • y.v + y.b • x.v - x.w ⨯₃ y.w, y.a • x.w + x.b • y.w + x.v ⨯₃ y.v⟩⟩

@[simp] theorem mul_a (x y : Octonion R) : (x * y).a = x.a * y.a + x.v ⬝ᵥ y.w := (rfl)
@[simp] theorem mul_b (x y : Octonion R) : (x * y).b = x.b * y.b + x.w ⬝ᵥ y.v := (rfl)

@[simp] theorem mul_v (x y : Octonion R) :
    (x * y).v = x.a • y.v + y.b • x.v - x.w ⨯₃ y.w := (rfl)

@[simp] theorem mul_w (x y : Octonion R) :
    (x * y).w = y.a • x.w + x.b • y.w + x.v ⨯₃ y.v := (rfl)

/- The vector simp set. Dot and cross products are pushed through the linear combinations that make
up an entry of a product — the dot product by Mathlib's bilinearity `simp` lemmas, the cross product
by `LinearMap.map_add₂`, `LinearMap.map_sub₂` and `LinearMap.map_smul₂` in its first argument and by
`map_add`, `map_sub` and `map_smul` in its second — and the compound products that survive are
reduced by Mathlib's own identities: `Matrix.cross_dot_cross` for a dot product of two cross
products, and `Matrix.cross_cross_eq_smul_sub_smul` and its primed form for an iterated cross
product. What is left is a linear combination of the entries and their cross products, which
`module` closes, or a polynomial in their dot products, which `ring` closes. -/
section Vector

attribute [local simp] LinearMap.map_add₂ LinearMap.map_sub₂ LinearMap.map_smul₂
  cross_dot_cross cross_cross_eq_smul_sub_smul cross_cross_eq_smul_sub_smul'

instance : NonAssocRing (Octonion R) where
  __ := (inferInstance : AddCommGroupWithOne (Octonion R))
  left_distrib x y z := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [add_smul] <;> ring
  right_distrib x y z := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [add_smul] <;> ring
  zero_mul x := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  mul_zero x := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  one_mul x := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
  mul_one x := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

instance : SMulCommClass R (Octonion R) (Octonion R) where
  smul_comm r x y := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
    · ring
    · ring
    · module
    · module

instance : IsScalarTower R (Octonion R) (Octonion R) where
  smul_assoc r x y := by
    refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp
    · ring
    · ring
    · module
    · module

/-! ### Conjugation, trace and norm -/

/-- **Octonion conjugation** `⟨a, b, v, w⟩ ↦ ⟨b, a, -v, -w⟩`: it exchanges the two diagonal entries
and negates the two vector entries, so it fixes `1` and negates the imaginary part. -/
def conj : Octonion R →ₗ[R] Octonion R where
  toFun x := ⟨x.b, x.a, -x.v, -x.w⟩
  map_add' _ _ := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [add_comm]
  map_smul' _ _ := by refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

@[simp] theorem conj_a (x : Octonion R) : (conj x).a = x.b := (rfl)
@[simp] theorem conj_b (x : Octonion R) : (conj x).b = x.a := (rfl)
@[simp] theorem conj_v (x : Octonion R) : (conj x).v = -x.v := (rfl)
@[simp] theorem conj_w (x : Octonion R) : (conj x).w = -x.w := (rfl)

@[simp, grind =] theorem conj_conj (x : Octonion R) : conj (conj x) = x := by
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

@[simp, grind =] theorem conj_one : conj (1 : Octonion R) = 1 := by
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp

/-- **Conjugation is an anti-automorphism**: it reverses products. -/
@[simp, grind =]
theorem conj_mul (x y : Octonion R) : conj (x * y) = conj y * conj x := by
  -- The two vector entries pick up the sign of `Matrix.cross_anticomm`, the two scalar entries the
  -- symmetry of the dot product. `Matrix.cross_anticomm` is used at the two entries it is needed at
  -- rather than in its `simp` orientation, which would leave the two sides with opposite argument
  -- orders.
  refine Octonion.ext ?_ ?_ ?_ ?_ <;>
    simp [-cross_anticomm, ← cross_anticomm y.v x.v, ← cross_anticomm y.w x.w, dotProduct_comm,
      mul_comm] <;> module

/-- **The trace** `⟨a, b, v, w⟩ ↦ a + b` of a vector matrix, the coefficient of the rank-two
equation `TauCeti.Octonion.mul_self`. -/
def trace : Octonion R →ₗ[R] R where
  toFun x := x.a + x.b
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp [smul_eq_mul, mul_add]

@[simp] theorem trace_apply (x : Octonion R) : trace x = x.a + x.b := (rfl)

/-- The trace of `1` is `2`, not `1`: the identity vector matrix has two diagonal entries. Not a
`simp` lemma, because `TauCeti.Octonion.trace_apply` already takes its left-hand side apart. -/
theorem trace_one : trace (1 : Octonion R) = 2 := by
  simp only [trace_apply, one_a, one_b, one_add_one_eq_two]

/-- An octonion and its conjugate add up to a scalar: the trace. -/
theorem add_conj (x : Octonion R) : x + conj x = trace x • 1 := by
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [add_comm]

/-- Conjugation preserves the trace: it only exchanges the two diagonal entries. Not a `simp`
lemma, for the same reason as `TauCeti.Octonion.trace_one`. -/
theorem trace_conj (x : Octonion R) : trace (conj x) = trace x := by
  simp [add_comm]

/-- **The trace is symmetric in a product**: `trace (x * y) = trace (y * x)`, since the two dot
products of a Zorn product are exchanged when the factors are. Not a `simp` lemma, for the same
reason as `TauCeti.Octonion.trace_one`. -/
theorem trace_mul_comm (x y : Octonion R) : trace (x * y) = trace (y * x) := by
  simp [dotProduct_comm, mul_comm]
  ring

/-- **The norm** `⟨a, b, v, w⟩ ↦ a * b - v ⬝ᵥ w` of a vector matrix: the determinant of the matrix,
and the norm form of the composition algebra `𝕆`. -/
def norm (x : Octonion R) : R := x.a * x.b - x.v ⬝ᵥ x.w

theorem norm_def (x : Octonion R) : norm x = x.a * x.b - x.v ⬝ᵥ x.w := (rfl)

@[simp, grind =] theorem norm_one : norm (1 : Octonion R) = 1 := by simp [norm_def]

@[simp, grind =] theorem norm_zero : norm (0 : Octonion R) = 0 := by simp [norm_def]

@[simp, grind =] theorem norm_conj (x : Octonion R) : norm (conj x) = norm x := by
  simp [norm_def]; ring

/-- The norm is even: negating an octonion negates both its scalar and both its vector entries, so
each of the two products making up the norm is unchanged. -/
@[simp, grind =] theorem norm_neg (x : Octonion R) : norm (-x) = norm x := by
  simp [norm_def]

/-- The norm is homogeneous of degree two: rescaling an octonion by `r` rescales its norm by
`r ^ 2`. -/
@[simp, grind =]
theorem norm_smul (r : R) (x : Octonion R) : norm (r • x) = r ^ 2 * norm x := by
  simp [norm_def]; ring

/-- `x * x̄ = N x • 1`: conjugation inverts an octonion up to its norm. -/
@[simp, grind =]
theorem self_mul_conj (x : Octonion R) : x * conj x = norm x • 1 := by
  -- The two vector entries vanish by `Matrix.cross_self`.
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [norm_def, dotProduct_comm] <;> ring

/-- `x̄ * x = N x • 1`, the mirror of `TauCeti.Octonion.self_mul_conj`. -/
@[simp, grind =]
theorem conj_mul_self (x : Octonion R) : conj x * x = norm x • 1 := by
  simpa using self_mul_conj (conj x)

/-- **The rank-two equation.** Every split octonion satisfies `x² - trace x · x + N x · 1 = 0`, so
it generates a subalgebra of dimension at most `2`. -/
theorem mul_self (x : Octonion R) : x * x = trace x • x - norm x • 1 := by
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [norm_def, dotProduct_comm, add_smul]
  ring

/-- **The norm of a split octonion is multiplicative**, so `𝕆` is a composition algebra. -/
@[simp, grind =]
theorem norm_mul (x y : Octonion R) : norm (x * y) = norm x * norm y := by
  -- The scalar quadruple product identity `Matrix.cross_dot_cross`, a Binet--Cauchy identity, does
  -- the work: the cross-product corrections to the vector entries of a product are exactly what the
  -- two dot products of the norm need.
  simp [norm_def, dotProduct_comm]
  ring

/-! ### The norm as a quadratic form -/

/-- **The norm is a quadratic form.** Its companion is the bilinear map
`(x, y) ↦ a b' + a' b - v ⬝ᵥ w' - v' ⬝ᵥ w`, the polarization of the determinant of a vector matrix.
Packaging the norm this way makes Mathlib's `QuadraticMap.polar` API — symmetry, bilinearity in each
argument, and `QuadraticMap.polar_self` — available for the associated symmetric form, which is what
the Hermitian matrix algebras over `𝕆` are built from. -/
def normQuadraticForm (R : Type*) [CommRing R] : QuadraticForm R (Octonion R) :=
  -- `QuadraticMap.ofPolar` asks only for the two left-argument laws and derives the right-argument
  -- ones from `QuadraticMap.polar_comm`.
  QuadraticMap.ofPolar norm (fun _ _ => by simp [smul_eq_mul]; ring)
    (fun _ _ _ => by
      simp [QuadraticMap.polar, norm_def, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by
      simp [QuadraticMap.polar, norm_def, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

@[simp] theorem normQuadraticForm_apply (x : Octonion R) : normQuadraticForm R x = norm x := (rfl)

/-- The polar form of the norm, read off the entries of the two vector matrices. Stated for
`QuadraticMap.polar` rather than for `QuadraticMap.polarBilin`, which `simp` unfolds to it. Not a
`simp` lemma: the polar form and its half `QuadraticMap.associated` are the interface the Hermitian
matrix algebras are stated against, and `simp` should not take it apart into coordinates behind
their backs. -/
theorem polar_normQuadraticForm (x y : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) x y =
      x.a * y.b + y.a * x.b - x.v ⬝ᵥ y.w - y.v ⬝ᵥ x.w := by
  simp [QuadraticMap.polar, norm_def, add_dotProduct, dotProduct_add]
  ring

/-- The polar form of the norm is unchanged by conjugating both arguments: conjugation is additive
and preserves the norm. -/
theorem polar_normQuadraticForm_conj (x y : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) (conj x) (conj y) =
      QuadraticMap.polar (normQuadraticForm R) x y := by
  simp [polar_normQuadraticForm]
  ring

/-- **The polar form of the norm is the trace form** `(x, y) ↦ trace (x * conj y)`: the two
descriptions of the symmetric bilinear form of a composition algebra agree. -/
theorem trace_mul_conj (x y : Octonion R) :
    trace (x * conj y) = QuadraticMap.polar (normQuadraticForm R) x y := by
  simp [polar_normQuadraticForm, dotProduct_comm]
  ring

/-- **The polar form of the norm is visible inside the algebra**: `x * conj y + y * conj x` is the
scalar `QuadraticMap.polar (normQuadraticForm R) x y · 1`. Together with
`TauCeti.Octonion.self_mul_conj`, which is the case `y = x` up to a factor of `2`, this is what
makes the symmetric form of a composition algebra an algebraic, not merely a quadratic, datum.

The mirror form `conj x * y + conj y * x` is this identity at `(conj x, conj y)`, read through
`TauCeti.Octonion.conj_conj` and `TauCeti.Octonion.polar_normQuadraticForm_conj`:
`simpa [polar_normQuadraticForm_conj] using mul_conj_add_mul_conj (conj x) (conj y)`. -/
theorem mul_conj_add_mul_conj (x y : Octonion R) :
    x * conj y + y * conj x = QuadraticMap.polar (normQuadraticForm R) x y • 1 := by
  -- `y * conj x` is the conjugate of `x * conj y`, so this is `TauCeti.Octonion.add_conj` at
  -- `x * conj y`, read through the trace form.
  have h : conj (x * conj y) = y * conj x := by rw [conj_mul, conj_conj]
  rw [← h, add_conj, trace_mul_conj]

/-! ### Alternativity -/

/-- **The split octonions are left alternative**: `x * x * y = x * (x * y)`. -/
@[simp, grind =]
theorem left_alternative (x y : Octonion R) : x * x * y = x * (x * y) := by
  -- The iterated cross products of the vector entries are expanded by
  -- `Matrix.cross_cross_eq_smul_sub_smul'`, which is exactly what the repeated dot products of the
  -- scalar entries produce.
  refine Octonion.ext ?_ ?_ ?_ ?_ <;> simp [dotProduct_comm, mul_comm]
  · ring
  · ring
  · module
  · module

/-- **The split octonions are right alternative**: `x * y * y = x * (y * y)`. -/
@[simp, grind =]
theorem right_alternative (x y : Octonion R) : x * y * y = x * (y * y) := by
  -- Left alternativity read through the anti-automorphism `TauCeti.Octonion.conj_mul`.
  have h : conj (conj y * conj y * conj x) = conj (conj y * (conj y * conj x)) :=
    congrArg _ (left_alternative (conj y) (conj x))
  simpa only [conj_mul, conj_conj] using h.symm

end Vector

/-! ### The Moufang identities

The two Moufang identities proved directly are the one place where the vector simp set above does
not suffice. Reducing them with it leaves obligations that hold only because the vector entries have
three coordinates and that Mathlib does not name: the vanishing of `v ⬝ᵥ u ⨯₃ w + w ⬝ᵥ u ⨯₃ v` at
the scalar entries, and a relation between a triple product and the entries themselves at the vector
entries. Both are therefore proved in coordinates: dot
products are expanded by Mathlib's `Matrix.vec3_dotProduct`, cross products by Mathlib's
`Matrix.cross_apply`. The latter rewrites `u ⨯₃ t` to a `![…]` literal, and such a literal meeting
the generic vector entries of a product fires `Matrix.sub_cons`, `Matrix.head_add` and
`Matrix.dotProduct_cons`, which re-express the coordinates as `vecHead`/`vecTail` towers; unfolding
those two definitions turns the towers back into the coordinates `u 0`, `u 1`, `u 2`, so that `ring`
sees one atom per coordinate. -/

section Coordinates

attribute [local simp] vec3_dotProduct cross_apply Matrix.vecHead Matrix.vecTail

/-- **The left Moufang identity**: `(z * x * z) * y = z * (x * (z * y))`. -/
theorem moufang_left (x y z : Octonion R) : z * x * z * y = z * (x * (z * y)) := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- **The flexible law**: `x * y * x = x * (y * x)`, so the two bracketings of `x * y * x` agree. -/
@[grind =]
theorem flexible (x y : Octonion R) : x * y * x = x * (y * x) := by
  -- The left Moufang identity at `y = 1`.
  simpa only [mul_one] using moufang_left y 1 x

/-- **The right Moufang identity**: `x * (z * y * z) = ((x * z) * y) * z`. -/
theorem moufang_right (x y z : Octonion R) : x * (z * y * z) = x * z * y * z := by
  -- The left identity read through the anti-automorphism `TauCeti.Octonion.conj_mul`, after the
  -- flexible law `TauCeti.Octonion.flexible` has put the two brackets of `z * y * z` in the shape
  -- the mirror produces.
  have h : conj (conj z * conj y * conj z * conj x) =
      conj (conj z * (conj y * (conj z * conj x))) :=
    congrArg _ (moufang_left (conj y) (conj x) (conj z))
  rw [flexible z y]
  simpa only [conj_mul, conj_conj] using h

/-- **The middle Moufang identity**: `(z * x) * (y * z) = (z * (x * y)) * z`. -/
theorem moufang_middle (x y z : Octonion R) : z * x * (y * z) = z * (x * y) * z := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

end Coordinates

/-! ### Worked examples: `Octonion ℤ` is neither commutative nor associative

Alternativity is as much associativity as `𝕆` has, and the two vector entries are what break the
rest: `[[0, e₀], [0, 0]] · [[0, e₁], [0, 0]]` picks up the cross product `e₀ ⨯₃ e₁ = e₂` in its
bottom-left entry, and the opposite product picks up `e₁ ⨯₃ e₀ = -e₂`. The two examples below run
this over `ℤ`, so they witness both failures for that base ring rather than for every `R`; over the
zero ring `Octonion R` is of course commutative and associative. -/

example :
    (⟨0, 0, ![1, 0, 0], 0⟩ * ⟨0, 0, ![0, 1, 0], 0⟩ : Octonion ℤ) ≠
      ⟨0, 0, ![0, 1, 0], 0⟩ * ⟨0, 0, ![1, 0, 0], 0⟩ := fun h => by
  have h₂ := congrArg (fun x : Octonion ℤ => x.w 2) h
  -- the bottom-left entries are `e₀ ⨯₃ e₁` and `e₁ ⨯₃ e₀`, so `h₂` reads `(1 : ℤ) = -1`
  simp only [mul_w, smul_zero, add_zero, cross_apply, cons_val_one, cons_val_zero, mul_one,
    mul_zero, zero_sub, sub_zero, Pi.add_apply, Pi.zero_apply, zero_add] at h₂
  exact absurd h₂ (by decide)

example :
    (⟨0, 0, ![1, 0, 0], 0⟩ * ⟨0, 0, 0, ![1, 0, 0]⟩ : Octonion ℤ) * ⟨0, 0, ![0, 1, 0], 0⟩ ≠
      (⟨0, 0, ![1, 0, 0], 0⟩ : Octonion ℤ) *
        (⟨0, 0, 0, ![1, 0, 0]⟩ * ⟨0, 0, ![0, 1, 0], 0⟩) := fun h => by
  have h₁ := congrArg (fun x : Octonion ℤ => x.v 1) h
  -- bracketed on the left the dot product `e₀ ⬝ᵥ e₀ = 1` scales `e₁`; on the right the two cross
  -- products `e₀ ⨯₃ e₁` and `e₀ ⨯₃ (e₀ ⨯₃ e₁)` cancel it, so `h₁` reads `(1 : ℤ) = 0`
  simp only [mul_v, mul_a, mul_b, mul_w, mul_zero, mul_one, dotProduct_cons, head_cons, tail_cons,
    dotProduct_of_isEmpty, add_zero, zero_add, one_smul, zero_smul, smul_zero, Pi.sub_apply,
    Pi.zero_apply, cons_val_zero, cons_val_one] at h₁
  exact absurd h₁ (by decide)

/-! ### The imaginary octonions -/

/-- **The imaginary octonions**, the trace-zero subspace of `𝕆`. It is `7`-dimensional
(`TauCeti.Octonion.finrank_imaginary`); identifying it with the fundamental representation of
`G₂ = Der 𝕆` -- where `Der 𝕆` is `TauCeti.derivationLieAlgebra R (Octonion R)` -- waits on the
count `finrank (Der 𝕆) = 14` and the isomorphism with `LieAlgebra.g₂`, neither of which is proved
here. -/
def imaginary (R : Type*) [CommRing R] : Submodule R (Octonion R) := LinearMap.ker trace

@[simp] theorem mem_imaginary {x : Octonion R} : x ∈ imaginary R ↔ trace x = 0 :=
  LinearMap.mem_ker

/-- **Conjugation negates exactly the imaginary octonions**: `x̄ = -x` if and only if `x` has
vanishing trace. Not a `simp` lemma, because `TauCeti.Octonion.mem_imaginary` already takes its
left-hand side apart. -/
theorem mem_imaginary_iff_conj_eq_neg {x : Octonion R} : x ∈ imaginary R ↔ conj x = -x := by
  simp [Octonion.ext_iff, eq_neg_iff_add_eq_zero, add_comm]

/-- The trace is a surjection onto the base ring: it already is on the scalar diagonal. -/
theorem trace_surjective : Function.Surjective (trace : Octonion R →ₗ[R] R) :=
  fun r => ⟨⟨r, 0, 0, 0⟩, by simp⟩

/-- The imaginary octonions are free on the entries `a`, `v`, `w`: a vanishing trace forces
`b = -a`, so `⟨a, -a, v, w⟩ ↦ (a, v, w)` is an `R`-linear isomorphism. Private: it exists only to
transport the dimension count in `TauCeti.Octonion.finrank_imaginary`. -/
private def imaginaryLinearEquivProd (R : Type*) [CommRing R] :
    imaginary R ≃ₗ[R] R × (Fin 3 → R) × (Fin 3 → R) where
  toFun x := (x.1.a, x.1.v, x.1.w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨⟨p.1, -p.1, p.2.1, p.2.2⟩, by simp⟩
  left_inv x :=
    Subtype.ext (Octonion.ext rfl (neg_eq_iff_add_eq_zero.mpr (mem_imaginary.mp x.2)) rfl rfl)
  right_inv _ := rfl

/-- **The imaginary split octonions are `7`-dimensional**: a vanishing trace pins the second
diagonal entry to `b = -a`, leaving the entries `a`, `v` and `w` free. -/
theorem finrank_imaginary (R : Type*) [CommRing R] [StrongRankCondition R] :
    Module.finrank R (imaginary R) = 7 := by
  rw [(imaginaryLinearEquivProd R).finrank_eq]
  simp

end Octonion

end TauCeti
