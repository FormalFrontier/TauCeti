/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The split octonions

The split octonions over a commutative ring `R` are realized here as **Zorn vector matrices**: an
element is a formal `2 × 2` matrix

`⟨a, b, v, w⟩ = [[a, v], [w, b]]`

with scalar diagonal `a b : R` and vector off-diagonal `v w : Fin 3 → R`, multiplied by

`[[a, v], [w, b]] * [[a', v'], [w', b']] =`
`  [[a * a' + v ⬝ᵥ w', a • v' + b' • v - w ⨯₃ w'], [a' • w + b • w' + v ⨯₃ v', b * b' + w ⬝ᵥ v']]`

using the dot and cross products of `Fin 3 → R`. This is an `8`-dimensional unital, non-associative,
non-commutative `R`-algebra carrying the multiplicative norm `N ⟨a, b, v, w⟩ = a * b - v ⬝ᵥ w`, the
determinant of the vector matrix: it is the split Cayley algebra, the split form of the octonions.

Zorn's model is used rather than a Cayley--Dickson doubling of the split quaternions because the two
produce the same algebra while the vector matrices carry the norm form on their sleeve: `N` is a
determinant, and its multiplicativity reduces to polynomial identities in the eight coordinates of
each factor.

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
* `TauCeti.Octonion.mul_conj` and `TauCeti.Octonion.conj_mul`: `x * x̄ = x̄ * x = N x • 1`.
* `TauCeti.Octonion.norm_mul`: the norm is **multiplicative**, so `𝕆` is a composition algebra.
* `TauCeti.Octonion.mul_self_mul` and `TauCeti.Octonion.mul_mul_self`: `𝕆` is **alternative**.
* `TauCeti.Octonion.moufang_left`, `TauCeti.Octonion.moufang_right` and
  `TauCeti.Octonion.moufang_middle`: the three **Moufang identities**.
* `TauCeti.Octonion.mul_self`: every octonion satisfies its rank-two equation
  `x * x = trace x • x - norm x • 1`.
* `TauCeti.Octonion.finrank_imaginary`: the imaginary octonions, the trace-zero subspace, are
  `7`-dimensional. Identifying them with the fundamental representation of `G₂ = Der 𝕆` waits on
  the derivation algebra, which is not built here.

## Implementation notes

Every identity below is a polynomial identity in the coordinates of its arguments, so the proofs
all run the same way: `TauCeti.Octonion.ext_coords` splits an equation of octonions into its eight
scalar coordinates, the file-local simp set expands the dot and cross products into coordinates,
and `ring` finishes.

The module is `public` but not exposed: consumers work through the projection `simp` lemmas rather
than through any definition body. The three component equivalences `TauCeti.Octonion.equivProd`,
`TauCeti.Octonion.addEquivProd` and `TauCeti.Octonion.linearEquivProd` are the exception, and carry
`@[expose]` because the additive and module structures they transport are the componentwise
operations only definitionally, through those bodies.

The norm is left as a bare map `Octonion R → R`, as the roadmap pins it. Packaging it as a
`QuadraticForm R (Octonion R)` — its polarization is the trace form `x, y ↦ trace (x * conj y)` —
is deferred, together with the derivation algebra `Der 𝕆`.

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
form of extensionality the coordinate computations below use. -/
theorem ext_coords {x y : Octonion R} (ha : x.a = y.a) (hb : x.b = y.b)
    (hv₀ : x.v 0 = y.v 0) (hv₁ : x.v 1 = y.v 1) (hv₂ : x.v 2 = y.v 2)
    (hw₀ : x.w 0 = y.w 0) (hw₁ : x.w 1 = y.w 1) (hw₂ : x.w 2 = y.w 2) : x = y := by
  refine Octonion.ext ha hb (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    exacts [hv₀, hv₁, hv₂]
  · fin_cases i
    exacts [hw₀, hw₁, hw₂]

/-- The components of a vector matrix, as a bijection with the tuple of its four entries. -/
@[simps, expose]
def equivProd (R : Type*) : Octonion R ≃ R × R × (Fin 3 → R) × (Fin 3 → R) where
  toFun x := (x.a, x.b, x.v, x.w)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

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

instance [AddCommGroup R] : AddCommGroup (Octonion R) := by
  apply (equivProd R).injective.addCommGroup <;> intros <;> rfl

/-- The components of a vector matrix, as an additive isomorphism with the tuple of its four
entries. -/
@[simps!, expose]
def addEquivProd (R : Type*) [AddCommGroup R] :
    Octonion R ≃+ R × R × (Fin 3 → R) × (Fin 3 → R) :=
  { equivProd R with map_add' := fun _ _ => rfl }

instance [Monoid S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S (Octonion R) :=
  (addEquivProd R).injective.distribMulAction (addEquivProd R).toAddMonoidHom fun _ _ => rfl

instance [Semiring S] [AddCommGroup R] [Module S R] : Module S (Octonion R) :=
  (addEquivProd R).injective.module _ (addEquivProd R).toAddMonoidHom fun _ _ => rfl

instance [AddCommGroup R] [One R] : AddCommGroupWithOne (Octonion R) where
  __ := (inferInstance : AddCommGroup (Octonion R))
  one := 1

/-- The components of a vector matrix, as an `R`-linear isomorphism with the tuple of its four
entries. -/
@[simps!, expose]
def linearEquivProd (R : Type*) [CommRing R] :
    Octonion R ≃ₗ[R] R × R × (Fin 3 → R) × (Fin 3 → R) :=
  { addEquivProd R with map_smul' := fun _ _ => rfl }

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

/-- The first coordinate of a cross product. -/
private theorem cross_apply_zero (u t : Fin 3 → R) : (u ⨯₃ t) 0 = u 1 * t 2 - u 2 * t 1 := by
  simp [cross_apply]

/-- The second coordinate of a cross product. -/
private theorem cross_apply_one (u t : Fin 3 → R) : (u ⨯₃ t) 1 = u 2 * t 0 - u 0 * t 2 := by
  simp [cross_apply]

/-- The third coordinate of a cross product. -/
private theorem cross_apply_two (u t : Fin 3 → R) : (u ⨯₃ t) 2 = u 0 * t 1 - u 1 * t 0 := by
  simp [cross_apply]

/- Dot products are expanded by Mathlib's `Matrix.vec3_dotProduct`; cross products are expanded one
coordinate at a time by the three lemmas above rather than by `Matrix.cross_apply` itself, because
`cross_apply` rewrites `u ⨯₃ t` to a `![…]` literal, and a literal meeting the generic vector
entries of a product fires `Matrix.sub_cons`, `Matrix.head_add` and `Matrix.dotProduct_cons`, which
re-express the coordinates as `vecHead`/`vecTail` towers that `ring` sees as atoms distinct from
`u 0`, `u 1`, `u 2`. -/
attribute [local simp] vec3_dotProduct cross_apply_zero cross_apply_one cross_apply_two

instance : NonAssocRing (Octonion R) where
  __ := (inferInstance : AddCommGroupWithOne (Octonion R))
  left_distrib x y z := by
    refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  right_distrib x y z := by
    refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  zero_mul x := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_zero x := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  one_mul x := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  mul_one x := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

instance : SMulCommClass R (Octonion R) (Octonion R) where
  smul_comm r x y := by
    refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

instance : IsScalarTower R (Octonion R) (Octonion R) where
  smul_assoc r x y := by
    refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-! ### Conjugation, trace and norm -/

/-- **Octonion conjugation** `⟨a, b, v, w⟩ ↦ ⟨b, a, -v, -w⟩`: it exchanges the two diagonal entries
and negates the two vector entries, so it fixes `1` and negates the imaginary part. -/
def conj : Octonion R →ₗ[R] Octonion R where
  toFun x := ⟨x.b, x.a, -x.v, -x.w⟩
  map_add' _ _ := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring
  map_smul' _ _ := by refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

@[simp] theorem conj_a (x : Octonion R) : (conj x).a = x.b := (rfl)
@[simp] theorem conj_b (x : Octonion R) : (conj x).b = x.a := (rfl)
@[simp] theorem conj_v (x : Octonion R) : (conj x).v = -x.v := (rfl)
@[simp] theorem conj_w (x : Octonion R) : (conj x).w = -x.w := (rfl)

@[simp] theorem conj_conj (x : Octonion R) : conj (conj x) = x := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

@[simp] theorem conj_one : conj (1 : Octonion R) = 1 := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

/-- **Conjugation is an anti-automorphism**: it reverses products. -/
theorem conj_mul_eq (x y : Octonion R) : conj (x * y) = conj y * conj x := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

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
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  ring

/-- Conjugation preserves the trace: it only exchanges the two diagonal entries. Not a `simp`
lemma, for the same reason as `TauCeti.Octonion.trace_one`. -/
theorem trace_conj (x : Octonion R) : trace (conj x) = trace x := by
  simp [add_comm]

/-- **The norm** `⟨a, b, v, w⟩ ↦ a * b - v ⬝ᵥ w` of a vector matrix: the determinant of the matrix,
and the norm form of the composition algebra `𝕆`. -/
def norm (x : Octonion R) : R := x.a * x.b - x.v ⬝ᵥ x.w

theorem norm_def (x : Octonion R) : norm x = x.a * x.b - x.v ⬝ᵥ x.w := (rfl)

@[simp] theorem norm_one : norm (1 : Octonion R) = 1 := by simp [norm_def]

@[simp] theorem norm_zero : norm (0 : Octonion R) = 0 := by simp [norm_def]

@[simp] theorem norm_conj (x : Octonion R) : norm (conj x) = norm x := by
  simp [norm_def]; ring

/-- The norm is a **quadratic** form: rescaling an octonion by `r` rescales its norm by `r ^ 2`. -/
theorem norm_smul (r : R) (x : Octonion R) : norm (r • x) = r ^ 2 * norm x := by
  simp [norm_def]; ring

/-- `x * x̄ = N x • 1`: conjugation inverts an octonion up to its norm. -/
theorem mul_conj (x : Octonion R) : x * conj x = norm x • 1 := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [norm_def] <;> ring

/-- `x̄ * x = N x • 1`, the mirror of `TauCeti.Octonion.mul_conj`. -/
theorem conj_mul (x : Octonion R) : conj x * x = norm x • 1 := by
  simpa using mul_conj (conj x)

/-- **The rank-two equation.** Every split octonion satisfies `x² - trace x · x + N x · 1 = 0`, so
it generates a subalgebra of dimension at most `2`. -/
theorem mul_self (x : Octonion R) : x * x = trace x • x - norm x • 1 := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [norm_def] <;> ring

/-- **The norm of a split octonion is multiplicative**, so `𝕆` is a composition algebra. In
coordinates this is a Binet--Cauchy identity: the cross-product corrections to the vector entries of
a product are exactly what the two dot products of the norm need. -/
theorem norm_mul (x y : Octonion R) : norm (x * y) = norm x * norm y := by
  simp [norm_def]; ring

/-! ### Alternativity -/

/-- **The split octonions are left alternative**: `x * x * y = x * (x * y)`. -/
theorem mul_self_mul (x y : Octonion R) : x * x * y = x * (x * y) := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- **The split octonions are right alternative**: `x * y * y = x * (y * y)`. This is left
alternativity read through the anti-automorphism `TauCeti.Octonion.conj_mul_eq`. -/
theorem mul_mul_self (x y : Octonion R) : x * y * y = x * (y * y) := by
  have h : conj (conj y * conj y * conj x) = conj (conj y * (conj y * conj x)) :=
    congrArg _ (mul_self_mul (conj y) (conj x))
  simpa [conj_mul_eq] using h.symm

/-! ### The Moufang identities -/

/-- **The left Moufang identity**: `(z * x * z) * y = z * (x * (z * y))`. -/
theorem moufang_left (x y z : Octonion R) : z * x * z * y = z * (x * (z * y)) := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- **The right Moufang identity**: `x * (z * y * z) = ((x * z) * y) * z`. -/
theorem moufang_right (x y z : Octonion R) : x * (z * y * z) = x * z * y * z := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- **The middle Moufang identity**: `(z * x) * (y * z) = (z * (x * y)) * z`. -/
theorem moufang_middle (x y z : Octonion R) : z * x * (y * z) = z * (x * y) * z := by
  refine ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp <;> ring

/-! ### Worked examples: `𝕆` is neither commutative nor associative

Alternativity is as much associativity as `𝕆` has, and the two vector entries are what break the
rest: `[[0, e₀], [0, 0]] · [[0, e₁], [0, 0]]` picks up the cross product `e₀ ⨯₃ e₁ = e₂` in its
bottom-left entry, and the opposite product picks up `e₁ ⨯₃ e₀ = -e₂`. -/

example :
    (⟨0, 0, ![1, 0, 0], 0⟩ * ⟨0, 0, ![0, 1, 0], 0⟩ : Octonion ℤ) ≠
      ⟨0, 0, ![0, 1, 0], 0⟩ * ⟨0, 0, ![1, 0, 0], 0⟩ := fun h => by
  have h₂ := congrArg (fun x : Octonion ℤ => x.w 2) h
  -- the bottom-left entries are `e₀ ⨯₃ e₁` and `e₁ ⨯₃ e₀`, so `h₂` reads `(1 : ℤ) = -1`
  simp only [mul_w, smul_zero, add_zero, Pi.add_apply, Pi.zero_apply, cross_apply_two,
    cons_val_zero, cons_val_one, mul_one, mul_zero, sub_zero, zero_add, zero_sub] at h₂
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
`G₂ = Der 𝕆` waits on the derivation algebra, which is not built here. -/
def imaginary (R : Type*) [CommRing R] : Submodule R (Octonion R) := LinearMap.ker trace

@[simp] theorem mem_imaginary {x : Octonion R} : x ∈ imaginary R ↔ x.a + x.b = 0 :=
  LinearMap.mem_ker

/-- The trace is a surjection onto the base ring: it already is on the scalar diagonal. -/
theorem trace_surjective : Function.Surjective (trace : Octonion R →ₗ[R] R) :=
  fun r => ⟨⟨r, 0, 0, 0⟩, by simp⟩

/-- The imaginary octonions are free on the entries `a`, `v`, `w`: a vanishing trace forces
`b = -a`, so `⟨a, -a, v, w⟩ ↦ (a, v, w)` is an `R`-linear isomorphism. -/
def imaginaryLinearEquivProd (R : Type*) [CommRing R] :
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
