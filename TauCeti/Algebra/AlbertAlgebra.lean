/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Octonion

/-!
# The split Albert algebra

The split Albert algebra `H₃(𝕆)` over a commutative ring `R` in which `2` is invertible is the
space of `3 × 3` Hermitian matrices over the split octonions `TauCeti.Octonion R`,

`⟦d, x⟧ = [[d 0, x 2, conj (x 1)], [conj (x 2), d 1, x 0], [x 1, conj (x 0), d 2]]`,

under the symmetrized product `A ∘ B = ½ (A B + B A)`. A Hermitian matrix is recorded here by the
data it consists of — a scalar diagonal `d : Fin 3 → R` and three octonion entries
`x : Fin 3 → Octonion R`, the entry `x i` sitting in position `(i + 1, i + 2)` — rather than as a
`Matrix (Fin 3) (Fin 3) (Octonion R)` cut out by a Hermitian predicate: octonion matrices do not
form a ring (their entries do not associate), so `Matrix.mul` would carry no algebraic structure to
inherit, and the subtype would still have to be given its multiplication by hand.

Carrying out the matrix product `½ (A B + B A)` on that data leaves an expression in the octonion
multiplication and in the symmetric bilinear form of the split-octonion norm. That form is Mathlib's
`β = QuadraticMap.associated (TauCeti.Octonion.normQuadraticForm R)` — half the polar form, and the
scalar `½ (x * conj y + y * conj x)` — so the bilinearity and symmetry the product needs are
Mathlib's. The diagonal of the product is
`d i * e i + β (x (i + 1)) (y (i + 1)) + β (x (i + 2)) (y (i + 2))`, and the entries are
`½ ((d (i + 1) + d (i + 2)) • y i + (e (i + 1) + e (i + 2)) • x i)` corrected by the conjugate of
`½ (x (i + 1) * y (i + 2) + y (i + 1) * x (i + 2))`. That expression *is* the definition below.

The product is commutative, `R`-bilinear, and unital with the identity matrix as its unit, and the
three diagonal idempotents form a complete orthogonal frame. The **Jordan identity**
`(A ∘ B) ∘ A² = A ∘ (B ∘ A²)` — that is, `IsCommJordan (AlbertAlgebra R)` — is **not proved here**;
it is what makes `H₃(𝕆)` an exceptional Jordan algebra rather than merely a commutative one, and it
deserves its own file. The same roadmap unit also pins `finrank_derivationAlbert`
(`finrank (Der H₃(𝕆)) = 52`) and `derivationAlbert_equiv_f4`, which are not proved here either.

Everything is stated over a commutative ring. The invertibility of `2` is genuinely needed: the
symmetrized product of matrices is a halved sum, and over `ℤ` the halved symmetric form of the split
octonion norm is not integral. The two dimension counts additionally ask for a base over which ranks
are well behaved, as `StrongRankCondition` and nothing more.

## Main definitions

* `TauCeti.AlbertAlgebra`: the split Albert algebra over `R`, with its `NonAssocCommRing` and
  `Module R` structure and the `SMulCommClass` and `IsScalarTower` instances that say the product
  is `R`-bilinear.
* `TauCeti.AlbertAlgebra.trace`: the trace `d 0 + d 1 + d 2`, an `R`-linear functional.
* `TauCeti.AlbertAlgebra.traceZero`: the trace-zero subspace `J₀`, the kernel of the trace.
* `TauCeti.AlbertAlgebra.diagIdempotent`: the three diagonal idempotents `E₀`, `E₁`, `E₂`.

## Main results

* `TauCeti.AlbertAlgebra.finrank_eq_twentySeven`: `H₃(𝕆)` is `27`-dimensional.
* `TauCeti.AlbertAlgebra.finrank_traceZero`: the trace-zero subspace is `26`-dimensional.
* the `NonAssocCommRing` instance: the product is `R`-bilinear and commutative, and the identity
  matrix is a two-sided unit. It is `NonAssocCommRing` and not `CommRing` because the product is
  not associative, and it subsumes the `NonUnitalNonAssocCommRing` the roadmap pins.
* `TauCeti.AlbertAlgebra.diagIdempotent_mul_diagIdempotent` and
  `TauCeti.AlbertAlgebra.sum_diagIdempotent`: the diagonal idempotents are orthogonal and sum
  to `1`.

## Implementation notes

The additive and module structures are transported along
`TauCeti.AlbertAlgebra.addEquivProd`, which packages a Hermitian matrix as the pair of its diagonal
and its octonion entries; `TauCeti.AlbertAlgebra.linearEquivProd` upgrades it to an `R`-linear
isomorphism, which is what both dimension counts run through.

The multiplication is deliberately left unexposed: its body does not unfold outside this file, and
a product is read through the projection `simp` lemmas `TauCeti.AlbertAlgebra.mul_diag` and
`TauCeti.AlbertAlgebra.mul_offDiag`, which give its two components.

## References

This builds the split Albert algebra of Layer 8 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` ("the split Albert algebra
`J = H₃(𝕆)` of `3×3` Hermitian split-octonionic matrices under the symmetrized product
`x ∘ y = ½(x y + y x)`, a `27`-dimensional exceptional Jordan algebra"), whose `Suggested.lean` pins
it as `AlbertAlgebra`, `finrank_albertAlgebra`, `albertTrace`, `traceZeroAlbert` and
`finrank_traceZeroAlbert`; those are the declarations below, named inside the `AlbertAlgebra`
namespace, as the split octonions of `TauCeti/Algebra/Octonion.lean` are named inside `Octonion`.
That roadmap's `## Ordering` marks this unit as buildable from scratch at any time, independently of
every other layer. The pinned clauses `isCommJordan_albertAlgebra`, `finrank_derivationAlbert` and
`derivationAlbert_equiv_f4` are not proved here.

The model is P. Jordan, J. von Neumann and E. Wigner, *On an algebraic generalization of the quantum
mechanical formalism*, Ann. of Math. 35 (1934); see also T. A. Springer and F. D. Veldkamp,
*Octonions, Jordan Algebras and Exceptional Groups*, §5.3, and J. C. Baez, *The octonions*, Bull.
Amer. Math. Soc. 39 (2002), §3.4, from which the coordinate form of the product above is taken.
-/

public section

namespace TauCeti

/-- The **split Albert algebra** `H₃(𝕆)` over `R`: a `3 × 3` Hermitian matrix over the split
octonions, recorded as its scalar diagonal together with its three octonion entries. -/
@[ext]
structure AlbertAlgebra (R : Type*) where
  /-- The scalar diagonal of the Hermitian matrix. -/
  diag : Fin 3 → R
  /-- The octonion entries: `offDiag i` is the entry in position `(i + 1, i + 2)`, and the entry in
  position `(i + 2, i + 1)` is its conjugate. -/
  offDiag : Fin 3 → Octonion R

namespace AlbertAlgebra

variable {R S : Type*}

/-! ### The additive and module structure -/

instance [Zero R] : Zero (AlbertAlgebra R) := ⟨0, 0⟩

@[simp] theorem zero_diag [Zero R] : (0 : AlbertAlgebra R).diag = 0 := (rfl)
@[simp] theorem zero_offDiag [Zero R] : (0 : AlbertAlgebra R).offDiag = 0 := (rfl)

instance [Zero R] : Inhabited (AlbertAlgebra R) := ⟨0⟩

instance [Zero R] [One R] : One (AlbertAlgebra R) := ⟨1, 0⟩

@[simp] theorem one_diag [Zero R] [One R] : (1 : AlbertAlgebra R).diag = 1 := (rfl)
@[simp] theorem one_offDiag [Zero R] [One R] : (1 : AlbertAlgebra R).offDiag = 0 := (rfl)

instance [Add R] : Add (AlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag + B.diag, A.offDiag + B.offDiag⟩⟩

@[simp] theorem add_diag [Add R] (A B : AlbertAlgebra R) : (A + B).diag = A.diag + B.diag := (rfl)
@[simp] theorem add_offDiag [Add R] (A B : AlbertAlgebra R) :
    (A + B).offDiag = A.offDiag + B.offDiag := (rfl)

instance [Neg R] : Neg (AlbertAlgebra R) := ⟨fun A => ⟨-A.diag, -A.offDiag⟩⟩

@[simp] theorem neg_diag [Neg R] (A : AlbertAlgebra R) : (-A).diag = -A.diag := (rfl)
@[simp] theorem neg_offDiag [Neg R] (A : AlbertAlgebra R) : (-A).offDiag = -A.offDiag := (rfl)

instance [Sub R] : Sub (AlbertAlgebra R) :=
  ⟨fun A B => ⟨A.diag - B.diag, A.offDiag - B.offDiag⟩⟩

@[simp] theorem sub_diag [Sub R] (A B : AlbertAlgebra R) : (A - B).diag = A.diag - B.diag := (rfl)
@[simp] theorem sub_offDiag [Sub R] (A B : AlbertAlgebra R) :
    (A - B).offDiag = A.offDiag - B.offDiag := (rfl)

instance [SMul S R] : SMul S (AlbertAlgebra R) :=
  ⟨fun s A => ⟨s • A.diag, s • A.offDiag⟩⟩

@[simp] theorem smul_diag [SMul S R] (s : S) (A : AlbertAlgebra R) :
    (s • A).diag = s • A.diag := (rfl)

@[simp] theorem smul_offDiag [SMul S R] (s : S) (A : AlbertAlgebra R) :
    (s • A).offDiag = s • A.offDiag := (rfl)

/-- The components of a Hermitian matrix, as an additive isomorphism with the pair of its scalar
diagonal and its octonion entries. The additive and module structures are transported along it, and
`TauCeti.AlbertAlgebra.linearEquivProd` upgrades it to an `R`-linear isomorphism. -/
def addEquivProd (R : Type*) [Add R] :
    AlbertAlgebra R ≃+ (Fin 3 → R) × (Fin 3 → Octonion R) where
  toFun A := (A.diag, A.offDiag)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem addEquivProd_apply [Add R] (A : AlbertAlgebra R) :
    addEquivProd R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem addEquivProd_symm_apply [Add R] (p : (Fin 3 → R) × (Fin 3 → Octonion R)) :
    (addEquivProd R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance [AddCommGroup R] : AddCommGroup (AlbertAlgebra R) := by
  apply (addEquivProd R).injective.addCommGroup <;> intros <;> simp

instance [Monoid S] [AddCommGroup R] [DistribMulAction S R] :
    DistribMulAction S (AlbertAlgebra R) :=
  (addEquivProd R).injective.distribMulAction (addEquivProd R).toAddMonoidHom fun _ _ => by simp

instance [Semiring S] [AddCommGroup R] [Module S R] : Module S (AlbertAlgebra R) :=
  (addEquivProd R).injective.module _ (addEquivProd R).toAddMonoidHom fun _ _ => by simp

instance [AddCommGroup R] [One R] : AddCommGroupWithOne (AlbertAlgebra R) where
  __ := (inferInstance : AddCommGroup (AlbertAlgebra R))
  one := 1

/-- The components of a Hermitian matrix, as an `R`-linear isomorphism with the pair of its scalar
diagonal and its octonion entries. -/
def linearEquivProd (R : Type*) [CommRing R] :
    AlbertAlgebra R ≃ₗ[R] (Fin 3 → R) × (Fin 3 → Octonion R) :=
  { addEquivProd R with map_smul' := fun _ _ => rfl }

@[simp] theorem linearEquivProd_apply [CommRing R] (A : AlbertAlgebra R) :
    linearEquivProd R A = (A.diag, A.offDiag) := (rfl)

@[simp] theorem linearEquivProd_symm_apply [CommRing R] (p : (Fin 3 → R) × (Fin 3 → Octonion R)) :
    (linearEquivProd R).symm p = ⟨p.1, p.2⟩ := (rfl)

instance [CommRing R] : Module.Free R (AlbertAlgebra R) :=
  Module.Free.of_equiv (linearEquivProd R).symm

instance [CommRing R] : Module.Finite R (AlbertAlgebra R) :=
  Module.Finite.equiv (linearEquivProd R).symm

/-- **The split Albert algebra is `27`-dimensional**: three scalars on the diagonal and three
`8`-dimensional octonion entries. -/
theorem finrank_eq_twentySeven (R : Type*) [CommRing R] [StrongRankCondition R] :
    Module.finrank R (AlbertAlgebra R) = 27 := by
  rw [(linearEquivProd R).finrank_eq, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_pi_fintype, Finset.sum_const]
  simp [Octonion.finrank_eq_eight]

/-! ### The symmetrized product -/

variable [CommRing R]

/-- The symmetrized matrix product `A ∘ B = ½ (A B + B A)`, written out on the diagonal and on the
octonion entries of a Hermitian matrix. The symmetric bilinear form associated with the octonion
norm — Mathlib's `QuadraticMap.associated`, half the polar form — enters on the diagonal, and the
conjugate of a symmetrized octonion product off it. -/
instance [Invertible (2 : R)] : Mul (AlbertAlgebra R) :=
  ⟨fun A B =>
    ⟨fun i => A.diag i * B.diag i
        + QuadraticMap.associated (Octonion.normQuadraticForm R)
            (A.offDiag (i + 1)) (B.offDiag (i + 1))
        + QuadraticMap.associated (Octonion.normQuadraticForm R)
            (A.offDiag (i + 2)) (B.offDiag (i + 2)),
      fun i =>
        ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
            + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i)
          + Octonion.conj
              (⅟(2 : R) • (A.offDiag (i + 1) * B.offDiag (i + 2)
                + B.offDiag (i + 1) * A.offDiag (i + 2)))⟩⟩

@[simp] theorem mul_diag [Invertible (2 : R)] (A B : AlbertAlgebra R) (i : Fin 3) :
    (A * B).diag i = A.diag i * B.diag i
      + QuadraticMap.associated (Octonion.normQuadraticForm R)
          (A.offDiag (i + 1)) (B.offDiag (i + 1))
      + QuadraticMap.associated (Octonion.normQuadraticForm R)
          (A.offDiag (i + 2)) (B.offDiag (i + 2)) :=
  (rfl)

@[simp] theorem mul_offDiag [Invertible (2 : R)] (A B : AlbertAlgebra R) (i : Fin 3) :
    (A * B).offDiag i =
      ⅟(2 : R) • ((A.diag (i + 1) + A.diag (i + 2)) • B.offDiag i
          + (B.diag (i + 1) + B.diag (i + 2)) • A.offDiag i)
        + Octonion.conj
            (⅟(2 : R) • (A.offDiag (i + 1) * B.offDiag (i + 2)
              + B.offDiag (i + 1) * A.offDiag (i + 2))) :=
  (rfl)

section Product

variable [Invertible (2 : R)]

instance : NonAssocCommRing (AlbertAlgebra R) where
  __ := (inferInstance : AddCommGroupWithOne (AlbertAlgebra R))
  left_distrib A B C := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add]
      abel
    · simp [mul_add, add_mul, smul_add]
      module
  right_distrib A B C := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [add_mul]
      abel
    · simp [mul_add, add_mul, smul_add]
      module
  zero_mul A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_zero A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  mul_comm A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [QuadraticMap.associated_isSymm R (Octonion.normQuadraticForm R) (B.offDiag _), mul_comm]
    · simp
      module
  one_mul A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]
  mul_one A := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp
    · simp [one_add_one_eq_two, smul_smul]

instance : SMulCommClass R (AlbertAlgebra R) (AlbertAlgebra R) where
  smul_comm r A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add, mul_left_comm]
    · simp [mul_smul_comm, smul_mul_assoc]
      module

instance : IsScalarTower R (AlbertAlgebra R) (AlbertAlgebra R) where
  smul_assoc r A B := by
    refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [mul_add, mul_assoc]
    · simp [mul_smul_comm, smul_mul_assoc]
      module

end Product

/-! ### The trace -/

/-- **The trace** of a Hermitian octonion matrix: the sum of its three scalar diagonal entries. -/
def trace : AlbertAlgebra R →ₗ[R] R where
  toFun A := ∑ i, A.diag i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

@[simp] theorem trace_apply (A : AlbertAlgebra R) : trace A = ∑ i, A.diag i := (rfl)

/-- The trace of the identity matrix is `3`, one for each diagonal entry. Not a `simp` lemma,
because `TauCeti.AlbertAlgebra.trace_apply` already takes its left-hand side apart. -/
theorem trace_one : trace (1 : AlbertAlgebra R) = 3 := by
  simp

/-- The trace is a surjection onto the base ring: it already is on the first diagonal entry. -/
theorem trace_surjective : Function.Surjective (trace : AlbertAlgebra R →ₗ[R] R) :=
  fun r => ⟨⟨![r, 0, 0], 0⟩, by simp [Fin.sum_univ_three]⟩

/-- **The trace-zero subspace** `J₀ ⊆ H₃(𝕆)`, the kernel of the trace. Over a base ring satisfying
`StrongRankCondition` it is `26`-dimensional (`TauCeti.AlbertAlgebra.finrank_traceZero`). Reading it
as the fundamental representation of `F₄ = Der H₃(𝕆)` -- where `Der H₃(𝕆)` is
`TauCeti.derivationLieAlgebra R (AlbertAlgebra R)` -- is a further step that is not taken here, and
it is not available over an arbitrary `R`: it needs `3` invertible, since otherwise `trace 1 = 3`
vanishes, `J₀` contains the identity and so is not a complement of the scalars. Even over such an
`R` it waits on the count `finrank (Der H₃(𝕆)) = 52` and the isomorphism with `LieAlgebra.f₄`,
neither of which is proved here. -/
def traceZero (R : Type*) [CommRing R] : Submodule R (AlbertAlgebra R) := LinearMap.ker trace

@[simp] theorem mem_traceZero {A : AlbertAlgebra R} : A ∈ traceZero R ↔ trace A = 0 :=
  LinearMap.mem_ker

/-- The trace-zero matrices are free on the first two diagonal entries and the three octonion
entries: a vanishing trace forces the last diagonal entry. Private: it exists only to transport the
dimension count in `TauCeti.AlbertAlgebra.finrank_traceZero`. -/
private def traceZeroLinearEquivProd (R : Type*) [CommRing R] :
    traceZero R ≃ₗ[R] (R × R) × (Fin 3 → Octonion R) where
  toFun A := ((A.1.diag 0, A.1.diag 1), A.1.offDiag)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨⟨![p.1.1, p.1.2, -(p.1.1 + p.1.2)], p.2⟩, by simp [Fin.sum_univ_three]⟩
  left_inv A := by
    have h : (A : AlbertAlgebra R).diag 2
        = -((A : AlbertAlgebra R).diag 0 + (A : AlbertAlgebra R).diag 1) := by
      have h0 : (A : AlbertAlgebra R).diag 0 + (A : AlbertAlgebra R).diag 1
          + (A : AlbertAlgebra R).diag 2 = 0 := by
        simpa [Fin.sum_univ_three] using mem_traceZero.mp A.2
      exact eq_neg_of_add_eq_zero_right h0
    refine Subtype.ext (AlbertAlgebra.ext (funext fun i => ?_) rfl)
    fin_cases i <;> simp [h]
  right_inv _ := rfl

/-- **The trace-zero subspace of the split Albert algebra is `26`-dimensional**: a vanishing trace
pins the last diagonal entry to the negative of the sum of the other two. -/
theorem finrank_traceZero (R : Type*) [CommRing R] [StrongRankCondition R] :
    Module.finrank R (traceZero R) = 26 := by
  rw [(traceZeroLinearEquivProd R).finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_pi_fintype, Finset.sum_const]
  simp [Octonion.finrank_eq_eight]

/-! ### The diagonal frame of idempotents -/

/-- The `i`-th **diagonal idempotent** `Eᵢ` of `H₃(𝕆)`: the Hermitian matrix with a single `1` in
position `(i, i)`. -/
def diagIdempotent (R : Type*) [Zero R] [One R] (i : Fin 3) : AlbertAlgebra R := ⟨Pi.single i 1, 0⟩

@[simp] theorem diagIdempotent_diag (i : Fin 3) : (diagIdempotent R i).diag = Pi.single i 1 := (rfl)
@[simp] theorem diagIdempotent_offDiag (i : Fin 3) : (diagIdempotent R i).offDiag = 0 := (rfl)

/-- **The diagonal idempotents are orthogonal**: `Eᵢ ∘ Eⱼ` is `Eᵢ` when `i = j` and `0`
otherwise. -/
@[simp] theorem diagIdempotent_mul_diagIdempotent [Invertible (2 : R)] (i j : Fin 3) :
    diagIdempotent R i * diagIdempotent R j = if i = j then diagIdempotent R i else 0 := by
  rcases eq_or_ne i j with rfl | h
  · refine AlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases eq_or_ne k i with rfl | hk
      · simp
      · simp [hk]
    · simp
  · refine AlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
    · by_cases hk : k = i <;> simp [Pi.single_apply, hk, h]
    · simp [h]

/-- The diagonal idempotents add up to the identity matrix. -/
@[simp] theorem sum_diagIdempotent : ∑ i, diagIdempotent R i = 1 := by
  refine AlbertAlgebra.ext (funext fun k => ?_) (funext fun k => ?_)
  · fin_cases k <;> simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]

/-- Each diagonal idempotent has trace `1`, so the frame accounts for the whole trace of the
identity. Not a `simp` lemma: `TauCeti.AlbertAlgebra.trace_apply` already takes its left-hand side
apart, and `simp` proves it outright. -/
theorem trace_diagIdempotent (i : Fin 3) : trace (diagIdempotent R i) = 1 := by
  simp [Pi.single_apply]

end AlbertAlgebra

end TauCeti
