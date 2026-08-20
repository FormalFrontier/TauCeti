/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# The dynamic parabolic, unipotent and Levi subgroups of a cocharacter

Let `H` be a Hopf algebra over `R`, so that `Spec H` is an affine group scheme `G`, and let
`l : H →ₐc[R] R[T;T⁻¹]` be a **cocharacter**, that is, a homomorphism of group schemes `𝔾ₘ → G`
written contravariantly on coordinate rings. The *dynamic method* attaches to `l` three subgroups
of the convolution group `G(A) = H →ₐ[R] A` of `A`-points, for every commutative `R`-algebra `A`,
using only limits of one-parameter conjugation and no root data:

* the **parabolic** `P(l)(A)`: the points `g` for which `t ↦ l(t) · g · l(t)⁻¹` extends over
  `t = 0`;
* the **Levi** `Z(l)(A)`: the points centralized by `l`;
* the **unipotent** subgroup `U(l)(A)`: the points whose limit at `t = 0` is the identity.

Everything is phrased on the functor of points, which is where these conditions are honest: the
conjugate of `g` by the *generic* point `l(T)` is a point of `G` with values in the Laurent
polynomial ring `A[T;T⁻¹]`, and `g` lies in `P(l)(A)` exactly when that conjugate lies in the
image of the points with values in `A[X]`. Since `A[X] → A[T;T⁻¹]` is injective the extension is
unique, so extending and then evaluating at `X = 0` is a group homomorphism
`limit : P(l)(A) → G(A)`, whose kernel is `U(l)(A)`.

The main theorem is the **Levi decomposition on points**: `limit` takes values in `Z(l)(A)` and
restricts to the identity there, so it is a retraction of `P(l)(A)` onto `Z(l)(A)`. Consequently
`U(l)(A)` and `Z(l)(A)` generate `P(l)(A)`, meet trivially, and the resulting factorization is
unique; `U(l)(A)` is moreover normalized by `P(l)(A)`. That `limit g` is centralized by `l` is
the generic identity `l(T) · F(X) · l(T)⁻¹ = F(T · X)` over `A[X][T;T⁻¹]`, proved by comparing
two substitutions inside `A[T;T⁻¹][T';T'⁻¹]`, where the cocycle relation
`l(T · T') = l(T) · l(T')` is available; specializing that identity at `X = 0` gives the
statement.

All three subgroups are preserved by change of value algebra, so they are subgroup functors of
the functor of points, and `limit` is natural. Representability of these subfunctors by closed
subschemes is not addressed here. For a commutative affine group the whole construction
degenerates: `P(l)` and `Z(l)` are everything and `U(l)` is trivial.

## Main declarations

* `TauCeti.Cocharacter.pointsHom`: a cocharacter read on points, `𝔾ₘ(A) = Aˣ → G(A)`.
* `TauCeti.Cocharacter.conjugate`: conjugation by the generic point `l(T)`.
* `TauCeti.Cocharacter.parabolic`, `TauCeti.Cocharacter.levi` and
  `TauCeti.Cocharacter.unipotent`: the three dynamic subgroups.
* `TauCeti.Cocharacter.limit`: the limit homomorphism `P(l)(A) → G(A)`.
* `TauCeti.Cocharacter.limit_of_mem_levi` and `TauCeti.Cocharacter.limit_mem_levi`: the limit is
  a retraction of the dynamic parabolic onto its Levi subgroup.
* `TauCeti.Cocharacter.unipotent_sup_levi`, `TauCeti.Cocharacter.unipotent_inf_levi`,
  `TauCeti.Cocharacter.conj_mem_unipotent` and
  `TauCeti.Cocharacter.eq_of_unipotent_mul_levi_eq`: the Levi decomposition.
* `TauCeti.Cocharacter.parabolic_le_comap`, `TauCeti.Cocharacter.levi_le_comap` and
  `TauCeti.Cocharacter.unipotent_le_comap`: the three subgroups are subgroup functors.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This is the "dynamic" route to parabolic, Levi and unipotent subgroups asked for in Layer 7,
"Structure theory", of the ReductiveGroups roadmap, which keeps it as a parallel route that
avoids full root data.
-/

public section

open WithConv

namespace TauCeti

namespace Cocharacter

variable {R H A B : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

/-! ### Auxiliary lemmas -/

private theorem conj_conj {G : Type*} [Group G] (a b x : G) :
    a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ := by
  rw [mul_inv_rev]
  simp only [mul_assoc]

private theorem mapAlgHom_C {C : Type*} [CommSemiring C] [Algebra R C] (φ : A →ₐ[R] C) (a : A) :
    (AddMonoidAlgebra.mapAlgHom ℤ φ) (LaurentPolynomial.C a) = LaurentPolynomial.C (φ a) :=
  AddMonoidAlgebra.mapAlgHom_single φ (0 : ℤ) a

private theorem mapAlgHom_T {C : Type*} [CommSemiring C] [Algebra R C] (φ : A →ₐ[R] C) (n : ℤ) :
    (AddMonoidAlgebra.mapAlgHom ℤ φ) (LaurentPolynomial.T n) = LaurentPolynomial.T n :=
  (AddMonoidAlgebra.mapAlgHom_single φ n 1).trans (by rw [map_one]; rfl)

private theorem mapAlgHom_comp_const {C : Type*} [CommSemiring C] [Algebra R C] (φ : A →ₐ[R] C) :
    (AddMonoidAlgebra.mapAlgHom ℤ φ).comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      (IsScalarTower.toAlgHom R C (LaurentPolynomial C)).comp φ :=
  AlgHom.ext fun a => AddMonoidAlgebra.mapAlgHom_single φ (0 : ℤ) a

/-! ### Points over the line and the punctured line -/

variable (A) in
/-- The constant-point inclusion `G(A) → G(A[T;T⁻¹])`, pullback of points along the structure
map `A → A[T;T⁻¹]`. -/
noncomputable def constPoint :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom R A (LaurentPolynomial A))

variable (A) in
/-- The constant-point inclusion `G(A) → G(A[X])`, pullback of points along `A → A[X]`. -/
noncomputable def constPolyPoint :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] Polynomial A) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom R A (Polynomial A))

variable (A) in
/-- The inclusion `G(A[X]) → G(A[T;T⁻¹])` of points over the affine line into points over the
punctured affine line, pullback along `Polynomial.toLaurent`. -/
noncomputable def ofPolyPoint :
    WithConv (H →ₐ[R] Polynomial A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  AlgHom.mapValue (Polynomial.toLaurentAlg.restrictScalars R)

variable (A) in
/-- Evaluation at the origin, `G(A[X]) → G(A)`. -/
noncomputable def evalZeroPoint :
    WithConv (H →ₐ[R] Polynomial A) →* WithConv (H →ₐ[R] A) :=
  AlgHom.mapValue ((Polynomial.aeval (0 : A)).restrictScalars R)

variable (A) in
/-- The constant-point inclusion post-composes a point with the structure map `A → A[T;T⁻¹]`. -/
theorem constPoint_apply (g : WithConv (H →ₐ[R] A)) :
    constPoint A g = toConv ((IsScalarTower.toAlgHom R A (LaurentPolynomial A)).comp g.ofConv) := by
  rw [constPoint, AlgHom.mapValue_apply]

variable (A) in
/-- The constant-point inclusion post-composes a point with the structure map `A → A[X]`. -/
theorem constPolyPoint_apply (g : WithConv (H →ₐ[R] A)) :
    constPolyPoint A g = toConv ((IsScalarTower.toAlgHom R A (Polynomial A)).comp g.ofConv) := by
  rw [constPolyPoint, AlgHom.mapValue_apply]

variable (A) in
/-- The inclusion of points over the affine line post-composes with `Polynomial.toLaurent`. -/
theorem ofPolyPoint_apply (F : WithConv (H →ₐ[R] Polynomial A)) :
    ofPolyPoint A F = toConv ((Polynomial.toLaurentAlg.restrictScalars R).comp F.ofConv) := by
  rw [ofPolyPoint, AlgHom.mapValue_apply]

variable (A) in
/-- Evaluation at the origin post-composes a point over `A[X]` with `X ↦ 0`. -/
theorem evalZeroPoint_apply (F : WithConv (H →ₐ[R] Polynomial A)) :
    evalZeroPoint A F = toConv (((Polynomial.aeval (0 : A)).restrictScalars R).comp F.ofConv) := by
  rw [evalZeroPoint, AlgHom.mapValue_apply]

variable (A) in
/-- A point over `A[X]` is determined by the point over `A[T;T⁻¹]` that it induces. -/
theorem ofPolyPoint_injective :
    Function.Injective (ofPolyPoint (R := R) (H := H) A) :=
  AlgHom.mapValue_injective Polynomial.toLaurent_injective

variable (A) in
/-- A constant point over `A[X]` induces the constant point over `A[T;T⁻¹]`. -/
@[simp]
theorem ofPolyPoint_constPolyPoint (g : WithConv (H →ₐ[R] A)) :
    ofPolyPoint A (constPolyPoint A g) = constPoint A g := by
  have h : (Polynomial.toLaurentAlg.restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (Polynomial A)) =
      IsScalarTower.toAlgHom R A (LaurentPolynomial A) := by ext a; simp
  rw [ofPolyPoint, constPolyPoint, constPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, h]

variable (A) in
/-- A constant point over `A[X]` evaluates at the origin to the point it came from. -/
@[simp]
theorem evalZeroPoint_constPolyPoint (g : WithConv (H →ₐ[R] A)) :
    evalZeroPoint A (constPolyPoint A g) = g := by
  have h : ((Polynomial.aeval (0 : A)).restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (Polynomial A)) = AlgHom.id R A := by ext a; simp
  rw [evalZeroPoint, constPolyPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, h,
    AlgHom.mapValue_id, MonoidHom.id_apply]

/-! ### The generic point of a cocharacter and conjugation by it -/

variable (A) in
/-- The Laurent variable `T`, as a unit of `A[T;T⁻¹]`. It is the tautological `A[T;T⁻¹]`-point of
the multiplicative group. -/
noncomputable def genericUnit : (LaurentPolynomial A)ˣ :=
  unitOfInvertible (LaurentPolynomial.T 1)

/-- The generic unit is the Laurent variable `T`. -/
@[simp]
theorem genericUnit_val : (genericUnit A : LaurentPolynomial A) = LaurentPolynomial.T 1 := by
  simp [genericUnit]

variable (A) in
/-- **A cocharacter on points**: the group homomorphism `𝔾ₘ(A) = Aˣ → G(A)` obtained from a
cocharacter `l : 𝔾ₘ → G`, presented contravariantly as a bialgebra homomorphism
`H →ₐc[R] R[T;T⁻¹]`. -/
noncomputable def pointsHom (l : H →ₐc[R] LaurentPolynomial R) :
    Aˣ →* WithConv (H →ₐ[R] A) :=
  (AlgHom.mapDomain l).comp
    (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm.toMonoidHom

/-- A cocharacter sends a unit to the corresponding `𝔾ₘ`-point precomposed with `l`. -/
theorem pointsHom_apply (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    pointsHom A l u = AlgHom.mapDomain l (toConv (MultiplicativeGroup.point (R := R) u)) := by
  rw [pointsHom, MonoidHom.comp_apply]
  congr 1

/-- Values of a cocharacter commute with one another: they lie in the image of the commutative
group `𝔾ₘ(A)`. -/
theorem pointsHom_commute (l : H →ₐc[R] LaurentPolynomial R) (u v : Aˣ) :
    Commute (pointsHom A l u) (pointsHom A l v) :=
  (Commute.all u v).map (pointsHom A l)

variable (A) in
/-- The point `l(T)` of the affine group `Spec H` with values in `A[T;T⁻¹]`: the cocharacter `l`
evaluated at the tautological point `T` of the multiplicative group. -/
noncomputable def genericPoint (l : H →ₐc[R] LaurentPolynomial R) :
    WithConv (H →ₐ[R] LaurentPolynomial A) :=
  pointsHom (LaurentPolynomial A) l (genericUnit A)

/-- The generic point is the value of the cocharacter at the generic unit `T`. -/
theorem genericPoint_eq_pointsHom (l : H →ₐc[R] LaurentPolynomial R) :
    genericPoint A l = pointsHom (LaurentPolynomial A) l (genericUnit A) := by
  rw [genericPoint]

variable (A) in
/-- **Conjugation by the generic point of a cocharacter**: the group homomorphism
`G(A) → G(A[T;T⁻¹])` sending an `A`-point `g` to `l(T) · g · l(T)⁻¹`. -/
noncomputable def conjugate (l : H →ₐc[R] LaurentPolynomial R) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  (MulAut.conj (genericPoint A l)).toMonoidHom.comp (constPoint A)

/-- Conjugation by the generic point acts as `g ↦ l(T) · g · l(T)⁻¹`. -/
@[simp]
theorem conjugate_apply (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] A)) :
    conjugate A l g = genericPoint A l * constPoint A g * (genericPoint A l)⁻¹ := by
  rw [conjugate, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-! ### Naturality in the value algebra -/

section Naturality

variable (φ : A →ₐ[R] B) (l : H →ₐc[R] LaurentPolynomial R)

/-- Change of value algebra commutes with change of source Hopf algebra on points. -/
theorem mapValue_mapDomain (x : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    AlgHom.mapValue φ (AlgHom.mapDomain l x) = AlgHom.mapDomain l (AlgHom.mapValue φ x) :=
  rfl

/-- A cocharacter, read on points, is natural in the value algebra. -/
theorem mapValue_pointsHom (u : Aˣ) :
    AlgHom.mapValue φ (pointsHom A l u) = pointsHom B l (Units.map φ.toMonoidHom u) := by
  rw [pointsHom_apply, pointsHom_apply, mapValue_mapDomain]
  congr 1
  rw [AlgHom.mapValue_apply, MultiplicativeGroup.comp_point]

/-- The induced map on Laurent coefficient algebras fixes the Laurent variable. -/
theorem map_genericUnit :
    Units.map (AddMonoidAlgebra.mapAlgHom ℤ φ).toMonoidHom (genericUnit A) = genericUnit B :=
  Units.ext ((AddMonoidAlgebra.mapAlgHom_single φ (1 : ℤ) 1).trans (by rw [map_one]; rfl))

/-- The constant-point inclusion is natural in the value algebra. -/
theorem mapValue_constPoint (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (constPoint A g) =
      constPoint B (AlgHom.mapValue φ g) := by
  rw [constPoint, constPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp,
    mapAlgHom_comp_const, AlgHom.mapValue_comp, MonoidHom.comp_apply]

/-- The generic point of a cocharacter is natural in the value algebra. -/
theorem mapValue_genericPoint :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (genericPoint A l) = genericPoint B l := by
  rw [genericPoint, genericPoint, mapValue_pointsHom, map_genericUnit]

/-- **Conjugation by the generic point, pushed forward along an arbitrary homomorphism `ψ` out of
`A[T;T⁻¹]`**: it becomes conjugation by the value of the cocharacter at the image of `T`. -/
theorem mapValue_conjugate {C : Type*} [CommSemiring C] [Algebra R C]
    (ψ : LaurentPolynomial A →ₐ[R] C) (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue ψ (conjugate A l g) =
      pointsHom C l (Units.map ψ.toMonoidHom (genericUnit A)) *
        AlgHom.mapValue (ψ.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A))) g *
        (pointsHom C l (Units.map ψ.toMonoidHom (genericUnit A)))⁻¹ := by
  rw [conjugate_apply, map_mul, map_mul, map_inv, genericPoint, mapValue_pointsHom, constPoint,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

/-- **Conjugation by the generic point is natural in the value algebra.** -/
theorem mapValue_conjugate_mapAlgHom (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (conjugate A l g) =
      conjugate B l (AlgHom.mapValue φ g) := by
  rw [mapValue_conjugate, map_genericUnit, conjugate_apply, genericPoint,
    mapAlgHom_comp_const, AlgHom.mapValue_comp, MonoidHom.comp_apply, constPoint]

end Naturality

/-! ### The dynamic parabolic and its limit homomorphism -/

variable (A) in
/-- **The dynamic parabolic subgroup `P(l)(A)`**: the `A`-points `g` of the affine group such
that the conjugate `l(T) · g · l(T)⁻¹` extends over the origin, that is, lies in the image of
the `A[X]`-points. Geometrically, these are the points for which `lim_{t → 0} l(t) g l(t)⁻¹`
exists. -/
noncomputable def parabolic (l : H →ₐc[R] LaurentPolynomial R) :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  (ofPolyPoint A).range.comap (conjugate A l)

variable {l : H →ₐc[R] LaurentPolynomial R}

/-- Membership in the dynamic parabolic is the existence of an extension over the origin. -/
theorem mem_parabolic_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ parabolic A l ↔ ∃ F : WithConv (H →ₐ[R] Polynomial A), ofPolyPoint A F = conjugate A l g :=
  Iff.rfl

/-- An extension over the origin exhibits membership in the dynamic parabolic. -/
theorem mem_parabolic_of_eq {g : WithConv (H →ₐ[R] A)} {F : WithConv (H →ₐ[R] Polynomial A)}
    (hF : ofPolyPoint A F = conjugate A l g) : g ∈ parabolic A l :=
  ⟨F, hF⟩

variable (A l) in
/-- The unique `A[X]`-point extending the conjugate of a point of the dynamic parabolic. -/
noncomputable def extend : parabolic A l →* WithConv (H →ₐ[R] Polynomial A) :=
  (MonoidHom.ofInjective (ofPolyPoint_injective (R := R) (H := H) A)).symm.toMonoidHom.comp
    (MonoidHom.codRestrict ((conjugate A l).comp (parabolic A l).subtype) _ fun g => g.2)

/-- The chosen extension does induce the conjugate it extends. -/
@[simp]
theorem ofPolyPoint_extend (g : parabolic A l) :
    ofPolyPoint A (extend A l g) = conjugate A l (g : WithConv (H →ₐ[R] A)) := by
  have := (MonoidHom.ofInjective (ofPolyPoint_injective (R := R) (H := H) A)).apply_symm_apply
    (⟨conjugate A l (g : WithConv (H →ₐ[R] A)), g.2⟩ : (ofPolyPoint A).range)
  exact congrArg Subtype.val this

/-- The extension over the origin is unique. -/
theorem extend_unique {g : parabolic A l} {F : WithConv (H →ₐ[R] Polynomial A)}
    (hF : ofPolyPoint A F = conjugate A l (g : WithConv (H →ₐ[R] A))) : extend A l g = F :=
  ofPolyPoint_injective A (by rw [ofPolyPoint_extend, hF])

variable (A l) in
/-- **The limit homomorphism** `P(l)(A) → G(A)`, `g ↦ lim_{t → 0} l(t) g l(t)⁻¹`. It is a group
homomorphism because it is the composite of two group homomorphisms: extension over the origin
and evaluation there. -/
noncomputable def limit : parabolic A l →* WithConv (H →ₐ[R] A) :=
  (evalZeroPoint A).comp (extend A l)

/-- The limit is the extension over the origin, evaluated there. -/
theorem limit_apply (g : parabolic A l) : limit A l g = evalZeroPoint A (extend A l g) := by
  rw [limit, MonoidHom.comp_apply]

/-! ### The Levi and unipotent parts -/

variable (A) in
/-- **The dynamic Levi subgroup `Z(l)(A)`**: the `A`-points centralized by the cocharacter, that
is, those fixed by conjugation by the generic point `l(T)`. -/
noncomputable def levi (l : H →ₐc[R] LaurentPolynomial R) :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  MonoidHom.eqLocus (conjugate A l) (constPoint A)

/-- Membership in the Levi subgroup means being fixed by conjugation by `l(T)`. -/
theorem mem_levi_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ levi A l ↔ conjugate A l g = constPoint A g :=
  Iff.rfl

/-- The Levi subgroup is contained in the dynamic parabolic: a fixed point extends by a
constant. -/
theorem levi_le_parabolic : levi A l ≤ parabolic A l := fun g hg =>
  mem_parabolic_of_eq (F := constPolyPoint A g) <| by
    rw [ofPolyPoint_constPolyPoint]
    exact (mem_levi_iff.mp hg).symm

/-- The extension of a point of the Levi subgroup is the constant point. -/
theorem extend_of_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ levi A l) :
    extend A l ⟨g, levi_le_parabolic hg⟩ = constPolyPoint A g :=
  extend_unique <| by
    rw [ofPolyPoint_constPolyPoint]
    exact (mem_levi_iff.mp hg).symm

/-- The limit homomorphism restricts to the identity on the Levi subgroup: it is a retraction of
the dynamic parabolic onto its Levi part. -/
theorem limit_of_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ levi A l) :
    limit A l ⟨g, levi_le_parabolic hg⟩ = g := by
  rw [limit_apply, extend_of_mem_levi hg, evalZeroPoint_constPolyPoint]

variable (A l) in
/-- **The dynamic unipotent subgroup `U(l)(A)`**: the points of the dynamic parabolic whose limit
is the identity. It is the kernel of the limit homomorphism, hence normal in `P(l)(A)`. -/
noncomputable def unipotent : Subgroup (WithConv (H →ₐ[R] A)) :=
  (limit A l).ker.map (parabolic A l).subtype

/-- Membership in the dynamic unipotent subgroup means lying in the parabolic with trivial
limit. -/
theorem mem_unipotent_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ unipotent A l ↔ ∃ hg : g ∈ parabolic A l, limit A l ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

/-- The dynamic unipotent subgroup is contained in the dynamic parabolic. -/
theorem unipotent_le_parabolic : unipotent A l ≤ parabolic A l :=
  Subgroup.map_subtype_le _

/-- The dynamic unipotent subgroup meets the Levi subgroup trivially. -/
theorem unipotent_inf_levi : unipotent A l ⊓ levi A l = ⊥ := by
  refine le_antisymm (fun g hg => ?_) bot_le
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg.1
  rw [Subgroup.mem_bot, ← limit_of_mem_levi hg.2, ← hg1]

/-! ### Cocharacter values, and the commutative case -/

/-- **The values of the cocharacter lie in its own Levi subgroup.** They commute with the generic
point because the multiplicative group is commutative. -/
theorem pointsHom_mem_levi (u : Aˣ) : pointsHom A l u ∈ levi A l := by
  set v := Units.map (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toMonoidHom u
  have h : constPoint A (pointsHom A l u) = pointsHom (LaurentPolynomial A) l v :=
    mapValue_pointsHom _ l u
  rw [mem_levi_iff, conjugate_apply, h, genericPoint,
    (pointsHom_commute (A := LaurentPolynomial A) l (genericUnit A) v).eq, mul_assoc,
    mul_inv_cancel, mul_one]

/-- For a commutative affine group every point is fixed by conjugation, so the dynamic Levi
subgroup attached to any cocharacter is everything. -/
theorem levi_eq_top [Coalgebra.IsCocomm R H] : levi A l = ⊤ :=
  eq_top_iff.mpr fun g _ => by
    rw [mem_levi_iff, conjugate_apply, mul_comm (genericPoint A l), mul_assoc, mul_inv_cancel,
      mul_one]

/-- For a commutative affine group the dynamic parabolic attached to any cocharacter is
everything. -/
theorem parabolic_eq_top [Coalgebra.IsCocomm R H] : parabolic A l = ⊤ :=
  eq_top_iff.mpr ((levi_eq_top (A := A) (l := l)).symm.le.trans levi_le_parabolic)

/-- For a commutative affine group the dynamic unipotent subgroup attached to any cocharacter is
trivial. -/
theorem unipotent_eq_bot [Coalgebra.IsCocomm R H] : unipotent A l = ⊥ := by
  have h := unipotent_inf_levi (A := A) (l := l)
  rwa [levi_eq_top, inf_top_eq] at h

/-! ### Functoriality of the dynamic subgroups in the value algebra -/

section Functoriality

variable (φ : A →ₐ[R] B)

/-- The inclusion of points over the affine line is natural in the value algebra. -/
theorem mapValue_ofPolyPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (ofPolyPoint A F) =
      ofPolyPoint B (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) := by
  have h : (AddMonoidAlgebra.mapAlgHom ℤ φ).comp (Polynomial.toLaurentAlg.restrictScalars R) =
      (Polynomial.toLaurentAlg.restrictScalars R).comp (Polynomial.mapAlgHom φ) := by
    ext a <;> simp [apply_ite φ]
  rw [ofPolyPoint, ofPolyPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, h,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

/-- Evaluation at the origin is natural in the value algebra. -/
theorem mapValue_evalZeroPoint (F : WithConv (H →ₐ[R] Polynomial A)) :
    AlgHom.mapValue φ (evalZeroPoint A F) =
      evalZeroPoint B (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) := by
  have h : φ.comp ((Polynomial.aeval (0 : A)).restrictScalars R) =
      ((Polynomial.aeval (0 : B)).restrictScalars R).comp (Polynomial.mapAlgHom φ) := by
    ext a <;> simp
  rw [evalZeroPoint, evalZeroPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, h,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

/-- **The dynamic parabolic is a subgroup functor**: it is preserved by change of value
algebra. -/
theorem parabolic_le_comap : parabolic A l ≤ (parabolic B l).comap (AlgHom.mapValue φ) := by
  intro g hg
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  refine Subgroup.mem_comap.mpr
    (mem_parabolic_of_eq (F := AlgHom.mapValue (Polynomial.mapAlgHom φ) F) ?_)
  rw [← mapValue_ofPolyPoint, hF, mapValue_conjugate_mapAlgHom]

/-- The Levi subgroup is preserved by change of value algebra. -/
theorem levi_le_comap : levi A l ≤ (levi B l).comap (AlgHom.mapValue φ) := fun g hg => by
  rw [Subgroup.mem_comap, mem_levi_iff, ← mapValue_conjugate_mapAlgHom, mem_levi_iff.mp hg,
    mapValue_constPoint]

/-- The extension over the origin is natural in the value algebra. -/
theorem extend_mapValue (g : parabolic A l) :
    extend B l ⟨AlgHom.mapValue φ (g : WithConv (H →ₐ[R] A)), parabolic_le_comap φ g.2⟩ =
      AlgHom.mapValue (Polynomial.mapAlgHom φ) (extend A l g) :=
  extend_unique (by
    rw [← mapValue_ofPolyPoint, ofPolyPoint_extend, mapValue_conjugate_mapAlgHom])

/-- The limit homomorphism is natural in the value algebra. -/
theorem mapValue_limit (g : parabolic A l) :
    AlgHom.mapValue φ (limit A l g) =
      limit B l ⟨AlgHom.mapValue φ (g : WithConv (H →ₐ[R] A)), parabolic_le_comap φ g.2⟩ := by
  rw [limit_apply, limit_apply, extend_mapValue, mapValue_evalZeroPoint]

/-- The unipotent subgroup is preserved by change of value algebra. -/
theorem unipotent_le_comap : unipotent A l ≤ (unipotent B l).comap (AlgHom.mapValue φ) := by
  intro g hg
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg
  refine Subgroup.mem_comap.mpr (mem_unipotent_iff.mpr ⟨parabolic_le_comap φ hgP, ?_⟩)
  rw [← mapValue_limit φ ⟨g, hgP⟩, hg1, map_one]

end Functoriality

/-! ### The limit lies in the Levi subgroup -/

section LeviRetraction

variable (R A) in
/-- The unit `T · T'` of `A[T;T⁻¹][T';T'⁻¹]`, the product of the two Laurent variables. -/
private noncomputable def prodUnit : (LaurentPolynomial (LaurentPolynomial A))ˣ :=
  Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
      (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom (genericUnit A) *
    genericUnit (LaurentPolynomial A)

variable (R A) in
/-- The substitution `T ↦ T · T'`, as an `R`-algebra homomorphism
`A[T;T⁻¹] → A[T;T⁻¹][T';T'⁻¹]`. -/
private noncomputable def prodSubst :
    LaurentPolynomial A →ₐ[R] LaurentPolynomial (LaurentPolynomial A) :=
  (MultiplicativeGroup.point (R := A) (prodUnit R A)).restrictScalars R

variable (R A) in
/-- The substitution `X ↦ T · X`, as an `R`-algebra homomorphism `A[X] → A[X][T;T⁻¹]`. -/
private noncomputable def scaleSubst :
    Polynomial A →ₐ[R] LaurentPolynomial (Polynomial A) :=
  (Polynomial.aeval (R := A)
    (LaurentPolynomial.C (Polynomial.X : Polynomial A) * LaurentPolynomial.T 1)).restrictScalars R

private theorem scaleSubst_C (a : A) :
    scaleSubst R A (Polynomial.C a) = LaurentPolynomial.C (Polynomial.C a) := by
  simp [scaleSubst]

private theorem scaleSubst_X :
    scaleSubst R A Polynomial.X =
      LaurentPolynomial.C (Polynomial.X : Polynomial A) * LaurentPolynomial.T 1 := by
  simp [scaleSubst]

private theorem prodSubst_C (a : A) :
    prodSubst R A (LaurentPolynomial.C a) = LaurentPolynomial.C (LaurentPolynomial.C a) :=
  MultiplicativeGroup.point_C (R := A) _ a

private theorem prodSubst_T :
    prodSubst R A (LaurentPolynomial.T 1) =
      (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) :=
  (MultiplicativeGroup.point_T (R := A) (prodUnit R A) 1).trans (by rw [zpow_one])

private theorem map_prodSubst_genericUnit :
    Units.map (prodSubst R A).toMonoidHom (genericUnit A) = prodUnit R A :=
  Units.ext prodSubst_T

private theorem prodSubst_comp_const :
    (prodSubst R A).comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).comp
          (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) :=
  AlgHom.ext fun a => prodSubst_C (R := R) a

private theorem prodUnit_val :
    (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 := by
  rw [prodUnit, Units.val_mul, Units.coe_map]
  simp

private theorem prodSubst_comp_toLaurent :
    (prodSubst R A).comp (Polynomial.toLaurentAlg.restrictScalars R) =
      (AddMonoidAlgebra.mapAlgHom ℤ
        (Polynomial.toLaurentAlg.restrictScalars R)).comp (scaleSubst R A) := by
  ext a <;>
    simp [prodSubst_C, prodSubst_T, scaleSubst_C, scaleSubst_X, prodUnit_val, mapAlgHom_C,
      mapAlgHom_T]

private theorem mapAlgHom_evalZero_comp_scaleSubst :
    (AddMonoidAlgebra.mapAlgHom ℤ ((Polynomial.aeval (0 : A)).restrictScalars R)).comp
        (scaleSubst R A) =
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).comp
        ((Polynomial.aeval (0 : A)).restrictScalars R) := by
  ext a <;> simp [scaleSubst_C, scaleSubst_X, mapAlgHom_C, mapAlgHom_T]

/-- **The limit of a point of the dynamic parabolic lies in the Levi subgroup.** Together with
`limit_of_mem_levi` this exhibits the limit homomorphism as a retraction of the dynamic parabolic
onto its Levi subgroup. -/
theorem limit_mem_levi (g : parabolic A l) : limit A l g ∈ levi A l := by
  have hF : AlgHom.mapValue (Polynomial.toLaurentAlg.restrictScalars R) (extend A l g) =
      conjugate A l (g : WithConv (H →ₐ[R] A)) := ofPolyPoint_extend g
  -- The generic identity `l(T) · F(X) · l(T)⁻¹ = F(T · X)` over `A[X][T;T⁻¹]`.
  have key : conjugate (Polynomial A) l (extend A l g) =
      AlgHom.mapValue (scaleSubst R A) (extend A l g) := by
    have hinj : Function.Injective (AddMonoidAlgebra.mapAlgHom ℤ
        (Polynomial.toLaurentAlg.restrictScalars R : Polynomial A →ₐ[R] LaurentPolynomial A)) :=
      AddMonoidAlgebra.map_injective _ Polynomial.toLaurent_injective
    refine AlgHom.mapValue_injective hinj ?_
    have hl : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ
          (Polynomial.toLaurentAlg.restrictScalars R))
          (conjugate (Polynomial A) l (extend A l g)) =
        conjugate (LaurentPolynomial A) l (conjugate A l (g : WithConv (H →ₐ[R] A))) := by
      rw [mapValue_conjugate_mapAlgHom, hF]
    have hr : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ
          (Polynomial.toLaurentAlg.restrictScalars R))
          (AlgHom.mapValue (scaleSubst R A) (extend A l g)) =
        AlgHom.mapValue (prodSubst R A) (conjugate A l (g : WithConv (H →ₐ[R] A))) := by
      rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, ← prodSubst_comp_toLaurent,
        AlgHom.mapValue_comp, MonoidHom.comp_apply, hF]
    rw [hl, hr, conjugate_apply, constPoint, mapValue_conjugate, genericPoint, conj_conj, ← map_mul,
      mapValue_conjugate, map_prodSubst_genericUnit, prodSubst_comp_const, prodUnit,
      mul_comm (Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom (genericUnit A))
        (genericUnit (LaurentPolynomial A))]
  -- Specialize the generic identity at `X = 0`.
  rw [mem_levi_iff, limit_apply, evalZeroPoint, constPoint, ← mapValue_conjugate_mapAlgHom, key,
    ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, mapAlgHom_evalZero_comp_scaleSubst,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

end LeviRetraction

/-! ### The Levi decomposition of the dynamic parabolic -/

/-- Dividing a point of the dynamic parabolic by its limit lands in the unipotent part. -/
theorem mul_limit_inv_mem_unipotent {g : WithConv (H →ₐ[R] A)} (hg : g ∈ parabolic A l) :
    g * (limit A l ⟨g, hg⟩)⁻¹ ∈ unipotent A l := by
  have hz : limit A l ⟨g, hg⟩ ∈ levi A l := limit_mem_levi ⟨g, hg⟩
  have hmem : g * (limit A l ⟨g, hg⟩)⁻¹ ∈ parabolic A l :=
    mul_mem hg (inv_mem (levi_le_parabolic hz))
  refine mem_unipotent_iff.mpr ⟨hmem, ?_⟩
  have hsplit : (⟨g * (limit A l ⟨g, hg⟩)⁻¹, hmem⟩ : parabolic A l) =
      ⟨g, hg⟩ * (⟨limit A l ⟨g, hg⟩, levi_le_parabolic hz⟩ : parabolic A l)⁻¹ := rfl
  rw [hsplit, map_mul, map_inv, limit_of_mem_levi hz, mul_inv_cancel]

/-- **The dynamic Levi decomposition, on points**: every point of the dynamic parabolic is a
point of its unipotent part times a point of its Levi part. -/
theorem exists_mem_unipotent_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ parabolic A l) :
    ∃ u ∈ unipotent A l, ∃ z ∈ levi A l, g = u * z :=
  ⟨g * (limit A l ⟨g, hg⟩)⁻¹, mul_limit_inv_mem_unipotent hg, limit A l ⟨g, hg⟩,
    limit_mem_levi ⟨g, hg⟩, (inv_mul_cancel_right g _).symm⟩

/-- The unipotent part and the Levi part generate the dynamic parabolic. -/
theorem unipotent_sup_levi : unipotent A l ⊔ levi A l = parabolic A l := by
  refine le_antisymm (sup_le unipotent_le_parabolic levi_le_parabolic) fun g hg => ?_
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mem_unipotent_mem_levi hg
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hz)

/-- The dynamic unipotent subgroup is normalized by the dynamic parabolic: it is the kernel of a
homomorphism defined on the parabolic. -/
theorem conj_mem_unipotent {p u : WithConv (H →ₐ[R] A)} (hp : p ∈ parabolic A l)
    (hu : u ∈ unipotent A l) : p * u * p⁻¹ ∈ unipotent A l := by
  obtain ⟨huP, hu1⟩ := mem_unipotent_iff.mp hu
  have hmem : p * u * p⁻¹ ∈ parabolic A l := mul_mem (mul_mem hp huP) (inv_mem hp)
  refine mem_unipotent_iff.mpr ⟨hmem, ?_⟩
  have hsplit : (⟨p * u * p⁻¹, hmem⟩ : parabolic A l) =
      (⟨p, hp⟩ : parabolic A l) * ⟨u, huP⟩ * (⟨p, hp⟩ : parabolic A l)⁻¹ := rfl
  rw [hsplit, map_mul, map_mul, map_inv, hu1, mul_one, mul_inv_cancel]

/-- The Levi decomposition of a point of the dynamic parabolic is unique. -/
theorem eq_of_unipotent_mul_levi_eq {u₁ u₂ z₁ z₂ : WithConv (H →ₐ[R] A)}
    (hu₁ : u₁ ∈ unipotent A l) (hu₂ : u₂ ∈ unipotent A l)
    (hz₁ : z₁ ∈ levi A l) (hz₂ : z₂ ∈ levi A l) (h : u₁ * z₁ = u₂ * z₂) :
    u₁ = u₂ ∧ z₁ = z₂ := by
  have hcross : u₂⁻¹ * u₁ = z₂ * z₁⁻¹ := by
    have h' := congrArg (fun t => u₂⁻¹ * t * z₁⁻¹) h
    simpa [mul_assoc] using h'
  have hbot : u₂⁻¹ * u₁ ∈ unipotent A l ⊓ levi A l :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hu₂) hu₁, hcross ▸ mul_mem hz₂ (inv_mem hz₁)⟩
  rw [unipotent_inf_levi, Subgroup.mem_bot, inv_mul_eq_one] at hbot
  refine ⟨hbot.symm, ?_⟩
  rw [hbot] at h
  exact mul_left_cancel h

end Cocharacter

end TauCeti
