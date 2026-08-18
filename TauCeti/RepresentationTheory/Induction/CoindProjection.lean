/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The dual projection formula for coinduced representations

For a group homomorphism `φ : G →* H`, a `G`-representation `A` and an `H`-representation `B`, the
*dual projection formula* is the isomorphism of `H`-representations

`Coind_φ (Hom(Res_φ B, A)) ≅ Hom(B, Coind_φ A)`.

It is the exact dual of the projection formula `Ind_φ (A ⊗ Res_φ B) ≅ (Ind_φ A) ⊗ B` of
`TauCeti/RepresentationTheory/Induction/Projection.lean`: the tensor product of the induction
statement is replaced by the internal hom of `Rep k H`, and induction by coinduction. Where the
projection formula says that induction is a map of modules over the representation ring, this one
says that coinduction commutes with the internal hom of `Rep k H` in its covariant variable.

Mathlib has the adjunction `Rep.resCoindAdjunction` and its hom-set equivalence
`Rep.resCoindHomEquiv`, which are this formula after taking `H`-invariants of both sides: an
invariant vector of `Hom(B, Coind_φ A)` is a morphism `B ⟶ Coind_φ A`, and an invariant vector of
`Coind_φ (Hom(Res_φ B, A))` is a morphism `Res_φ B ⟶ A`, sitting there as a constant function. The
isomorphism of representations itself is not upstream, and it is not a formal consequence of the
adjunction: `Representation.coind` is carved out of the functions `H → A`, so the map has to be
produced by hand and shown to land in the equivariant ones. That is what this file does, over an
arbitrary commutative ring, for a homomorphism of groups rather than only a subgroup inclusion.

The two directions are

`F ↦ (b ↦ (h ↦ F h (τ h b)))`,  `Φ ↦ (h ↦ (b ↦ Φ (τ h⁻¹ b) h))`,

writing `τ` for the representation on `B`. The twist by `τ h` is forced, exactly as the twist by
`τ h⁻¹` is forced in the projection formula. A vector of `Coind_φ (Hom(Res_φ B, A))` is a function
`F : H → (B →ₗ[k] A)` with `F (φ g * h) = ρ g ∘ₗ F h ∘ₗ τ (φ g)⁻¹`, while a vector of
`Hom(B, Coind_φ A)` is a linear map in `b` whose values obey the *untwisted* equivariance
`Φ b (φ g * h) = ρ g (Φ b h)`. Feeding `τ h b` into `F h` is what cancels the `τ (φ g)⁻¹` against
the group coordinate, and it is also what makes the map `H`-equivariant, since `H` acts on
`Coind_φ A` by `(h₀ • f) h = f (h * h₀)` and on `Hom(B, C)` by conjugation.

## Main definitions

* `TauCeti.coindProjection`: **the dual projection formula**,
  `Rep.coind φ ((Rep.ihom (Rep.res φ Y)).obj X) ≅ (Rep.ihom Y).obj (Rep.coind φ X)` in `Rep k H`.
* `TauCeti.coindProjectionEquiv`, `TauCeti.coindProjectionLEquiv`: the same isomorphism as an
  equivalence of `Representation`s and as a `k`-linear equivalence of the underlying modules, built
  from the two explicit maps `TauCeti.coindProjectionHom` and `TauCeti.coindProjectionInv`.
* `TauCeti.coindProjectionNatIso`: the dual projection formula as a natural isomorphism of functors
  `Rep k G ⥤ Rep k H` in the coinduced variable.
* `TauCeti.coindConst`: an intertwiner `Res_φ B ⟶ A`, viewed as the constant function in
  `Coind_φ (Hom(Res_φ B, A))`.

## Main statements

* `TauCeti.coindProjectionHom_apply_coe`, `TauCeti.coindProjectionInv_apply_coe`: the two `k`-linear
  maps, evaluated at a group element. Every proof below goes through these two rules rather than
  through the definitions.
* `TauCeti.coindProjection_hom_hom_toLinearMap`, `TauCeti.coindProjection_inv_hom_toLinearMap`: the
  two directions of the `Rep k H` isomorphism are the two `k`-linear maps above.
* `TauCeti.coindProjection_hom_naturality` and `TauCeti.coindProjectionNatIso`: naturality in the
  coinduced variable.
* `TauCeti.resCoindToHom_eq_coindProjectionHom`: **the comparison with Mathlib's adjunction.** The
  dual projection formula carries the constant function at an intertwiner `f : Res_φ B ⟶ A` to the
  adjunct `Rep.resCoindToHom φ B A f` of Mathlib's `Res ⊣ Coind` adjunction, so the hom-set
  bijection of `Rep.resCoindAdjunction` is the restriction of the formula to the constant vectors.
  The adjunction is therefore consumed by the formula, not reproved by it.

## Implementation notes

Both directions are assembled from `LinearMap.pi`, `LinearMap.proj` and `LinearMap.codRestrict`, so
that linearity in the module variable holds by construction and only the equivariance conditions
have to be checked. The evaluation lemmas are stated on the underlying function of a submodule
element (`.1 h`), matching Mathlib's own `Representation.coindMap_coe_apply_apply`.

The equivariance of `TauCeti.coindProjectionEquiv` is proved by `congrArg` against a stated
cancellation `τ (h * h₀) ∘ₗ τ h₀⁻¹ = τ h` rather than by rewriting the goal. Mathlib's `@[simps]`
output for `Representation.coind` stops at the `LinearMap.restrict` carrying the action, and
rewriting through that restriction leaves the goal ill-typed at `implicit` transparency; both sides
are already definitionally the displayed formulas, so supplying the one genuine equation is enough.

The formula is contravariantly functorial in `B` as well; Mathlib packages that variance of the
internal hom as `CategoryTheory.MonoidalClosed.internalHom`, built from the mates construction
`MonoidalClosed.pre`. The naturality recorded here is the covariant one, in the `Rep k G` argument,
which is the variable the functorial statement `coindProjectionNatIso` is about.

The `Representation`-level constructions are universe-polymorphic in `k`, `G`, `H` and the two
carrier modules. The `Rep k H` layer keeps the source group `G` free but places `H` and both carrier
modules in the universe of `k`: `Rep.coind φ` raises the module universe by that of `H`, and
`Rep.ihom` compares its result with a representation of `H` in a single universe.

## References

This is the dual projection formula of Layer 0 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks for the projection
formula "and its dual" as isomorphisms of representations. See C. W. Curtis, I. Reiner, *Methods of
Representation Theory, Vol. I*, Wiley (1981), §10.
-/

public section

open CategoryTheory Representation

namespace TauCeti

universe u v v' w w'

section Linear

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  {A : Type w} {B : Type w'} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  (ρ : Representation k G A) (τ : Representation k H B)

/-- The forward map of the dual projection formula, `F ↦ (b ↦ (h ↦ F h (τ h b)))`. Feeding `τ h b`
into the `h`-th component is what turns the twisted equivariance of a coinduced vector of
`Hom(Res_φ B, A)` into the untwisted equivariance of a coinduced vector of `A`. -/
noncomputable def coindProjectionHom :
    coindV φ (linHom (τ.comp φ) ρ) →ₗ[k] B →ₗ[k] coindV φ ρ where
  toFun F := LinearMap.codRestrict (coindV φ ρ)
      (LinearMap.pi fun h => (F.1 h).comp (τ h : B →ₗ[k] B)) fun b => by
    simp only [mem_coindV, LinearMap.pi_apply, LinearMap.comp_apply]
    intro g h
    rw [F.2 g h]
    simp only [linHom_apply, LinearMap.coe_comp, Function.comp_apply, MonoidHom.comp_apply,
      map_inv]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- `TauCeti.coindProjectionHom`, evaluated at a group element. This is the only place the
definition is unfolded; every later proof rewrites with this rule instead. -/
@[simp]
theorem coindProjectionHom_apply_coe (F : coindV φ (linHom (τ.comp φ) ρ)) (b : B) (h : H) :
    (coindProjectionHom φ ρ τ F b).1 h = F.1 h (τ h b) :=
  (rfl)

/-- The backward map of the dual projection formula, `Φ ↦ (h ↦ (b ↦ Φ (τ h⁻¹ b) h))`. -/
noncomputable def coindProjectionInv :
    (B →ₗ[k] coindV φ ρ) →ₗ[k] coindV φ (linHom (τ.comp φ) ρ) where
  toFun Φ := ⟨fun h => (LinearMap.proj h ∘ₗ (coindV φ ρ).subtype ∘ₗ Φ).comp
      (τ h⁻¹ : B →ₗ[k] B), by
    simp only [mem_coindV]
    intro g h
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      Submodule.coe_subtype, linHom_apply, MonoidHom.comp_apply, map_inv]
    rw [(Φ _).2 g h, mul_inv_rev, map_mul, Module.End.mul_apply]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- `TauCeti.coindProjectionInv`, evaluated at a group element. This is the only place the
definition is unfolded; every later proof rewrites with this rule instead. -/
@[simp]
theorem coindProjectionInv_apply_coe (Φ : B →ₗ[k] coindV φ ρ) (h : H) (b : B) :
    (coindProjectionInv φ ρ τ Φ).1 h b = (Φ (τ h⁻¹ b)).1 h :=
  (rfl)

/-- The dual projection formula as a `k`-linear equivalence of the underlying modules: the two maps
above are mutually inverse because `τ h` and `τ h⁻¹` cancel. -/
noncomputable def coindProjectionLEquiv :
    coindV φ (linHom (τ.comp φ) ρ) ≃ₗ[k] B →ₗ[k] coindV φ ρ :=
  LinearEquiv.ofLinearMap (coindProjectionHom φ ρ τ) (coindProjectionInv φ ρ τ)
    (by ext Φ b h; simp)
    (by ext F h b; simp)

/-- `TauCeti.coindProjectionLEquiv` is `TauCeti.coindProjectionHom` in the forward direction. -/
@[simp]
theorem coindProjectionLEquiv_apply (F : coindV φ (linHom (τ.comp φ) ρ)) :
    coindProjectionLEquiv φ ρ τ F = coindProjectionHom φ ρ τ F :=
  (rfl)

/-- The dual projection formula as an equivalence of representations. Equivariance is the
computation `τ (h * h₀) ∘ₗ τ h₀⁻¹ = τ h`: translating the group coordinate of a coinduced vector on
the right by `h₀` is matched by conjugating a linear map by `τ h₀`. -/
noncomputable def coindProjectionEquiv :
    (Representation.coind φ (linHom (τ.comp φ) ρ)).Equiv (linHom τ (Representation.coind φ ρ)) :=
  Representation.Equiv.mk (coindProjectionLEquiv φ ρ τ) fun h₀ =>
    LinearMap.ext fun F => LinearMap.ext fun b => Subtype.ext (funext fun h => by
      have hb : τ (h * h₀) (τ h₀⁻¹ b) = τ h b := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
      exact congrArg (fun x => F.1 (h * h₀) x) hb.symm)

/-- An intertwiner `f : Res_φ B ⟶ A`, viewed as a vector of `Coind_φ (Hom(Res_φ B, A))`: it is
`G`-equivariant, so the constant function `H → (B →ₗ[k] A)` at `f` satisfies the twisted
equivariance defining the coinduced module. -/
def coindConst (f : Representation.IntertwiningMap (τ.comp φ) ρ) :
    coindV φ (linHom (τ.comp φ) ρ) :=
  ⟨fun _ => f.toLinearMap, fun g _ => LinearMap.ext fun b => by
    have hb : (τ.comp φ) g ((τ.comp φ) g⁻¹ b) = b := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    simpa [hb] using LinearMap.congr_fun (f.isIntertwining' g) ((τ.comp φ) g⁻¹ b)⟩

/-- `TauCeti.coindConst` is the constant function at the given intertwiner. -/
@[simp]
theorem coindConst_coe_apply (f : Representation.IntertwiningMap (τ.comp φ) ρ) (h : H) (b : B) :
    (coindConst φ ρ τ f).1 h b = f b :=
  (rfl)

end Linear

section Rep

variable {k : Type u} {G : Type v} {H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (X : Rep.{u} k G) (Y : Rep.{u} k H)

/-- **The dual projection formula** in `Rep k H`: coinducing the internal hom out of a restricted
representation is the internal hom out of that representation into the coinduced one,
`Coind_φ (Hom(Res_φ Y, X)) ≅ Hom(Y, Coind_φ X)`. -/
noncomputable def coindProjection :
    Rep.coind φ ((Rep.ihom (Rep.res φ Y)).obj X) ≅ (Rep.ihom Y).obj (Rep.coind φ X) :=
  Rep.mkIso (coindProjectionEquiv φ X.ρ Y.ρ)

/-- The forward direction of `TauCeti.coindProjection` is `TauCeti.coindProjectionHom`; the
element-level rule is `TauCeti.coindProjectionHom_apply_coe`. -/
theorem coindProjection_hom_hom_toLinearMap :
    (coindProjection φ X Y).hom.hom.toLinearMap = coindProjectionHom φ X.ρ Y.ρ :=
  (rfl)

/-- The backward direction of `TauCeti.coindProjection` is `TauCeti.coindProjectionInv`; the
element-level rule is `TauCeti.coindProjectionInv_apply_coe`. -/
theorem coindProjection_inv_hom_toLinearMap :
    (coindProjection φ X Y).inv.hom.toLinearMap = coindProjectionInv φ X.ρ Y.ρ :=
  (rfl)

/-- The dual projection formula is natural in the coinduced variable, the `Rep k G` argument. -/
theorem coindProjection_hom_naturality {X X' : Rep.{u} k G} (f : X ⟶ X') (Y : Rep.{u} k H) :
    (Rep.coindFunctor k φ).map ((Rep.ihom (Rep.res φ Y)).map f) ≫ (coindProjection φ X' Y).hom
      = (coindProjection φ X Y).hom ≫ (Rep.ihom Y).map ((Rep.coindFunctor k φ).map f) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ =>
    LinearMap.ext fun _ => Subtype.ext (funext fun _ => (rfl))))

/-- The dual projection formula as a natural isomorphism: the functors
`X ↦ Coind_φ (Hom(Res_φ Y, X))` and `X ↦ Hom(Y, Coind_φ X)` from `Rep k G` to `Rep k H` agree. -/
noncomputable def coindProjectionNatIso (Y : Rep.{u} k H) :
    Rep.ihom (Rep.res φ Y) ⋙ Rep.coindFunctor k φ ≅ Rep.coindFunctor k φ ⋙ Rep.ihom Y :=
  NatIso.ofComponents (fun X => coindProjection φ X Y) fun {_ _} f =>
    coindProjection_hom_naturality φ f Y

/-- **The comparison with Mathlib's adjunction.** The dual projection formula carries the constant
function at an intertwiner `f : Res_φ Y ⟶ X` to the adjunct `Rep.resCoindToHom φ Y X f` of
Mathlib's `Res ⊣ Coind` adjunction. So the hom-set bijection of `Rep.resCoindAdjunction` is the
restriction of `TauCeti.coindProjection` to the constant vectors, and the adjunction is consumed by
the formula rather than reproved by it. -/
theorem resCoindToHom_eq_coindProjectionHom (f : Rep.res φ Y ⟶ X) :
    (Rep.resCoindToHom φ Y X f).hom.toLinearMap
      = coindProjectionHom φ X.ρ Y.ρ (coindConst φ X.ρ Y.ρ f.hom) :=
  (rfl)

end Rep

end TauCeti
