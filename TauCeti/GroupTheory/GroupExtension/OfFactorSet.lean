/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Group extensions built from a factor set

A *factor set* of a group `G` with values in a `G`-module `M` (written multiplicatively: `M` is a
commutative group carrying a `MulDistribMulAction` of `G`) is a normalized multiplicative
`2`-cocycle `α : G × G → M`. This file builds the group extension `1 → M → E_α → G → 1` it
determines: the underlying set is `M × G`, and the multiplication is the one of a semidirect
product twisted by `α`,

`⟨a, g⟩ * ⟨b, h⟩ = ⟨a * g • b * α (g, h), g * h⟩`.

The cocycle identity is exactly associativity of this product and the normalization is exactly its
unitality, so both are carried as fields of `FactorSet` rather than as hypotheses of the results
below; without them the multiplication is neither associative nor unital.

Two facts identify `α` as *the* factor set of the extension it builds. The set-theoretic section
`g ↦ ⟨1, g⟩` fails to be a homomorphism by exactly `α` (`TauCeti.FactorSet.canonicalSection_mul`),
and conjugating the copy of `M` inside the extension is the given action of `G` on `M`
(`TauCeti.FactorSet.mul_inl`). When `G` acts trivially the latter says the copy of `M` is central,
so the extension is a central extension; that is the case `M = kˣ` in which a projective
representation of `G` with factor set `α` becomes a linear representation of `E_α`.

## Main definitions

* `TauCeti.FactorSet G M`: a normalized multiplicative `2`-cocycle `G × G → M`, bundled with its
  cocycle and normalization proofs.
* `TauCeti.FactorSet.Extension`: the twisted product `M × G` carrying the group structure above.
* `TauCeti.FactorSet.groupExtension`: that group as a `GroupExtension M _ G`, i.e. together with
  the inclusion of `M`, the projection to `G`, and the exactness proofs.
* `TauCeti.FactorSet.canonicalSection`: the section `g ↦ ⟨1, g⟩` of the projection.
* `TauCeti.FactorSet.rescaleEquiv`: the equivalence of extensions obtained by rescaling that
  section.
* `TauCeti.FactorSet.trivial`: the factor set that is constantly `1`.
* `TauCeti.FactorSet.toCocycles₂`: a factor set as a `2`-cocycle for the `ℤ`-linear representation
  of `G` on `Additive M`, the input to `groupCohomology.H2`.

## Main results

* `TauCeti.FactorSet.canonicalSection_mul`: `σ g * σ h = inl (α (g, h)) * σ (g * h)`, so `α`
  measures the failure of the canonical section to be a homomorphism.
* `TauCeti.FactorSet.mul_inl`: conjugation moves the copy of `M` by the action of the image in `G`.
* `TauCeti.FactorSet.inl_range_le_center`: when `G` acts trivially the extension is central.
* `TauCeti.FactorSet.nonempty_groupExtensionEquiv`: cohomologous factor sets build equivalent
  extensions.
* `TauCeti.FactorSet.trivialMulEquiv`: the extension attached to the trivial factor set is the
  semidirect product, and `TauCeti.FactorSet.trivialSplitting` splits it.

## References

This supplies the central-extension target of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` ("projective representations,
factor sets, and the Schur multiplier"), which the roadmap records as independent of Layers 3-5
apart from its closing Clifford-theory obstruction. See G. Karpilovsky, *Projective Representations
of Finite Groups*, Marcel Dekker (1985), Ch. 1, and I. M. Isaacs, *Character Theory of Finite
Groups*, AMS Chelsea (1976), Ch. 11.
-/

@[expose] public section

namespace TauCeti

open groupCohomology

universe u v

variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- A **factor set** of `G` with values in the `G`-module `M`: a multiplicative `2`-cocycle
`α : G × G → M` normalized by `α (1, 1) = 1`. The cocycle identity is Mathlib's
`groupCohomology.IsMulCocycle₂`, and the two fields are exactly what makes
`TauCeti.FactorSet.Extension` a group. -/
structure FactorSet where
  /-- The underlying function of a factor set. -/
  toFun : G × G → M
  /-- A factor set satisfies the multiplicative `2`-cocycle identity. -/
  isMulCocycle₂' : IsMulCocycle₂ toFun
  /-- A factor set is normalized. Together with the cocycle identity this forces
  `α (1, g) = α (g, 1) = 1` for every `g`. -/
  map_one_one' : toFun (1, 1) = 1

namespace FactorSet

variable {G M}

instance instFunLike : FunLike (FactorSet G M) (G × G) M where
  coe := toFun
  coe_injective := by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

@[simp]
theorem coe_mk (f : G × G → M) (hf : IsMulCocycle₂ f) (hf₁ : f (1, 1) = 1) :
    ⇑(mk f hf hf₁) = f :=
  rfl

@[ext]
theorem ext {α β : FactorSet G M} (h : ∀ p : G × G, α p = β p) : α = β :=
  DFunLike.ext _ _ h

section

variable (α : FactorSet G M)

theorem isMulCocycle₂ : IsMulCocycle₂ ⇑α := α.isMulCocycle₂'

/-- The cocycle identity of a factor set, in the form that gives associativity of the twisted
product `TauCeti.FactorSet.Extension`. -/
theorem cocycle (g h j : G) : α (g * h, j) * α (g, h) = g • α (h, j) * α (g, h * j) :=
  α.isMulCocycle₂ g h j

-- Not `@[simp]`: the two lemmas below subsume it.
theorem map_one_one : α (1, 1) = 1 := α.map_one_one'

@[simp]
theorem map_one_left (g : G) : α (1, g) = 1 := by
  rw [map_one_fst_of_isMulCocycle₂ α.isMulCocycle₂, map_one_one]

@[simp]
theorem map_one_right (g : G) : α (g, 1) = 1 := by
  rw [map_one_snd_of_isMulCocycle₂ α.isMulCocycle₂, map_one_one, smul_one]

/-- The two values of a factor set on an element and its inverse agree up to the action. This is
what makes the inverse of `TauCeti.FactorSet.Extension` a two-sided inverse. -/
theorem smul_apply_inv_left (g : G) : g • α (g⁻¹, g) = α (g, g⁻¹) := by
  have h := smul_map_inv_div_map_inv_of_isMulCocycle₂ α.isMulCocycle₂ g
  rwa [map_one_one, map_one_right, div_self', div_eq_one] at h

end

/-- The **twisted product** `M × G` attached to a factor set `α`: the underlying set of the group
extension of `G` by `M` that `α` determines, with multiplication
`⟨a, g⟩ * ⟨b, h⟩ = ⟨a * g • b * α (g, h), g * h⟩`. For the trivial factor set this is the
semidirect product `M ⋊ G` (`TauCeti.FactorSet.trivialMulEquiv`). -/
@[ext]
structure Extension (α : FactorSet G M) where
  /-- The `M`-component of an element of the twisted product. -/
  left : M
  /-- The `G`-component of an element of the twisted product. -/
  right : G

namespace Extension

variable {α : FactorSet G M}

instance instMul : Mul α.Extension where
  mul x y := ⟨x.left * x.right • y.left * α (x.right, y.right), x.right * y.right⟩

@[simp]
theorem mul_left (x y : α.Extension) :
    (x * y).left = x.left * x.right • y.left * α (x.right, y.right) :=
  rfl

@[simp]
theorem mul_right (x y : α.Extension) : (x * y).right = x.right * y.right := rfl

instance instOne : One α.Extension where one := ⟨1, 1⟩

@[simp] theorem one_left : (1 : α.Extension).left = 1 := rfl

@[simp] theorem one_right : (1 : α.Extension).right = 1 := rfl

instance instInv : Inv α.Extension where
  inv x := ⟨x.right⁻¹ • (x.left * α (x.right, x.right⁻¹))⁻¹, x.right⁻¹⟩

@[simp]
theorem inv_left (x : α.Extension) :
    x⁻¹.left = x.right⁻¹ • (x.left * α (x.right, x.right⁻¹))⁻¹ :=
  rfl

@[simp] theorem inv_right (x : α.Extension) : x⁻¹.right = x.right⁻¹ := rfl

instance instGroup : Group α.Extension where
  mul_assoc x y z := by
    ext
    · simp only [mul_left, mul_right, smul_mul', mul_smul]
      rw [show x.left * x.right • y.left * α (x.right, y.right) * (x.right • y.right • z.left) *
            α (x.right * y.right, z.right)
          = x.left * x.right • y.left * (x.right • y.right • z.left) *
            (α (x.right * y.right, z.right) * α (x.right, y.right)) from by ac_rfl, α.cocycle]
      ac_rfl
    · exact mul_assoc _ _ _
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    have key : x.right⁻¹ • α (x.right, x.right⁻¹) = α (x.right⁻¹, x.right) := by
      simpa using α.smul_apply_inv_left x.right⁻¹
    ext
    · rw [mul_left, inv_left, inv_right, one_left, smul_inv', smul_mul', key, mul_assoc,
        inv_mul_cancel]
    · simp

end Extension

section

variable (α : FactorSet G M)

/-- The inclusion of `M` into the twisted product, as `a ↦ ⟨a, 1⟩`. -/
def inl : M →* α.Extension where
  toFun a := ⟨a, 1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

@[simp] theorem inl_left (a : M) : (inl α a).left = a := rfl

@[simp] theorem inl_right (a : M) : (inl α a).right = 1 := rfl

/-- The projection of the twisted product onto `G`. -/
def rightHom : α.Extension →* G where
  toFun := Extension.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightHom_apply (x : α.Extension) : rightHom α x = x.right := rfl

theorem inl_injective : Function.Injective (inl α) := fun _ _ h => congrArg Extension.left h

theorem range_inl_eq_ker_rightHom : (inl α).range = (rightHom α).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp [MonoidHom.mem_ker]
  · intro hx
    have hx' : x.right = 1 := MonoidHom.mem_ker.1 hx
    refine ⟨x.left, ?_⟩
    ext
    · rfl
    · exact hx'.symm

theorem rightHom_surjective : Function.Surjective (rightHom α) := fun g => ⟨⟨1, g⟩, rfl⟩

/-- The group extension `1 → M → E_α → G → 1` determined by a factor set. -/
def groupExtension : GroupExtension M α.Extension G where
  inl := inl α
  rightHom := rightHom α
  inl_injective := inl_injective α
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom α
  rightHom_surjective := rightHom_surjective α

@[simp] theorem groupExtension_inl : α.groupExtension.inl = inl α := rfl

@[simp] theorem groupExtension_rightHom : α.groupExtension.rightHom = rightHom α := rfl

/-- The canonical set-theoretic section `g ↦ ⟨1, g⟩` of the projection. It fails to be a
homomorphism by exactly `α`; see `TauCeti.FactorSet.canonicalSection_mul`. -/
def canonicalSection : α.groupExtension.Section where
  toFun g := ⟨1, g⟩
  rightInverse_rightHom _ := rfl

@[simp] theorem canonicalSection_apply (g : G) : α.canonicalSection g = ⟨1, g⟩ := rfl

/-- **A factor set is the factor set of the extension it builds**: the canonical section fails to
be a homomorphism by exactly `α`. -/
theorem canonicalSection_mul (g h : G) :
    α.canonicalSection g * α.canonicalSection h
      = inl α (α (g, h)) * α.canonicalSection (g * h) := by
  ext <;> simp

/-- Conjugation in the twisted product moves the copy of `M` by the action of the image in `G`.
The copy of `M` is normal for a second reason: it is a kernel,
by `TauCeti.FactorSet.range_inl_eq_ker_rightHom`. -/
theorem mul_inl (x : α.Extension) (a : M) : x * inl α a = inl α (x.right • a) * x := by
  ext <;> simp [mul_comm]

/-- **The extension is central when `G` acts trivially on `M`.** This is the case `M = kˣ` with the
trivial action, in which a projective representation of `G` with factor set `α` is a linear
representation of the extension. -/
theorem inl_range_le_center (h : ∀ (g : G) (a : M), g • a = a) :
    (inl α).range ≤ Subgroup.center α.Extension := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  rw [mul_inl, h]

end

section Rescale

variable (α β : FactorSet G M) (x : G → M)
  (hx : ∀ g h : G, α (g, h) * x (g * h) = β (g, h) * (g • x h * x g))

include hx

/-- A rescaling turning one factor set into another is normalized. -/
theorem rescale_one : x 1 = 1 := by simpa using hx 1 1

/-- **Rescaling the canonical section by `x` turns the extension built from `α` into the one built
from `β`.** The hypothesis says that `α` and `β` differ by the coboundary of `x`; see
`TauCeti.FactorSet.nonempty_groupExtensionEquiv`. -/
def rescaleEquiv : α.groupExtension.Equiv β.groupExtension where
  toFun y := ⟨y.left * x y.right, y.right⟩
  invFun y := ⟨y.left * (x y.right)⁻¹, y.right⟩
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp
  map_mul' y z := by
    ext
    · change y.left * y.right • z.left * α (y.right, z.right) * x (y.right * z.right)
        = y.left * x y.right * y.right • (z.left * x z.right) * β (y.right, z.right)
      rw [mul_assoc, hx, smul_mul']
      ac_rfl
    · rfl
  inl_comm := by
    funext a
    ext
    · change a * x 1 = a
      rw [rescale_one α β x hx, mul_one]
    · rfl
  rightHom_comm := rfl

@[simp]
theorem rescaleEquiv_apply (y : α.Extension) :
    rescaleEquiv α β x hx y = ⟨y.left * x y.right, y.right⟩ :=
  rfl

end Rescale

section

variable (α β : FactorSet G M)

/-- **Cohomologous factor sets build equivalent extensions.** Two factor sets whose quotient is a
multiplicative `2`-coboundary give equivalent group extensions of `G` by `M`, the equivalence
rescaling the canonical section by the function the coboundary comes from. -/
theorem nonempty_groupExtensionEquiv
    (h : IsMulCoboundary₂ fun p : G × G => α p / β p) :
    Nonempty (α.groupExtension.Equiv β.groupExtension) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨rescaleEquiv α β x fun g h => ?_⟩
  have key := hx g h
  rw [div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul] at key
  rw [← key]
  ac_rfl

end

section Trivial

variable (G M)

/-- The **trivial factor set**, constantly `1`. Its extension is the semidirect product
(`TauCeti.FactorSet.trivialMulEquiv`) and is split (`TauCeti.FactorSet.trivialSplitting`). -/
def trivial : FactorSet G M where
  toFun _ := 1
  isMulCocycle₂' g h j := by simp
  map_one_one' := rfl

@[simp] theorem trivial_apply (p : G × G) : trivial G M p = 1 := rfl

/-- The extension attached to the trivial factor set is the semidirect product of `M` by `G`. -/
def trivialMulEquiv :
    (trivial G M).Extension ≃* M ⋊[MulDistribMulAction.toMulAut G M] G where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.left, x.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext <;> simp

/-- The extension attached to the trivial factor set is split: there the canonical section is a
homomorphism. -/
def trivialSplitting : (trivial G M).groupExtension.Splitting :=
  GroupExtension.Splitting.mk
    { toFun g := ⟨1, g⟩
      map_one' := rfl
      map_mul' _ _ := by ext <;> simp }
    fun _ => rfl

@[simp] theorem trivialSplitting_apply (g : G) : trivialSplitting G M g = ⟨1, g⟩ := rfl

end Trivial

/-- A factor set, read as a `2`-cocycle for the `ℤ`-linear representation of `G` on `Additive M`.
Its class in `groupCohomology.H2` is the factor set up to the rescaling of
`TauCeti.FactorSet.canonicalSection` that a coboundary records. The universes are pinned to `Type`
because `Rep ℤ G` forces its group and its module into the universe of `ℤ`. -/
def toCocycles₂ {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (α : FactorSet G M) : cocycles₂ (Rep.ofMulDistribMulAction G M) :=
  cocyclesOfIsMulCocycle₂ α.isMulCocycle₂

@[simp]
theorem toCocycles₂_apply {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (α : FactorSet G M) (p : G × G) : (toCocycles₂ α).1 p = Additive.ofMul (α p) :=
  rfl

end FactorSet

end TauCeti
