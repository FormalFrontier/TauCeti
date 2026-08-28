/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Cup products in low degrees on the explicit model

A cup product on continuous cochains is relative to a `G`-equivariant biadditive pairing
`μ : M →+ N →+ P`, that is one with `μ (g • m) (g • n) = g • μ m n`, which is furthermore
jointly continuous. This file builds the six low-degree shapes

```text
(p, q) ∈ {(0,0), (0,1), (1,0), (0,2), (1,1), (2,0)},   p + q ≤ 2,
```

of the general inhomogeneous formula
`(a ⌣ b)(g₁, …, g_{p+q}) = μ (a (g₁, …, g_p)) ((g₁ ⋯ g_p) • b (g_{p+1}, …, g_{p+q}))`, namely

```text
(0,0):  m ⌣ n = μ m n,                        (0,1):  (m ⌣ b) g = μ m (b g),
(1,0):  (a ⌣ n) g = μ (a g) (g • n),          (0,2):  (m ⌣ b) (g, h) = μ m (b (g, h)),
(1,1):  (a ⌣ b) (g, h) = μ (a g) (g • b h),   (2,0):  (a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n).
```

## Main definitions

* `TauCeti.ContCohomology.pairingLeft` and `TauCeti.ContCohomology.pairingRight`: partial
  application of the pairing at an *invariant* element, as an equivariant additive homomorphism.
  This is what makes the five shapes with a degree-`0` factor instances of the coefficient maps
  `TauCeti.ContCohomology.explicitCoeff0`, `explicitCoeff1` and `explicitCoeff2`.
* `TauCeti.ContCohomology.explicitCup00`, `explicitCup01`, `explicitCup10`, `explicitCup02`,
  `explicitCup11`, `explicitCup20`: the six shapes, each biadditive by construction, with the
  `_mk` theorems fixing the cochain formula on classes of cocycles.

## Main statements

* `TauCeti.ContCohomology.cup01_mem_Z1`, `cup10_mem_Z1`, `cup02_mem_Z2`, `cup11_mem_Z2` and
  `cup20_mem_Z2`: a cocycle cupped with a cocycle is a cocycle, the cochain-level heart of each
  shape.
* `TauCeti.ContCohomology.cup11_mem_B2_left` and `cup11_mem_B2_right`: the `(1,1)` cup descends
  through coboundaries in each variable. These are the only descent statements proved by hand:
  the other five shapes descend because they *are* coefficient maps, whose descent is
  `TauCeti.ContCohomology.cochainsMap1_mem_B1` and `cochainsMap2_mem_B2`.
* `TauCeti.ContCohomology.explicitCup00_comm`, `explicitCup01_eq_cup10_flip`,
  `explicitCup02_eq_cup20_flip` and `explicitCup11_eq_neg_flip`: **graded commutativity**
  `a ⌣_μ b = (-1)^{pq} (b ⌣_{μᵒᵖ} a)` in each bidegree with `p + q ≤ 2`, where `μᵒᵖ n m = μ m n`
  is Mathlib's `AddMonoidHom.flip`. With the sign `1` in the three shapes that have a degree-`0`
  factor the identity already holds on cochains, and those three are stated at cochain level as
  well (`cup01_eq_cup10_flip`, `cup02_eq_cup20_flip`), a degree-`0` class being invariant. In
  bidegree `(1,1)` it holds only on classes, with the sign `-1`.
* `TauCeti.ContCohomology.explicitCup11_comm_of_neg_eq_self`: the `2`-torsion specialization, in
  which the `(1,1)` cup is symmetric.

## Implementation notes

The translation factor `g •` in the `(1,0)`, `(1,1)` and `(2,0)` formulas is the one the general
inhomogeneous formula carries, and it is kept in the statements even though a degree-`0` class is
invariant and the factor is therefore invisible in the `(1,0)` and `(2,0)` shapes. Keeping it is
what makes those two shapes the specializations of the general formula that the roadmap's
associativity instances need, rather than the `(0,1)` and `(0,2)` shapes read backwards.

The `(1,1)` shape is the only one that is not a coefficient map, and the only one whose descent
through coboundaries needs a homotopy. Its two primitives are

```text
a ∈ B¹, a = d⁰ m :  (a ⌣ b) = d¹ (x ↦ μ m (b x)),
b ∈ B¹, b = d⁰ n :  (a ⌣ b) = d¹ (x ↦ -μ (a x) (x • n)),
```

recorded here because the graded-commutativity statement refers to them.

The `(1,1)` graded-commutativity homotopy is fixed once, here, and every sign below is read off
it: for continuous `1`-cocycles `a` and `b`,

```text
(a ⌣_μ b) + (b ⌣_{μᵒᵖ} a) = d¹ (g ↦ -μ (a g) (b g)),
```

which is `TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`.

Each cocycle proof opens with a `change`. It only beta-reduces: `groupCohomology.IsCocycle₁` and
`IsCocycle₂` are predicates on a function, so with the cup cochain supplied as a lambda the goal
is stated with a redex and the identity to be proved is unreadable until it is contracted. No
`change` below alters the goal by more than beta.

Continuity of the cup cochains is where joint continuity of `μ` is used. It is automatic when `M`
and `N` are discrete, which is the case in every arithmetic application, but it is carried as a
hypothesis rather than derived so that the shapes are available at the general topological
coefficients the explicit complex is built for.

This implements the "six low-degree shapes" and "graded commutativity" milestones of Layer 8 of
the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose §3 fixes the six formulas and whose
`Suggested.lean` fixes the names `explicitCup00`, `explicitCup01`, `explicitCup10`,
`explicitCup02`, `explicitCup11` and `explicitCup20`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §4: the cup
  product on inhomogeneous cochains and its low-degree formulas, and (1.4.4) for graded
  commutativity.
* K. Brown, *Cohomology of Groups*, V §3: the cochain-level cup product, and (3.6) for graded
  commutativity.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section Pairing

variable {G : Type uG} [Monoid G]
  {M : Type uM} [AddCommGroup M] [DistribMulAction G M]
  {N : Type uN} [AddCommGroup N] [DistribMulAction G N]
  {P : Type uP} [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- Partial application of an equivariant pairing at an **invariant** element of the first
factor. Invariance is what makes `μ m : N →+ P` equivariant, and hence what makes the `(0, q)`
cup shapes coefficient maps. -/
def pairingLeft (m : H0 G M) : N →+[G] P where
  toFun := μ (m : M)
  map_add' := map_add (μ (m : M))
  map_zero' := map_zero (μ (m : M))
  map_smul' g x := by
    conv_lhs => rw [← m.2 g]
    exact hequiv g (m : M) x

/-- Partial application of an equivariant pairing at an **invariant** element of the second
factor. -/
def pairingRight (n : H0 G N) : M →+[G] P where
  toFun m := μ m (n : N)
  map_add' m m' := by simp
  map_zero' := by simp
  map_smul' g m := by
    conv_lhs => rw [← n.2 g]
    exact hequiv g m (n : N)

/-- The underlying additive homomorphism of `TauCeti.ContCohomology.pairingLeft`. -/
@[simp]
theorem coe_pairingLeft (m : H0 G M) :
    ((pairingLeft μ hequiv m : N →+[G] P) : N →+ P) = μ (m : M) := (rfl)

/-- The underlying additive homomorphism of `TauCeti.ContCohomology.pairingRight` is the flip of
the pairing. -/
@[simp]
theorem coe_pairingRight (n : H0 G N) :
    ((pairingRight μ hequiv n : M →+[G] P) : M →+ P) = μ.flip (n : N) := (rfl)

/-- The defining formula for `TauCeti.ContCohomology.pairingLeft`. -/
@[simp]
theorem pairingLeft_apply (m : H0 G M) (x : N) : pairingLeft μ hequiv m x = μ (m : M) x := (rfl)

/-- The defining formula for `TauCeti.ContCohomology.pairingRight`. -/
@[simp]
theorem pairingRight_apply (n : H0 G N) (m : M) : pairingRight μ hequiv n m = μ m (n : N) := (rfl)

include hequiv in
/-- The pairing with an invariant first argument absorbs the action from the second. -/
theorem pairingLeft_smul (m : H0 G M) (g : G) (x : N) :
    μ (m : M) (g • x) = g • μ (m : M) x :=
  (pairingLeft μ hequiv m).map_smul g x

include hequiv in
/-- The pairing with an invariant second argument absorbs the action from the first. -/
theorem pairingRight_smul (n : H0 G N) (g : G) (m : M) :
    μ (g • m) (n : N) = g • μ m (n : N) :=
  (pairingRight μ hequiv n).map_smul g m

include hequiv in
/-- **The opposite pairing `μᵒᵖ n m = μ m n` is equivariant.** Mathlib's `AddMonoidHom.flip` is
the `μᵒᵖ` of the graded-commutativity statements below, and this is the hypothesis it has to be
fed to be cupped against. -/
theorem equivariant_flip (g : G) (x : N) (m : M) :
    μ.flip (g • x) (g • m) = g • μ.flip x m := by
  simp only [AddMonoidHom.flip_apply]
  exact hequiv g m x

variable [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  (hμ : Continuous fun p : M × N => μ p.1 p.2)

include hμ

/-- A jointly continuous pairing is continuous in the second variable. -/
theorem continuous_pairingLeft (m : H0 G M) : Continuous (pairingLeft μ hequiv m) :=
  hμ.comp (continuous_const.prodMk continuous_id)

/-- A jointly continuous pairing is continuous in the first variable. -/
theorem continuous_pairingRight (n : H0 G N) : Continuous (pairingRight μ hequiv n) :=
  hμ.comp (continuous_id.prodMk continuous_const)

/-- **The opposite pairing of a jointly continuous pairing is jointly continuous**, being its
composite with the swap homeomorphism. -/
theorem continuous_flip : Continuous fun p : N × M => μ.flip p.1 p.2 :=
  hμ.comp continuous_swap

end Pairing

section CupZeroZero

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **The `(0,0)` cup product**, `m ⌣ n = μ m n`: the pairing of two invariant elements is
invariant. No topology is involved, `H⁰` being a subgroup and not a quotient. -/
def explicitCup00 : H0 G M →+ H0 G N →+ H0 G P :=
  AddMonoidHom.mk' (fun m => explicitCoeff0 G N (pairingLeft μ hequiv m))
    fun m m' => AddMonoidHom.ext fun n => Subtype.ext <| by
      simp [coe_explicitCoeff0]

/-- The `(0,0)` cup is the pairing itself. -/
@[simp]
theorem coe_explicitCup00 (m : H0 G M) (n : H0 G N) :
    (explicitCup00 G M N P μ hequiv m n : P) = μ (m : M) (n : N) :=
  coe_explicitCoeff0 G N (pairingLeft μ hequiv m) n

end CupZeroZero

section CupZeroOne

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

omit [ContinuousSMul G N] [ContinuousSMul G P] in
/-- **The `(0,1)` cup of an invariant element with a continuous `1`-cocycle is a continuous
`1`-cocycle.** -/
theorem cup01_mem_Z1 (m : H0 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun g => μ (m : M) (b g)) ∈ Z1 G P := by
  refine mem_Z1_iff.2 ⟨(continuous_pairingLeft μ hequiv hμ m).comp (mem_Z1_iff.1 hb).1,
    fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (m : M) (b (g * h)) = g • μ (m : M) (b h) + μ (m : M) (b g)
  rw [(mem_Z1_iff.1 hb).2 g h, map_add, pairingLeft_smul μ hequiv m g (b h)]

/-- **The `(0,1)` cup product**, `(m ⌣ b) g = μ m (b g)`. For invariant `m` this is the
coefficient map induced by `μ m`. -/
noncomputable def explicitCup01 : H0 G M →+ H1 G N →+ H1 G P :=
  AddMonoidHom.mk'
    (fun m => explicitCoeff1 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m))
    fun m m' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z1 G P => (z : H1 G P))
          (Subtype.ext (funext fun g => by simp [cocyclesMap1_coe]))

/-- The `(0,1)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup01_apply (m : H0 G M) :
    explicitCup01 G M N P μ hμ hequiv m =
      explicitCoeff1 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m) :=
  (rfl)

/-- The cochain formula for the `(0,1)` cup on the class of a continuous `1`-cocycle. -/
@[simp]
theorem explicitCup01_mk (m : H0 G M) (b : Z1 G N) :
    explicitCup01 G M N P μ hμ hequiv m (b : H1 G N) =
      ((⟨fun g => μ (m : M) ((b : G → N) g), cup01_mem_Z1 G M N P μ hμ hequiv m b.2⟩ :
        Z1 G P) : H1 G P) := by
  rw [explicitCup01_apply, explicitCoeff1_mk]
  exact congrArg (fun z : Z1 G P => (z : H1 G P))
    (Subtype.ext (funext fun g => by simp [cocyclesMap1_coe]))

end CupZeroOne

section CupOneZero

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

omit [ContinuousSMul G M] [ContinuousSMul G P] in
/-- **The `(1,0)` cup of a continuous `1`-cocycle with an invariant element is a continuous
`1`-cocycle.** The translation factor `g •` is the one the general inhomogeneous formula carries;
it disappears only because `n` is invariant. -/
theorem cup10_mem_Z1 {a : G → M} (ha : a ∈ Z1 G M) (n : H0 G N) :
    (fun g => μ (a g) (g • (n : N))) ∈ Z1 G P := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hadd : ∀ x y : M, μ (x + y) (n : N) = μ x (n : N) + μ y (n : N) := fun x y => by simp
  simp only [hn]
  refine mem_Z1_iff.2 ⟨(continuous_pairingRight μ hequiv hμ n).comp (mem_Z1_iff.1 ha).1,
    fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (a (g * h)) (n : N) = g • μ (a h) (n : N) + μ (a g) (n : N)
  rw [(mem_Z1_iff.1 ha).2 g h, hadd, pairingRight_smul μ hequiv n g (a h)]

/-- **The `(1,0)` cup product**, `(a ⌣ n) g = μ (a g) (g • n)`. For invariant `n` this is the
coefficient map induced by `m ↦ μ m n`. -/
noncomputable def explicitCup10 : H1 G M →+ H0 G N →+ H1 G P :=
  AddMonoidHom.flip <| AddMonoidHom.mk'
    (fun n => explicitCoeff1 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n))
    fun n n' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z1 G P => (z : H1 G P))
          (Subtype.ext (funext fun g => by simp [cocyclesMap1_coe]))

/-- The `(1,0)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup10_apply (a : H1 G M) (n : H0 G N) :
    explicitCup10 G M N P μ hμ hequiv a n =
      explicitCoeff1 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n) a :=
  (rfl)

/-- The cochain formula for the `(1,0)` cup on the class of a continuous `1`-cocycle. -/
@[simp]
theorem explicitCup10_mk (a : Z1 G M) (n : H0 G N) :
    explicitCup10 G M N P μ hμ hequiv (a : H1 G M) n =
      ((⟨fun g => μ ((a : G → M) g) (g • (n : N)), cup10_mem_Z1 G M N P μ hμ hequiv a.2 n⟩ :
        Z1 G P) : H1 G P) := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  rw [explicitCup10_apply, explicitCoeff1_mk]
  exact congrArg (fun z : Z1 G P => (z : H1 G P))
    (Subtype.ext (funext fun g => by simp [cocyclesMap1_coe, hn g]))

end CupOneZero

section CupZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

omit [ContinuousMul G] [ContinuousSMul G N] [ContinuousSMul G P] in
/-- **The `(0,2)` cup of an invariant element with a continuous `2`-cocycle is a continuous
`2`-cocycle.** -/
theorem cup02_mem_Z2 (m : H0 G M) {b : G × G → N} (hb : b ∈ Z2 G N) :
    (fun q : G × G => μ (m : M) (b q)) ∈ Z2 G P := by
  refine mem_Z2_iff.2 ⟨(continuous_pairingLeft μ hequiv hμ m).comp (mem_Z2_iff.1 hb).1,
    fun g h j => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (m : M) (b (g * h, j)) + μ (m : M) (b (g, h)) =
    g • μ (m : M) (b (h, j)) + μ (m : M) (b (g, h * j))
  rw [← pairingLeft_smul μ hequiv m g (b (h, j)), ← map_add, ← map_add,
    (mem_Z2_iff.1 hb).2 g h j]

/-- **The `(0,2)` cup product**, `(m ⌣ b) (g, h) = μ m (b (g, h))`. -/
noncomputable def explicitCup02 : H0 G M →+ H2 G N →+ H2 G P :=
  AddMonoidHom.mk'
    (fun m => explicitCoeff2 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m))
    fun m m' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff2_mk, explicitCoeff2_mk, explicitCoeff2_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z2 G P => (z : H2 G P))
          (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [cocyclesMap2_coe]))

/-- The `(0,2)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup02_apply (m : H0 G M) :
    explicitCup02 G M N P μ hμ hequiv m =
      explicitCoeff2 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m) :=
  (rfl)

/-- The cochain formula for the `(0,2)` cup on the class of a continuous `2`-cocycle. -/
@[simp]
theorem explicitCup02_mk (m : H0 G M) (b : Z2 G N) :
    explicitCup02 G M N P μ hμ hequiv m (b : H2 G N) =
      ((⟨fun q : G × G => μ (m : M) ((b : G × G → N) q),
        cup02_mem_Z2 G M N P μ hμ hequiv m b.2⟩ : Z2 G P) : H2 G P) := by
  rw [explicitCup02_apply, explicitCoeff2_mk]
  exact congrArg (fun z : Z2 G P => (z : H2 G P))
    (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [cocyclesMap2_coe]))

end CupZeroTwo

section CupTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G P] in
/-- **The `(2,0)` cup of a continuous `2`-cocycle with an invariant element is a continuous
`2`-cocycle.** -/
theorem cup20_mem_Z2 {a : G × G → M} (ha : a ∈ Z2 G M) (n : H0 G N) :
    (fun q : G × G => μ (a q) ((q.1 * q.2) • (n : N))) ∈ Z2 G P := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  have hadd : ∀ x y : M, μ (x + y) (n : N) = μ x (n : N) + μ y (n : N) := fun x y => by simp
  simp only [hn]
  refine mem_Z2_iff.2 ⟨(continuous_pairingRight μ hequiv hμ n).comp (mem_Z2_iff.1 ha).1,
    fun g h j => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (a (g * h, j)) (n : N) + μ (a (g, h)) (n : N) =
    g • μ (a (h, j)) (n : N) + μ (a (g, h * j)) (n : N)
  rw [← pairingRight_smul μ hequiv n g (a (h, j)), ← hadd, ← hadd, (mem_Z2_iff.1 ha).2 g h j]

/-- **The `(2,0)` cup product**, `(a ⌣ n) (g, h) = μ (a (g, h)) ((g * h) • n)`. This is the last
of the six shapes: no explicit cup goes above total degree `2`. -/
noncomputable def explicitCup20 : H2 G M →+ H0 G N →+ H2 G P :=
  AddMonoidHom.flip <| AddMonoidHom.mk'
    (fun n => explicitCoeff2 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n))
    fun n n' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff2_mk, explicitCoeff2_mk, explicitCoeff2_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z2 G P => (z : H2 G P))
          (Subtype.ext (funext fun q => by obtain ⟨g, h⟩ := q; simp [cocyclesMap2_coe]))

/-- The `(2,0)` cup is the coefficient map induced by the pairing at an invariant element. -/
theorem explicitCup20_apply (a : H2 G M) (n : H0 G N) :
    explicitCup20 G M N P μ hμ hequiv a n =
      explicitCoeff2 G M (pairingRight μ hequiv n) (continuous_pairingRight μ hequiv hμ n) a :=
  (rfl)

/-- The cochain formula for the `(2,0)` cup on the class of a continuous `2`-cocycle. -/
@[simp]
theorem explicitCup20_mk (a : Z2 G M) (n : H0 G N) :
    explicitCup20 G M N P μ hμ hequiv (a : H2 G M) n =
      ((⟨fun q : G × G => μ ((a : G × G → M) q) ((q.1 * q.2) • (n : N)),
        cup20_mem_Z2 G M N P μ hμ hequiv a.2 n⟩ : Z2 G P) : H2 G P) := by
  have hn : ∀ g : G, g • (n : N) = (n : N) := n.2
  rw [explicitCup20_apply, explicitCoeff2_mk]
  exact congrArg (fun z : Z2 G P => (z : H2 G P))
    (Subtype.ext (funext fun q => by
      obtain ⟨g, h⟩ := q; simp [cocyclesMap2_coe, hn (g * h)]))

end CupTwoZero

section CupOneOne

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G P] in
/-- **The `(1,1)` cup of two continuous `1`-cocycles is a continuous `2`-cocycle.** This is the
cochain-level heart of the only shape that is not a coefficient map: the translation factor `g •`
on the second cocycle is what turns the two `1`-cocycle identities into the `2`-cocycle
identity. -/
theorem cup11_mem_Z2 {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ Z2 G P := by
  obtain ⟨hac, ha1⟩ := mem_Z1_iff.1 ha
  obtain ⟨hbc, hb1⟩ := mem_Z1_iff.1 hb
  refine mem_Z2_iff.2 ⟨hμ.comp ((hac.comp continuous_fst).prodMk
    (continuous_fst.smul (hbc.comp continuous_snd))), fun g h j => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change μ (a (g * h)) ((g * h) • b j) + μ (a g) (g • b h) =
    g • μ (a h) (h • b j) + μ (a g) (g • b (h * j))
  simp only [ha1 g h, hb1 h j, map_add, AddMonoidHom.add_apply, smul_add, mul_smul, hequiv]
  abel

omit [ContinuousMul G] [IsTopologicalAddGroup M] [ContinuousSMul G M] [ContinuousSMul G N]
  [ContinuousSMul G P] in
/-- **The `(1,1)` cup descends through coboundaries in the first variable**: if `a = d⁰ m` then
`a ⌣ b = d¹ (x ↦ μ m (b x))`. -/
theorem cup11_mem_B2_left {a : G → M} (ha : a ∈ B1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ B2 G P := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 ha
  obtain ⟨hbc, hb1⟩ := mem_Z1_iff.1 hb
  refine mem_B2_iff'.2 ⟨fun x => μ m (b x), hμ.comp (continuous_const.prodMk hbc),
    fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change g • μ m (b h) - μ m (b (g * h)) + μ m (b g) = μ (a g) (g • b h)
  rw [← hm g, hb1 g h]
  simp only [map_add, map_sub, AddMonoidHom.sub_apply, hequiv]
  abel

omit [ContinuousMul G] [ContinuousSMul G M] [IsTopologicalAddGroup N] [ContinuousSMul G P] in
/-- **The `(1,1)` cup descends through coboundaries in the second variable**: if `b = d⁰ n` then
`a ⌣ b = d¹ (x ↦ -μ (a x) (x • n))`. -/
theorem cup11_mem_B2_right {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ B1 G N) :
    (fun q : G × G => μ (a q.1) (q.1 • b q.2)) ∈ B2 G P := by
  obtain ⟨n, hn⟩ := mem_B1_iff.1 hb
  obtain ⟨hac, ha1⟩ := mem_Z1_iff.1 ha
  refine mem_B2_iff'.2 ⟨fun x => -μ (a x) (x • n),
    (hμ.comp (hac.prodMk (continuous_id.smul continuous_const))).neg, fun g h => ?_⟩
  -- beta-reduce the cup cochain; see the implementation notes.
  change g • -μ (a h) (h • n) - -μ (a (g * h)) ((g * h) • n) + -μ (a g) (g • n) =
    μ (a g) (g • b h)
  rw [← hn h, ha1 g h]
  simp only [mul_smul, smul_sub, smul_neg, map_add, map_sub, AddMonoidHom.add_apply, hequiv]
  abel

/-- The `(1,1)` cup of two continuous `1`-cocycles, as a continuous `2`-cocycle. -/
private noncomputable def cup11Cocycle (a : Z1 G M) (b : Z1 G N) : Z2 G P :=
  ⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
    cup11_mem_Z2 G M N P μ hμ hequiv a.2 b.2⟩

omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G P] in
/-- The `(1,1)` cup on cocycles is additive in the first variable. -/
private theorem cup11Cocycle_add_left (a a' : Z1 G M) (b : Z1 G N) :
    cup11Cocycle G M N P μ hμ hequiv (a + a') b =
      cup11Cocycle G M N P μ hμ hequiv a b + cup11Cocycle G M N P μ hμ hequiv a' b :=
  Subtype.ext (funext fun q => by simp [cup11Cocycle])

omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G P] in
/-- The `(1,1)` cup on cocycles is additive in the second variable. -/
private theorem cup11Cocycle_add_right (a : Z1 G M) (b b' : Z1 G N) :
    cup11Cocycle G M N P μ hμ hequiv a (b + b') =
      cup11Cocycle G M N P μ hμ hequiv a b + cup11Cocycle G M N P μ hμ hequiv a b' :=
  Subtype.ext (funext fun q => by simp [cup11Cocycle, smul_add])

omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G P] in
/-- The `(1,1)` cup on cocycles vanishes on the zero cocycle. -/
private theorem cup11Cocycle_zero_left (b : Z1 G N) :
    cup11Cocycle G M N P μ hμ hequiv 0 b = 0 :=
  Subtype.ext (funext fun q => by simp [cup11Cocycle])

/-- The `(1,1)` cup on cocycles, biadditive by construction. -/
private noncomputable def cocyclesCup11 : Z1 G M →+ Z1 G N →+ Z2 G P where
  toFun a :=
    { toFun := fun b => cup11Cocycle G M N P μ hμ hequiv a b
      map_zero' := Subtype.ext (funext fun q => by simp [cup11Cocycle])
      map_add' := cup11Cocycle_add_right G M N P μ hμ hequiv a }
  map_zero' := AddMonoidHom.ext fun b => cup11Cocycle_zero_left G M N P μ hμ hequiv b
  map_add' a a' := AddMonoidHom.ext fun b => cup11Cocycle_add_left G M N P μ hμ hequiv a a' b

/-- **The `(1,1)` cup product**, the descent of the cochain formula
`(a ⌣ b) (g, h) = μ (a g) (g • b h)`. This is the only one of the six shapes that is not a
coefficient map. -/
noncomputable def explicitCup11 : H1 G M →+ H1 G N →+ H2 G P :=
  QuotientAddGroup.lift _
    { toFun := fun a =>
        QuotientAddGroup.lift _
          ((QuotientAddGroup.mk' ((B2 G P).addSubgroupOf (Z2 G P))).comp
            (cocyclesCup11 G M N P μ hμ hequiv a))
          fun b hb => (QuotientAddGroup.eq_zero_iff _).2 <| AddSubgroup.mem_addSubgroupOf.2 <|
            cup11_mem_B2_right G M N P μ hμ hequiv a.2 (AddSubgroup.mem_addSubgroupOf.1 hb)
      map_zero' := AddMonoidHom.ext fun x => by
        induction x using QuotientAddGroup.induction_on with
        | _ b =>
          exact congrArg (fun z : Z2 G P => (z : H2 G P))
            (cup11Cocycle_zero_left G M N P μ hμ hequiv b)
      map_add' := fun a a' => AddMonoidHom.ext fun x => by
        induction x using QuotientAddGroup.induction_on with
        | _ b =>
          rw [AddMonoidHom.add_apply]
          exact (congrArg (fun z : Z2 G P => (z : H2 G P))
            (cup11Cocycle_add_left G M N P μ hμ hequiv a a' b)).trans
            (QuotientAddGroup.mk_add _ _ _) }
    fun a ha => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ b =>
        exact (QuotientAddGroup.eq_zero_iff _).2 <| AddSubgroup.mem_addSubgroupOf.2 <|
          cup11_mem_B2_left G M N P μ hμ hequiv (AddSubgroup.mem_addSubgroupOf.1 ha) b.2

/-- The cochain formula for the `(1,1)` cup on the classes of two continuous `1`-cocycles. -/
@[simp]
theorem explicitCup11_mk (a : Z1 G M) (b : Z1 G N) :
    explicitCup11 G M N P μ hμ hequiv (a : H1 G M) (b : H1 G N) =
      ((⟨fun q : G × G => μ ((a : G → M) q.1) (q.1 • (b : G → N) q.2),
        cup11_mem_Z2 G M N P μ hμ hequiv a.2 b.2⟩ : Z2 G P) : H2 G P) :=
  (rfl)

end CupOneOne

section CommZeroZero

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

/-- **Graded commutativity in bidegree `(0,0)`.** The sign `(-1)^{pq}` is `1`, and the two
cochains, here two elements of `P`, are literally equal. -/
theorem explicitCup00_comm (m : H0 G M) (n : H0 G N) :
    explicitCup00 G M N P μ hequiv m n =
      explicitCup00 G N M P μ.flip (equivariant_flip μ hequiv) n m :=
  Subtype.ext (by simp)

end CommZeroZero

section CommCochain

/-! The three shapes with a degree-`0` factor commute already on cochains, because a degree-`0`
class is invariant. Neither statement mentions a topology or an action on the second factor. -/

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommMonoid N]
  (P : Type uP) [AddCommMonoid P]
  (μ : M →+ N →+ P)

/-- **Graded commutativity in bidegree `(0,1)`, at cochain level.** The `(1,0)` cup of a cochain
`b` with the invariant `m` along the opposite pairing is the `(0,1)` cup of `m` with `b`: the
translation factor `g •` the `(1,0)` formula carries acts on `m`, which is invariant. -/
theorem cup01_eq_cup10_flip (m : H0 G M) (b : G → N) :
    (fun g => μ (m : M) (b g)) = fun g => μ.flip (b g) (g • (m : M)) := by
  have hm : ∀ g : G, g • (m : M) = (m : M) := m.2
  funext g
  rw [AddMonoidHom.flip_apply, hm g]

/-- **Graded commutativity in bidegree `(0,2)`, at cochain level**, the degree-`2` counterpart of
`TauCeti.ContCohomology.cup01_eq_cup10_flip`. -/
theorem cup02_eq_cup20_flip (m : H0 G M) (b : G × G → N) :
    (fun q : G × G => μ (m : M) (b q)) =
      fun q : G × G => μ.flip (b q) ((q.1 * q.2) • (m : M)) := by
  have hm : ∀ g : G, g • (m : M) = (m : M) := m.2
  funext q
  rw [AddMonoidHom.flip_apply, hm (q.1 * q.2)]

end CommCochain

section CommZeroOne

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv in
/-- **Graded commutativity in bidegree `(0,1)`.** The sign `(-1)^{pq}` is `1`, and by
`TauCeti.ContCohomology.cup01_eq_cup10_flip` the identity already holds on cochains. -/
theorem explicitCup01_eq_cup10_flip (m : H0 G M) (b : H1 G N) :
    explicitCup01 G M N P μ hμ hequiv m b =
      explicitCup10 G N M P μ.flip (continuous_flip μ hμ) (equivariant_flip μ hequiv) b m := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCup01_mk, explicitCup10_mk]
    exact congrArg (fun z : Z1 G P => (z : H1 G P))
      (Subtype.ext (cup01_eq_cup10_flip G M N P μ m (c : G → N)))

end CommZeroOne

section CommZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv in
/-- **Graded commutativity in bidegree `(0,2)`.** The sign `(-1)^{pq}` is `1`, and by
`TauCeti.ContCohomology.cup02_eq_cup20_flip` the identity already holds on cochains. -/
theorem explicitCup02_eq_cup20_flip (m : H0 G M) (b : H2 G N) :
    explicitCup02 G M N P μ hμ hequiv m b =
      explicitCup20 G N M P μ.flip (continuous_flip μ hμ) (equivariant_flip μ hequiv) b m := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCup02_mk, explicitCup20_mk]
    exact congrArg (fun z : Z2 G P => (z : H2 G P))
      (Subtype.ext (cup02_eq_cup20_flip G M N P μ m (c : G × G → N)))

end CommZeroTwo

section CommOneOne

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hequiv in
omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G N] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousSMul G P] in
/-- **The homotopy behind graded commutativity in bidegree `(1,1)`.** The two cochains
`a ⌣_μ b` and `b ⌣_{μᵒᵖ} a` need not be equal in general; their sum is the coboundary of the
`1`-cochain `g ↦ -μ (a g) (b g)`. -/
theorem cup11_add_cup11_flip_eq_d1 {a : G → M} (ha : a ∈ Z1 G M) {b : G → N} (hb : b ∈ Z1 G N) :
    ((fun q : G × G => μ (a q.1) (q.1 • b q.2)) +
        fun q : G × G => μ.flip (b q.1) (q.1 • a q.2)) =
      d1 G P fun g => -μ (a g) (b g) := by
  obtain ⟨-, ha1⟩ := mem_Z1_iff.1 ha
  obtain ⟨-, hb1⟩ := mem_Z1_iff.1 hb
  funext q
  obtain ⟨g, h⟩ := q
  simp only [Pi.add_apply, AddMonoidHom.flip_apply, d1_apply, ha1 g h, hb1 g h, map_add,
    AddMonoidHom.add_apply, smul_neg, hequiv]
  abel

include hμ hequiv in
omit [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G N] [ContinuousSMul G P] in
/-- **The sum of the two `(1,1)` cup cochains is a coboundary**, by
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`; its primitive is continuous because `μ` is
jointly continuous. -/
theorem cup11_add_cup11_flip_mem_B2 {a : G → M} (ha : a ∈ Z1 G M) {b : G → N}
    (hb : b ∈ Z1 G N) :
    ((fun q : G × G => μ (a q.1) (q.1 • b q.2)) +
      fun q : G × G => μ.flip (b q.1) (q.1 • a q.2)) ∈ B2 G P :=
  mem_B2_iff.2 ⟨fun g => -μ (a g) (b g),
    (hμ.comp ((mem_Z1_iff.1 ha).1.prodMk (mem_Z1_iff.1 hb).1)).neg,
    (cup11_add_cup11_flip_eq_d1 G M N P μ hequiv ha hb).symm⟩

include hμ hequiv in
/-- **Graded commutativity in bidegree `(1,1)`**, `a ⌣_μ b = -(b ⌣_{μᵒᵖ} a)`, the sign
`(-1)^{pq}` now being `-1`. This is an identity of classes and not of cochains: the two cochains
differ by the coboundary exhibited in
`TauCeti.ContCohomology.cup11_add_cup11_flip_eq_d1`. -/
theorem explicitCup11_eq_neg_flip (a : H1 G M) (b : H1 G N) :
    explicitCup11 G M N P μ hμ hequiv a b =
      -explicitCup11 G N M P μ.flip (continuous_flip μ hμ) (equivariant_flip μ hequiv) b a := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      rw [explicitCup11_mk, explicitCup11_mk, eq_neg_iff_add_eq_zero, ← QuotientAddGroup.mk_add,
        H2pi_eq_zero_iff]
      exact cup11_add_cup11_flip_mem_B2 G M N P μ hμ hequiv x.2 y.2

include hμ hequiv in
/-- **Graded commutativity in bidegree `(1,1)` for `2`-torsion coefficients**: when every element
of `P` is its own negative the `(1,1)` cup is symmetric on classes. This is the form the
`𝔽₂`-valued arithmetic applications use, where every sign is `1`. -/
theorem explicitCup11_comm_of_neg_eq_self (hP : ∀ x : P, -x = x) (a : H1 G M) (b : H1 G N) :
    explicitCup11 G M N P μ hμ hequiv a b =
      explicitCup11 G N M P μ.flip (continuous_flip μ hμ) (equivariant_flip μ hequiv) b a := by
  have hneg : ∀ y : H2 G P, -y = y := fun y => by
    induction y using QuotientAddGroup.induction_on with
    | _ z =>
      rw [← QuotientAddGroup.mk_neg]
      exact congrArg (fun w : Z2 G P => (w : H2 G P))
        (Subtype.ext (funext fun q => hP ((z : G × G → P) q)))
  rw [explicitCup11_eq_neg_flip G M N P μ hμ hequiv a b, hneg]

end CommOneOne

end TauCeti.ContCohomology
