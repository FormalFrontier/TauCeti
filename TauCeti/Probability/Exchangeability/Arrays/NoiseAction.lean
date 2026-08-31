/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover

/-!
# The noise action for Aldous--Hoover codings

The invariance proofs for the Aldous--Hoover codings reindex the independent noise coordinates.
The public action interface names those reindexings and records their pathwise effect on the coded
array.  The separate action permutes the row and column vertex families independently, while the
joint action uses one permutation on both vertex coordinates and on the unordered-pair cell family.

The resulting identities are the reusable symmetry interface for the converse representation:
they expose the exact measurable change of noise variables behind the law-level exchangeability
theorems in `Arrays.AldousHoover`, without identifying a coding function for an arbitrary
exchangeable array.  In particular, the cell action in the joint case is `Sym2.map`, so it
preserves the unordered cell shared by the two orientations of an off-diagonal entry.

## Main declarations

* `AldousHoover.separateNoiseCongr` and `AldousHoover.jointNoiseCongr` are the measurable noise
  equivalences for the two coding forms;
* `AldousHoover.separateArray_reindex` and `AldousHoover.jointArray_reindex` give their pathwise
  equivariance formulas;
* `AldousHoover.map_separateNoiseCongr_noiseMeasure` and
  `AldousHoover.map_jointNoiseCongr_noiseMeasure` record preservation of the canonical noise law.

The action interface and the law-level exchangeability results are in `Arrays.AldousHoover`; this
module provides a focused import for the common interface used by later converse constructions.

## References

* David Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.
* Olav Kallenberg, [*Probabilistic Symmetries and Invariance Principles*]
  (https://doi.org/10.1007/0-387-28836-4), Springer (2005), Chapter 7.
-/
