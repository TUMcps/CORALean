module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Ellipsoid.enclosePointsCov`

CORA's `@ellipsoid/enclosePoints.m` at `method = 'cov'` (the default), for points that span the
whole space (`n_nd = n`, so no projection to a subspace and `n_d = 0`): the points are centered
on their mean `c`, rotated by `T'` (`T` from `svd(points)`), the covariance of the result gives a
basis `U` (`svd(C)`), and in the rotated coordinates `orientedMatrix = U' * points` the ellipsoid
is `diag(nt²) * maxDist`, `nt = max([m1, m2], [], 2)` the larger of the per-coordinate extremes
and `maxDist` the largest `Σᵢ (orientedMatrix(i,j) / ntᵢ)²` over the points, then rotated back,
`E = T * (U * E) + c`.

A singular value decomposition has no algorithm in this library, so `T` and `U` are arguments (as
for `Zonotope.enclosePointsStursberg`): the result is the one CORA builds for those matrices, and
the enclosure holds for every orthogonal pair, the SVDs only deciding how tight it is. The points
are the columns of CORA's `points`, and at least one is required (`NeZero N`). The shape `B =
diag(nt²) * maxDist` is written `D Dᵀ` with `D = diag(nt · sqrt maxDist)`, the same matrix and
positive semi-definite on sight, and the rotation `T * (U * E)` is `(T U) B (T U)ᵀ`. The branches
`n_nd = 0` (empty), `n_nd = 1` (an interval) and `n_nd < n` (a projection to the subspace and back)
and the SDP method `'min-vol'` are not formalized.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `maxDist = max_j Σᵢ (orientedMatrix(i,j) / ntᵢ)²`. -/
noncomputable def Ellipsoid.aux_enclosePointsMaxDist [NeZero N] (O : Fin N → Vec ℝ n)
    (nt : Vec ℝ n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => ∑ i, (O j i / nt i) ^ 2

/-- `nt = max([m1, m2], [], 2)`, with `m1` and `m2` the largest and smallest rotated coordinates. -/
noncomputable def Ellipsoid.aux_enclosePointsNt [NeZero N] (O : Fin N → Vec ℝ n) : Vec ℝ n :=
  let m1 := fun i => Finset.univ.sup' Finset.univ_nonempty fun j => O j i
  let m2 := fun i => Finset.univ.inf' Finset.univ_nonempty fun j => O j i
  let nt := fun i => max (m1 i) (m2 i)
  nt

/-- `orientedMatrix = U' * (T' * (points - c))`, one column per point. -/
noncomputable def Ellipsoid.aux_enclosePointsOriented [NeZero N] (pts : Fin N → Vec ℝ n)
    (T U : Mat ℝ n n) : Fin N → Vec ℝ n :=
  let c := (1 / (N : ℝ)) • ∑ j, pts j
  let points := fun j => pts j - c
  let pointsT := fun j => Tᵀ *ᵥ points j
  let orientedMatrix := fun j => Uᵀ *ᵥ pointsT j
  orientedMatrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclosePoints(points, 'cov')` for points spanning `ℝⁿ`, given `T` and `U`. -/
noncomputable def Ellipsoid.enclosePointsCov [NeZero N] (pts : Fin N → Vec ℝ n)
    (T U : Mat ℝ n n) : Ellipsoid n :=
  let c := (1 / (N : ℝ)) • ∑ j, pts j
  let orientedMatrix := Ellipsoid.aux_enclosePointsOriented pts T U
  let nt := Ellipsoid.aux_enclosePointsNt orientedMatrix
  let maxDist := Ellipsoid.aux_enclosePointsMaxDist orientedMatrix nt
  -- `B = diag(nt²) * maxDist`, as `D Dᵀ` with `D = diag(nt · sqrt maxDist)`
  let D := (Matrix.diagonal fun i => nt i * Real.sqrt maxDist : Mat ℝ n n)
  -- `E = T * (U * E) + c`: the shape `(T U) B (T U)ᵀ`
  let TUD := T * U * D
  ⟨TUD * TUDᵀ, c, by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose TUD⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
