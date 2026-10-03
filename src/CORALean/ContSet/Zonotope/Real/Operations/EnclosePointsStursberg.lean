import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Mul

/-!
# `Zonotope.enclosePointsStursberg`

CORA's `@zonotope/enclosePoints.m` at `method = 'stursberg'`, `aux_enclosePointsStursberg`: the
points are centred on their mean, rotated by `Uᵀ`, boxed per rotated coordinate (`m1` the
maximum, `m2` the minimum), and the box is rotated back: centre `mean + U (m1 + m2) / 2`,
generators `(m1ᵢ - m2ᵢ) / 2 · U[:, i]`.

CORA takes `U` from `svd(cov(sampleMatrix'))`, the principal axes of the sample. A singular value
decomposition has no algorithm in this library, so `U` is an argument here: the result is the one
CORA builds for that `U`, and the enclosure holds for every orthogonal `U`
(`enclosePointsStursberg_mem`), the SVD only deciding how tight the box is. The points are the
columns of CORA's `points`, and at least one is required (`NeZero N`), as `nonempty` demands.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclosePoints(points, 'stursberg')` for a given basis `U`. -/
noncomputable def Zonotope.enclosePointsStursberg [NeZero N] (pts : Fin N → Vec ℝ n)
    (U : Mat ℝ n n) : Zonotope (Vec ℝ n) :=
  let mean := (1 / (N : ℝ)) • ∑ j, pts j
  let sampleMatrix := fun j => pts j - mean
  let orientedMatrix := fun j => Uᵀ *ᵥ sampleMatrix j
  let m1 := fun i => Finset.univ.sup' Finset.univ_nonempty fun j => orientedMatrix j i
  let m2 := fun i => Finset.univ.inf' Finset.univ_nonempty fun j => orientedMatrix j i
  let c := mean + U *ᵥ ((1 / 2 : ℝ) • (m1 + m2))
  let G := fun i : Fin n => ((m1 i - m2 i) * (1 / 2 : ℝ)) • (fun r => U r i)
  ⟨n, c, G⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
