import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotope
import CORALean.ContSet.Zonotope.Real.Operations.SegmentLength

/-!
# `Zonotope.enclosePointsMaiga`

CORA's `@zonotope/enclosePoints.m` at `method = 'maiga'` (the default), `aux_enclosePointsMaiga`,
after [1, Alg. 5]: run `cloud2zonotope` with `s₁ = n` rounds for each of
`ratio = 1/100, ..., 100/100` and keep the zonotope of least size, the size being the sum of the
squared generator entries ([1, Eq. 46]), where [1, Alg. 5] takes the volume; the first of equal
ones. The principal direction `svd(X)(:, 1)` has no algorithm here, so `dir` is an argument and the
result is CORA's for that `dir`; the enclosure holds for every `dir` (`enclosePointsMaiga_mem`).

CORA never tests `s₂`; here `s₂ = 0`, which only skips the rounds after the cloud has collapsed to a
point, whose generators are `0`.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclosePoints(points, 'maiga')` for a given principal-direction oracle `dir`. -/
noncomputable def Zonotope.enclosePointsMaiga [NeZero N] (dir : (Fin N → Vec ℝ n) → Vec ℝ n)
    (pts : Fin N → Vec ℝ n) : Zonotope (Vec ℝ n) :=
  let Zopt := Zonotope.cloud2zonotope dir (1 / 100) n 0 pts
  (List.range' 2 99).foldl
    (fun Zopt (i : ℕ) =>
      let Z := Zonotope.cloud2zonotope dir ((i : ℝ) / 100) n 0 pts
      if Z.segmentLength < Zopt.segmentLength then Z else Zopt)
    Zopt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
