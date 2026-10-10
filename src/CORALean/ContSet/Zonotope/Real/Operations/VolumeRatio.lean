import CORALean.ContSet.Zonotope.Real.Operations.Project
import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Zonotope.volumeRatio`

CORA's `@zonotope/volumeRatio(Z, P, dims)` [1]: how much larger an over-approximating polytope
`P` is than the zonotope `Z`, as the mean over the `n - dims + 1` windows of `dims` consecutive
coordinates of the normalized ratio `(vol(P|window) / vol(Z|window))^(1/dims)` of the volumes of
the two projections.

`n = d + k`, `dims = d`, and the windows are indexed by `i : Fin (k + 1)`. The volumes are the
Lebesgue measures of the projected sets, in `ENNReal`: for a zonotope this is the quantity
CORA's `volume(Zproj)` computes (`Zonotope.volume` for it, as far as `volume_eq_of_h_eq` and
`volume_eq_of_rank_lt` reach), and for the polytope `HPolytope.volume`, here at the projected set
(the image of the polytope's set, which is what CORA's exact `project(P)` denotes). A zero
projected zonotope volume gives `⊤` for a positive polytope volume where CORA divides by zero and
gets `Inf`.

## References

* [1] `contSet/@zonotope/volumeRatio.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind
      the measure was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {d k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `volumeRatio(Z, P, dims)` at `dims = d` in dimension `d + k`: the mean over the
`k + 1` windows of consecutive coordinates of `(vol(P|window) / vol(Z|window))^(1/d)`. -/
noncomputable def Zonotope.volumeRatio (Z : Zonotope (Vec ℝ (d + k)))
    (P : HPolytope (Vec ℝ (d + k))) : ENNReal :=
  let projDims := fun (i : Fin (k + 1)) (j : Fin d) =>
    (⟨j + i, by omega⟩ : Fin (d + k))                                      -- dimVector + i - 1
  let volZ := fun i => MeasureTheory.volume (Z.project (projDims i)).construct   -- volume(Zproj)
  let volP := fun i =>
    MeasureTheory.volume ((LinearMap.funLeft ℝ ℝ (projDims i)) '' P.construct)   -- volume(Pproj)
  let partialRatio := fun i => (volP i / volZ i) ^ (1 / (d : ℝ))         -- (volP/volZ)^(1/dims)
  (∑ i, partialRatio i) / ((k + 1 : ℕ) : ENNReal)                        -- mean(partialRatio)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
