module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeffER

@[expose] public section

/-!
# `ConZonotope.tightenPassER`

[1, Alg. 1 (R)], [2, Alg. 1], lines 2-10 from a given state `(E, R)`: every row `i = 1..n_c` in
turn, and within a row every column `j = 1..n_g`, the printed double loop. Started from
line 1's `E = [-1, 1]`, `R = [-∞, +∞]` it is the algorithm itself (`tightenER` at `0`);
started from its own output it is the algorithm "applied iteratively to further refine E".

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset
* `S` – current box and running bounds

## Output
* the state after tightening every row and coefficient once

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica, 2022.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 2-10: one pass over every row and, within it, every column. -/
noncomputable def ConZonotope.tightenPassER {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))) :
    Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal)) :=
  Fin.foldl nc (fun S i =>                                                   -- 9-10: i ← 1..nc
    Fin.foldl ng (fun S j => ConZonotope.tightenCoeffER A b i j S) S) S      -- 2, 6-8: j ← 1..ng

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
