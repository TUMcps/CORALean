module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenPassER

@[expose] public section

/-!
# `ConZonotope.tightenER`

[1, Alg. 1 (R)], [1, Alg. 1 (iteration)], [2, Alg. 1] with both outputs, `E` and `R`, run `k + 1`
times: line 1's `E = [-1, 1]`, `R = [-∞, +∞]`, then the pass of lines 2-10, then the pass again on
its own output `k` more times. At `k = 0` it is the algorithm as listed; [2] says it "can be applied
iteratively to further refine E", and [1] repeats that, which is `k > 0`.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset
* `k` – number of extra passes

## Output
* the tightened box and the running bounds after k + 1 passes

## References

* [1] [V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica,
      2022.](../../../../../../references/2022/raghuraman-koeln-constrained-zonotopes.md)
* [2] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1 (R)], [1, Alg. 1 (iteration)] with `E` and `R`, applied `k + 1` times. -/
noncomputable def ConZonotope.tightenER {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc) (k : ℕ) :
    Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal)) :=
  -- 1. start from the unit box, `E_j ← [-1, 1]`
  let E₀ : Interval (Vec ℝ ng) := ⟨fun _ => -1, fun _ => 1⟩
  -- 1. and from the whole line, `R_j ← [-∞, ∞]`
  let R₀ : (Fin ng → EReal) × (Fin ng → EReal) := (fun _ => ⊥, fun _ => ⊤)
  -- 2. lines 2-10, the pass over every row, run `k + 1` times on its own output
  (ConZonotope.tightenPassER A b)^[k + 1] (E₀, R₀)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
