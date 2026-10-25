module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenRow
public import CORALean.Global.FoldInduction

@[expose] public section

/-!
# `ConZonotope.tighten`

[1]'s Algorithm 1 ([2, Alg. 1]): the coefficient box `B∞(A,b) = {ξ | Aξ = b, ‖ξ‖∞ ≤ 1}` of a
constrained zonotope `Zc = {G,c,A,b}` is not itself a box, but every row of `Aξ = b`
tightens one further, and running every row once — the way Gauss-Jordan elimination
does — gives an interval enclosure of it. `Thm. 2`'s `E_k` and `R_{r,c}` (eq. 12) are
what a single pass buys.

The paper's own outer refinement — running Algorithm 1 again on its own output — is a
separate procedure `Thm. 2` does not ask for; it is `tightenER`, which also returns `R`.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset

## Output
* the tightened coefficient box

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica, 2022.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the interval enclosure of the feasible coefficient box `B∞(A,b)`, one
coordinate tightened at a time by every row of `Aξ = b` in turn. -/
noncomputable def ConZonotope.tighten {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc) :
    Interval (Vec ℝ ng) :=
  -- 1. start from the unit box, `E_j ← [-1, 1]`
  let E₀ : Interval (Vec ℝ ng) := ⟨fun _ => -1, fun _ => 1⟩
  -- 2. lines 2-10: tighten every coordinate by row `i` of `Aξ = b`, for `i ← 1, …, nc` in turn
  Fin.foldl nc (fun E i => ConZonotope.tightenRow A b i E) E₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
