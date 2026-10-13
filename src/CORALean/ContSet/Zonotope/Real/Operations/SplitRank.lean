import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.splitRank`

The measure that picks which generator to split [1, Heuristic 3.1], first
[2, Sec. VI-A]'s `ρ_j`: `l1 j`, `l2 j` are Prop. 3.7's bounds for `Z.split j`'s two
halves, `l̄` is §3.4.4's admissible bound, and `splitRank` folds each ratio to its
worst dimension and multiplies the two — the lowest names the generator to split.

`l1`, `l2`, `l̄` are parameters: neither Prop. 3.7 nor §3.4.4's bound is
formalized here (both rows are `—`), so this reads like
`NN.Operations.RefinementRank` — a paper's ranking over what the caller has.

Nothing here is proved and nothing here can be wrong: `split_union` and
`split_intersection` hold at every `j` unconditionally, so this only ranks
generators, never whether the split stays sound.

Printed as a product (two extractions of the thesis agree); the sentence
right after needs a sum instead, since a product under `1` bounds neither
factor (`0.1 · 5 < 1`). Formalized as printed regardless.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The performance measure `ϱ_j` [1, Heuristic 3.1]: `l1 j`, `l2 j` read
against `l̄` and folded to their worst dimension, then multiplied — the
generator with the lowest `splitRank` is the one `Heuristic 3.1` picks. -/
noncomputable def Zonotope.splitRank (Z : Zonotope (Vec ℝ n)) (l1 l2 : Fin Z.h → Vec ℝ n)
    (lBar : Vec ℝ n) (j : Fin Z.h) : ℝ :=
  (Finset.univ.fold max 0 fun i => l1 j i / lBar i) *
    (Finset.univ.fold max 0 fun i => l2 j i / lBar i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
