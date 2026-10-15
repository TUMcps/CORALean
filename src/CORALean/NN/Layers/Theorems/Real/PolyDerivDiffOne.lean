module

public import CORALean.NN.Layers.Definitions.PolyDerivBound
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# At order 1 the derivative bound is the bracket

ℝ-only, as the bound is: the radius vanishes and the center is the slope, so this is the bracket
`Relaxation.ofDeriv` works with and no precision is lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem polyDerivDiff_one (lo hi : ℝ) (c : Fin 2 → ℝ) (l u : ℝ) :
    polyDerivDiff lo hi (polyDerivCenter c) (polyDerivRadius c l u)
      = max |lo - c 1| |hi - c 1| := by -- --- PROOF ---
  have hctr : polyDerivCenter c = c 1 := by
    show (∑ i : Fin 2, if (i : ℕ) = 1 then c i else 0) = c 1
    rw [Fin.sum_univ_two]
    norm_num
  have hrad : polyDerivRadius c l u = 0 := by
    show (∑ i : Fin 2, if (i : ℕ) = 1 then 0
      else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)) = 0
    rw [Fin.sum_univ_two]
    norm_num
  show max |lo - polyDerivCenter c - polyDerivRadius c l u|
      |hi - polyDerivCenter c + polyDerivRadius c l u| = _
  rw [hctr, hrad, sub_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
