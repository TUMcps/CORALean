module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ConsistentSet
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The exact uncertain set of a measured run

[1, Def. 2]: `X_k = (A X_{k-1} ⊕ W) ∩ X_{y_k}` for `k ≥ 1`, from `X_0`, with `X_{y_k}` the
consistent set of [1, Def. 1]. The system is [1, Eq. 1], `x_{k+1} = A x_k + ω_k`,
`y_k = C x_k + v_k`, `ω_k ∈ W`, `v_k ∈ V`, at one matrix `A`: the paper's `A` is unknown
but constant. The paper's claim that this is exactly the set of states consistent with the
measurements is `exactUncertainSet_eq`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X_0`, and `X_k = (A X_{k-1} ⊕ W) ∩ X_{y_k}`. -/
def LinearSysDT.exactUncertainSet (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (V : Set (Vec ℝ p)) (X₀ W : Set (Vec ℝ n)) (y : ℕ → Vec ℝ p) : ℕ → Set (Vec ℝ n)
  | 0 => X₀
  | k + 1 => (mulVecLin sys.A '' sys.exactUncertainSet C V X₀ W y k + W) ∩
      LinearSysDT.consistentSet C V (y (k + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
