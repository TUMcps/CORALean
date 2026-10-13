import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# Range bounding

[1, Def. 5]: `bound(f, X) ⊇ [min_{x∈X} f(x), max_{x∈X} f(x)]` — an interval `[l, u]` that
contains every value `f` takes on `X`, which is that inclusion read pointwise, without asking
the minimum and maximum to exist. How it is computed (interval arithmetic, Taylor models) is
left open, as in [1]; [1, Sec. 4.1] decides with it whether a set leaves an invariant or meets
a guard.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[l, u] ⊇ f(X)`. -/
def IsRangeBound (f : Vec ℝ n → ℝ) (X : Set (Vec ℝ n)) (l u : ℝ) : Prop :=
  ∀ x ∈ X, l ≤ f x ∧ f x ≤ u

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
