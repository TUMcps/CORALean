module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Range bounding

[1, Def. 5]: `bound(f, X) ⊇ [min_{x∈X} f(x), max_{x∈X} f(x)]` — an interval `[l, u]` that
contains every value `f` takes on `X`, which is that inclusion read pointwise, without asking
the minimum and maximum to exist. How it is computed (interval arithmetic, Taylor models) is
left open, as in [1]; [1, Sec. 4.1] decides with it whether a set leaves an invariant or meets
a guard.

## Inputs
* `f` – function
* `X` – set
* `l` – lower bound
* `u` – upper bound

## Output
* `[l, u]` contains the range of `f` on `X`

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
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
