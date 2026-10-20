module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The reachable set of the Luenberger estimation error

Eq. 24 of [1, Thm. 2]: for `x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k` and the observer
`x̂_{k+1} = A x̂_k + B u_k + L(y_k - C x̂_k)` started at `x̂_0 = p₀`, the error `e_k = x_k - x̂_k`
ranges over
`Ω_k = (A - LC)ᵏ Ω₀ ⊕ ⨁_{i<k} (A - LC)ⁱ E W ⊕ ⨁_{i<k} (A - LC)ⁱ (-LF) V`, `Ω₀ = ⟨0, H₀⟩`,
the initial set `X₀ = ⟨p₀, H₀⟩` moved to the origin. The input and the measurements do not
enter: the error dynamics `e_{k+1} = (A - LC) e_k + E w_k - L F v_k` [1, Eq. 14] is free of them.

## Inputs
* `sys` – system
* `L` – observer gain
* `X₀` – initial error zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `k` – step

## Output
* the estimation error set at step `k`

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ω_k`, Eq. 24 of [1, Thm. 2]. -/
def LinearSysDT.reachErrorSet (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q) (X₀ : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ sys.r))
    (V : Zonotope (Vec ℝ sys.s)) (k : ℕ) : Set (Vec ℝ n) :=
  (((sys.A - L * sys.C) ^ k) *ᵥ ·) '' (⟨X₀.h, 0, X₀.G⟩ : Zonotope (Vec ℝ n)).construct +
    ∑ i ∈ Finset.range k, (((sys.A - L * sys.C) ^ i * sys.E) *ᵥ ·) '' W.construct +
    ∑ i ∈ Finset.range k, (((sys.A - L * sys.C) ^ i * -(L * sys.F)) *ᵥ ·) '' V.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
