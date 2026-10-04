import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Matrix.Mul

/-!
# The reachable set of the Luenberger estimation error

Eq. 24 of [1, Thm. 2]: for `x_{k+1} = A x_k + B u_k + E w_k`, `y_k = C x_k + F v_k` and the observer
`x̂_{k+1} = A x̂_k + B u_k + L(y_k - C x̂_k)` started at `x̂_0 = p₀`, the error `e_k = x_k - x̂_k`
ranges over
`Ω_k = (A - LC)ᵏ Ω₀ ⊕ ⨁_{i<k} (A - LC)ⁱ E W ⊕ ⨁_{i<k} (A - LC)ⁱ (-LF) V`, `Ω₀ = ⟨0, H₀⟩`,
the initial set `X₀ = ⟨p₀, H₀⟩` moved to the origin. The input and the measurements do not
enter: the error dynamics `e_{k+1} = (A - LC) e_k + E w_k - L F v_k` [1, Eq. 14] is free of them.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ω_k`, Eq. 24 of [1, Thm. 2]. -/
def LinearSysDT.reachErrorSet (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ nw))
    (V : Zonotope (Vec ℝ nv)) (k : ℕ) : Set (Vec ℝ n) :=
  (((A - L * C) ^ k) *ᵥ ·) '' (⟨X₀.h, 0, X₀.G⟩ : Zonotope (Vec ℝ n)).construct +
    ∑ i ∈ Finset.range k, (((A - L * C) ^ i * E) *ᵥ ·) '' W.construct +
    ∑ i ∈ Finset.range k, (((A - L * C) ^ i * -(L * F)) *ᵥ ·) '' V.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
