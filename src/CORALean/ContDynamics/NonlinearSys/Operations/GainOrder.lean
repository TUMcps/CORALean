module

public import CORALean.ContDynamics.NonlinearSys.Operations.GainOrderDim

@[expose] public section

/-!
# The gain order of a set-based solver

`[1, Def. 6]`: the gain order of the method is the smallest of its dimensions'
gain orders, so that `φ(h;δ) ≤ δ^{q+1}` holds in every dimension at once.

`ℕ∞` and not `ℕ` because `⊤` is a value the definition needs and not a failure
case: `[1, Def. 6]` reads `q = ∞` as the method committing no abstraction error
at all, which is `gainOrder_eq_top_iff`.

## Inputs
* `q` – orders of the coefficients
* `a` – leading vectors of the coefficients

## Output
* the smallest gain order over the dimensions

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `q := minᵢ qᵢ`, the gain order of the method. -/
noncomputable def gainOrder (q : ℕ → Fin n → ℕ∞) (a : ℕ → Fin n → Vec ℝ m) : ℕ∞ :=
  ⨅ i, gainOrderDim q a i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
