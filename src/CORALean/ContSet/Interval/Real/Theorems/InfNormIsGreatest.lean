module

public import CORALean.ContSet.Interval.Real.Operations.InfNorm
public import CORALean.ContSet.Interval.Real.Theorems.MatNormIsGreatest

@[expose] public section

/-!
# `Interval.infNorm` is the maximum infinity norm over the box

`norm(abs(A), Inf)` is `norm(|center| + rad, Inf)` on a nonempty box (`abs_center_add_radius`),
so this is `matNorm_isGreatest` at the type `Inf`.

## Inputs
* `A` – interval matrix

## Hypotheses
* `hA` – `A` has ordered bounds

## Conclusion
* the infinity norm of the box is the greatest member norm
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The maximum of the infinity norm over a nonempty box is `infNorm`, and is attained. -/
theorem Interval.infNorm_isGreatest (A : Interval (Mat ℝ m n))
    (hA : ∀ r s, A.inf r s ≤ A.sup r s) :
    IsGreatest ((fun M : Mat ℝ m n => Interval.NormType.inf.eval M) '' A.construct)
      A.infNorm := by -- --- PROOF ---
  have h : A.matNorm .inf = A.infNorm := by
    unfold Interval.matNorm Interval.infNorm
    show Interval.NormType.eval .inf (fun i j => |A.center i j| + A.radius i j) = _
    exact congrArg _ (funext fun i => funext fun j => Interval.abs_center_add_radius A hA i j)
  rw [← h]
  exact Interval.matNorm_isGreatest .inf A hA

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
