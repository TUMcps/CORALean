module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop

@[expose] public section

/-!
# The first steps of the inner algorithm are a run of their own

`k + j` steps of [1, Alg. 1]'s loop are `k` steps followed by `j` steps from where those ended.
So the time-point set `R̂(t_k)` that a run of `ω ≥ k` steps passes through is the first
component of `innerMinkDiffLoop … k X₀ ∅`, and a statement about that is one about every
time-point set the algorithm computes.

## Inputs
* `ops` – set operations
* `f` – autonomous field
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound per remainder loop
* `k` – first step count
* `j` – second step count
* `Rtk` – start set
* `Rτ` – accumulated time-interval sets

## Hypotheses
* none

## Conclusion
* steps added together equal the steps run one after another

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k + j` steps of [1, Alg. 1] are `k` steps, then `j` more. -/
theorem NonlinearSys.innerMinkDiffLoop_add (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ) (fuel k j : ℕ) (Rtk Rτ : Set (Vec ℝ n)) : -- --- CONCL ---
    NonlinearSys.innerMinkDiffLoop ops f Δt μ fuel (k + j) Rtk Rτ =
      (NonlinearSys.innerMinkDiffLoop ops f Δt μ fuel k Rtk Rτ).bind fun p =>
        NonlinearSys.innerMinkDiffLoop ops f Δt μ fuel j p.1 p.2 := by -- --- PROOF ---
  induction k generalizing Rtk Rτ with
  | zero => simp [NonlinearSys.innerMinkDiffLoop]
  | succ k ih =>
    rw [show k + 1 + j = (k + j) + 1 by omega]
    simp only [NonlinearSys.innerMinkDiffLoop, ih, Option.bind_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
