module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop

@[expose] public section

/-!
# The first steps of the inner algorithm are a run of their own

`k + j` steps of [1, Alg. 1]'s loop are `k` steps followed by `j` steps from where those ended.
So the time-point set `R̂(t_k)` that a run of `ω ≥ k` steps passes through is the first
component of `innerMinkDiffLoop … k X₀ ∅`, and a statement about that is one about every
time-point set the algorithm computes.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
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
    (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ) (fuel k j : ℕ) (Rtk Rτ : Set (Vec ℝ n)) :
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
