module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffCorrectedStep

@[expose] public section

/-!
# `innerMinkDiffCorrectedLoop`, the time steps of the corrected inner algorithm

The loop of lines 2-17 of [1, Alg. 1] as `innerMinkDiffLoop` runs it, its steps those of
`innerMinkDiffCorrectedStep`, lines 15 and 16 repaired: `k` steps, each started from the
previous step's `R̂(t_{k+1})`, returning the last time-point set and the union of the
time-interval sets `R̂(τ_k)` the steps computed on top of `Rτ` — line 18's union, accumulated
as the loop runs. `none` as soon as one step's remainder loop runs out of fuel.

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
* `f` – autonomous field
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound per remainder loop

## Output
* the last time-point set and the union of time-interval sets

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `k` steps of the corrected [1, Alg. 1] from `R̂(t_j) = Rtk`: `(R̂(t_{j+k}), Rτ ∪ ⋃ R̂(τ_i))`. -/
noncomputable def NonlinearSys.innerMinkDiffCorrectedLoop (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n)) (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ) (fuel : ℕ) :
    ℕ → Set (Vec ℝ n) → Set (Vec ℝ n) → Option (Set (Vec ℝ n) × Set (Vec ℝ n))
  | 0, Rtk, Rτ => some (Rtk, Rτ)
  | k + 1, Rtk, Rτ =>
    -- 3. one step, lines 3-16
    (NonlinearSys.innerMinkDiffCorrectedStep ops zono f Δt μ fuel Rtk).bind fun st =>
      -- 17. the next step from `R̂(t_{k+1})`, `R̂(τ)` joined with `R̂(τ_k)`
      NonlinearSys.innerMinkDiffCorrectedLoop ops zono f Δt μ fuel k st.Rtk1 (Rτ ∪ st.Rtauk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
