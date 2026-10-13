module

public import CORALean.ContDynamics.NonlinearSys.Operations.ReachInnerMinkdiffLoop

@[expose] public section

/-!
# `reachInnerMinkdiff`, CORA's `'minkdiff'` inner reachability

CORA's `nonlinearSys/reachInner` with `options.algInner = 'minkdiff'`, which calls
`priv_reachInnerMinkdiff.m`, the implementation of [1, Alg. 1]: from `R0` at `tStart = 0`,
`steps` steps of size `timeStep` (`tVec = tStart:timeStep:tFinal`, `steps = length(tVec) - 1`,
passed as a number), each by `linReachInner`, the error guess starting at `zeros(n,1)` and the
input fixed at `params.u` (in `f`). The result is the pair of cell arrays `timePoint.set`
(index `k` the time `k Δt`) and `timeInt.set` (index `k` the interval `[k Δt, (k+1) Δt]`),
the cells past an empty step left empty; `none` when one step's error loop runs out of `fuel`.

CORALean's step differs from CORA's where CORA is unsound (see `NonlinearSys.linReachInner`):
the exact Minkowski difference, and the time-interval set `R̂(t_k) ∪ R̂(t_{k+1})` in place of
[1, Prop. 2]. The other options of `reachInner` are not this definition: `'parallelo'` and
`'proj'` are refuted in their CORA form, and `'scale'` is not formalized.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `priv_reachInnerMinkdiff` from `R0` for the field `f` under `params.u`, `steps`
steps of `timeStep`: the time-point and time-interval cells. -/
noncomputable def NonlinearSys.reachInnerMinkdiff (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (R0 : Set (Vec ℝ n)) (timeStep : ℝ) (steps fuel : ℕ) :
    Option ((ℕ → Set (Vec ℝ n)) × (ℕ → Set (Vec ℝ n))) :=
  let timePoint : ℕ → Set (Vec ℝ n) := Function.update (fun _ => ∅) 0 R0  -- timePoint.set{1}
  let timeInt : ℕ → Set (Vec ℝ n) := fun _ => ∅                    -- timeInt.set = cell(steps)
  let Rtp := R0                                                     -- Rtp.set = params.X₀
  let err : Vec ℝ n := 0                                            -- Rtp.error = zeros(n,1)
  NonlinearSys.reachInnerMinkdiffLoop ops f timeStep fuel steps 0 Rtp err timePoint timeInt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
